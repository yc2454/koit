import Koit.Lower.LIR
import Koit.Core.Interp

/-!
The dynamic semantics of LIR: the machine of Core, restricted to what
a structured language needs. The state is Core's, shared verbatim in
its maps, packet, layout token, kernel objects, held stack, and
trace; the frame binds each local to a value, an integer at its type
or a location; the kernel `K` is the same parameter and `KernelOk`
the same contract. Expressions are pure and partial functions of the
state, so they are functions here; the builtins and the kernel
functions are deterministic given `K`, so they are functions too,
and the statement, call, and program judgments are the relations the
lowering theorems are stated on. `LIRInterp.lean` is the executable
form of those relations, and the runner compares it with Core's.

The held stack is protocol state: `lock`, `enter`, `reserve`, and an
acquiring row push; `unlock`, `leave`, `submit`, `discard`, and a
releasing row pop and check. A release that does not match the
innermost entry, a call a held row forbids, and a program that ends
holding anything are errors, which is what makes a missing or
misplaced release a divergence the pass-B theorem sees.
-/

namespace Koit.LIR

open Koit (Span)
open Koit.Core (ArithOp CmpOp AtomicOp Kind Resource)
open Koit.Sem (State Val Loc Region Binding HeldRes Kernel Event CallOut M
  Abort toNatMod wrap slice zeros leBytes ofLe prim)
open Koit.Prelude (CallRow ResourceRow)

/-- How a statement ends. -/
inductive Outcome where
  | normal
  | br (n : Nat)
  | ret (v : Option Val)
  | raise (k : Kind) (reason : Nat)
  | err (msg : String)
  deriving Repr, Inhabited

/-! ### Values -/

/-- `fit(T, v)`: an integer reduced to `int(s,w)`, a location kept. -/
def fit (t : Ty) (v : Val) : Val :=
  match t, v with
  | .int s w, .int _ _ x _ => Val.mkInt s w x
  | _, v => v

/-- The `w`-bit pattern of a scalar. -/
def pattern (w : Nat) : Val → Option Nat
  | .int _ _ x _ => some (toNatMod x w)
  | .bool b => some (if b then 1 else 0)
  | .be _ x => some (toNatMod x w)
  | .loc _ => none

/-- A pattern read at a signedness and width. -/
def ofPattern (s : Bool) (w : Nat) (n : Nat) : Int := wrap s w n

/-- The location a type-agnostic place carries; LIR never reads it. -/
def anyTy : Core.Ty := .int Koit.Prelude.noSpan false 8

abbrev Res (α : Type) := Except String α

/-! ### Expressions -/

/-- A load or store of `n` bytes at `l` is admitted: the location's
token is current for the packet, and the bytes lie in the region. -/
def admitted (st : State) (l : Loc) (n : Nat) : Bool :=
  (l.region != .pkt || l.tok == st.layout) &&
    l.off + n ≤ (st.region l.region).size

mutual

/-- The value of an expression in a state. -/
partial def evalExpr (st : State) : Expr → Res Val
  | .lit w k => return .int false w k
  | .var x =>
    match st.local? x with
    | some (.val v) => return v
    | some (.place l) => return .loc l
    | _ => throw s!"`{x}` is unbound"
  | .arith op s w l r => do
    let some a := pattern w (← evalExpr st l) | throw "arithmetic on a location"
    let some b := pattern w (← evalExpr st r) | throw "arithmetic on a location"
    return Val.mkInt s w (Sem.arith op s w (ofPattern s w a) (ofPattern s w b))
  | .cast s w s' w' e => do
    let some a := pattern w (← evalExpr st e) | throw "a cast of a location"
    return Val.mkInt s' w' (ofPattern s w a)
  | .bswap w e => do
    let some a := pattern w (← evalExpr st e) | throw "a swap of a location"
    return Val.mkInt false w (Val.bswap w a)
  | .load s w a => do
    let l ← evalAddr st a
    unless admitted st l (w / 8) do
      throw s!"a load of {w} bits at {repr l.region} + {l.off} is not admitted"
    return Val.mkInt s w (ofLe (st.bytesAt l (w / 8)))
  | .ctx f =>
    match st.ctx.lookup f with
    | some v => return v
    | none => throw s!"the context has no field `{f}`"
  | .addr a => do return .loc (← evalAddr st a)

partial def evalAddr (st : State) : Addr → Res Loc
  | .var x =>
    match st.local? x with
    | some (.val (.loc l)) | some (.place l) => return l
    | _ => throw s!"`{x}` is not a location"
  | .plus a k => do
    let l ← evalAddr st a
    return { l with off := l.off + k }
  | .index a e k => do
    let l ← evalAddr st a
    let some i := pattern 64 (← evalExpr st e) | throw "an index that is a location"
    return { l with off := l.off + i * k }
  | .pktData => return { region := .pkt, off := 0, ty := anyTy, tok := st.layout }
  | .pktEnd =>
    return { region := .pkt, off := st.packet.size, ty := anyTy, tok := st.layout }
  | .mapval m k => return { region := .map m 0, off := k, ty := anyTy }

end

/-- A condition: two scalars at the width, two locations of one
region by offset, or a location against zero. -/
def evalCond (st : State) (c : Cond) : Res Bool := do
  let a ← evalExpr st c.l
  let b ← evalExpr st c.r
  match a, b with
  | .loc l, .loc l' =>
    unless l.region == l'.region do throw "locations of different regions compared"
    return Sem.compare c.op l.off l'.off
  | .loc _, v | v, .loc _ =>
    match c.op, pattern 64 v with
    | .eq, some 0 => return false
    | .ne, some 0 => return true
    | _, _ => throw "a location compared with a scalar other than zero"
  | a, b =>
    let some x := pattern c.w a | throw "a comparison of a location"
    let some y := pattern c.w b | throw "a comparison of a location"
    return Sem.compare c.op (ofPattern c.signed c.w x) (ofPattern c.signed c.w y)

/-! ### Builtins and kernel functions, in the machine's monad -/

def fail (msg : String) : M α := throw (.err msg)

def liftRes (r : Res α) : M α :=
  match r with
  | .ok v => pure v
  | .error m => fail m

def locOf (v : Val) (what : String) : M Loc :=
  match v with
  | .loc l => pure l
  | _ => fail s!"{what} takes a location"

/-- The bytes of a key or value argument, which must be initialized
and admitted. -/
def argBytes (st : State) (l : Loc) (n : Nat) : M (List UInt8) := do
  unless admitted st l n do fail "a key or value outside its region"
  return st.bytesAt l n

/-- The row of a resource, by its name. -/
def resourceRow (st : State) (r : Resource) : M ResourceRow :=
  match st.env.prelude.resource? r with
  | some row => pure row
  | none => fail s!"no row for `{r}`"

def sameObj (a b : Option Loc) : Bool :=
  match a, b with
  | some l, some l' => l.region == l'.region && l.off == l'.off
  | none, none => true
  | _, _ => false

/-- The innermost held entry popped, when it is the row's object. -/
def popHeld (r : Resource) (obj : Option Loc) : M HeldRes := do
  let st ← get
  match st.held with
  | h :: rest =>
    unless h.row.res == r && sameObj h.obj obj do
      fail s!"a release of {h.row.describe} that is not the innermost held"
    set { st with held := rest }
    return h
  | [] => fail "a release with nothing held"

/-- What a builtin does. The map operations have Core's semantics;
the protocol operations push and pop the held stack. -/
def execBuiltin (b : Builtin) (args : List Val) : M (Option Val) := do
  let st ← get
  match b, args with
  | .lookup m, [k] =>
    let some ms := st.maps.lookup m | fail s!"unknown map `{m}`"
    let kl ← locOf k "`lookup`"
    match ms.decl.kind with
    | .hash .. =>
      let kb ← argBytes st kl ms.keySize
      match ms.entries.find? (·.2.1 == kb) with
      | some (i, _, _) =>
        return some (.loc { region := .map m i, off := 0, ty := ms.valueTy })
      | none => return some (Val.mkInt false 64 0)
    | .ringbuf _ => fail "a ring buffer has no slots"
    | _ =>
      let idx := ofLe (← argBytes st kl 4)
      if idx < ms.capacity then
        return some (.loc { region := .map m idx, off := 0, ty := ms.valueTy })
      else return some (Val.mkInt false 64 0)
  | .update m, [k, v] =>
    let some ms := st.maps.lookup m | fail s!"unknown map `{m}`"
    let kb ← argBytes st (← locOf k "`update`") ms.keySize
    let vb ← argBytes st (← locOf v "`update`") ms.valueSize
    match ms.entries.find? (·.2.1 == kb) with
    | some (i, _, _) =>
      set (st.setRegion (.map m i) (ByteArray.mk vb.toArray))
      return some (Val.mkInt true 64 0)
    | none =>
      if ms.entries.length ≥ ms.capacity then return some (Val.mkInt true 64 (-7))
      let ms' := { ms with entries := ms.entries ++ [(ms.nextEntry, kb, ByteArray.mk vb.toArray)],
                           nextEntry := ms.nextEntry + 1 }
      set { st with maps := st.maps.map fun (n, x) => if n == m then (n, ms') else (n, x) }
      return some (Val.mkInt true 64 0)
  | .delete m, [k] =>
    let some ms := st.maps.lookup m | fail s!"unknown map `{m}`"
    let kb ← argBytes st (← locOf k "`delete`") ms.keySize
    if ms.entries.any (·.2.1 == kb) then
      let ms' := { ms with entries := ms.entries.filter (·.2.1 != kb) }
      set { st with maps := st.maps.map fun (n, x) => if n == m then (n, ms') else (n, x) }
      return some (Val.mkInt true 64 0)
    else return some (Val.mkInt true 64 (-2))
  | .reserve m n, [] =>
    let some ms := st.maps.lookup m | fail s!"unknown map `{m}`"
    let row ← resourceRow st ⟨"ringbuf"⟩
    if (ms.ring.foldl (fun a b => a + b.size) 0) + n > ms.capacity then
      return some (Val.mkInt false 64 0)
    let (id, st) := st.fresh
    let l : Loc := { region := .kernel id, off := 0, ty := anyTy }
    set { st.setRegion (.kernel id) (zeros n) with
            held := { row, name := none, map := some m, obj := some l } :: st.held }
    return some (.loc l)
  | .submit, [r] =>
    let l ← locOf r "`submit`"
    let h ← popHeld ⟨"ringbuf"⟩ (some l)
    let st ← get
    let rec_ := st.region l.region
    if let some m := h.map then
      set { st with maps := st.maps.map fun (p : String × Sem.MapState) =>
        if p.1 == m then (p.1, { p.2 with ring := p.2.ring ++ [rec_] }) else p }
    return none
  | .discard, [r] =>
    let _ ← popHeld ⟨"ringbuf"⟩ (some (← locOf r "`discard`"))
    return none
  | .lock, [a] =>
    let l ← locOf a "`lock`"
    let row ← resourceRow st ⟨"spinlock"⟩
    if st.held.any (·.row.res == ⟨"spinlock"⟩) then fail "a lock acquired while a lock is held"
    set { st with held := { row, name := none, obj := some l } :: st.held }
    return none
  | .unlock, [a] =>
    let _ ← popHeld ⟨"spinlock"⟩ (some (← locOf a "`unlock`"))
    return none
  | .enter r, [] =>
    let row ← resourceRow st r
    set { st with held := { row, name := none } :: st.held }
    return none
  | .leave r, [] =>
    let _ ← popHeld r none
    return none
  | .copy n, [d, s] =>
    let dl ← locOf d "`copy`"
    let sl ← locOf s "`copy`"
    unless admitted st sl n && admitted st dl n do fail "`copy` outside a region"
    set (st.writeAt dl (st.bytesAt sl n))
    return none
  | .fill n, [d, v] =>
    let dl ← locOf d "`fill`"
    let some b := pattern 8 v | fail "`fill` takes a byte"
    unless admitted st dl n do fail "`fill` outside a region"
    set (st.writeAt dl (List.replicate n (UInt8.ofNat b)))
    return none
  | .printk fmt, vs =>
    set (st.record (.print fmt vs))
    return none
  | .atomic op s w fetch, a :: vs =>
    let l ← locOf a "an atomic update"
    unless admitted st l (w / 8) do fail "an atomic update outside its region"
    let old : Int := ofPattern s w (ofLe (st.bytesAt l (w / 8)))
    match Sem.atomicResult op s w old vs with
    | some v => set (st.writeAt l (leBytes (toNatMod v w) (w / 8)))
    | none => pure ()
    return if fetch then some (Val.mkInt s w old) else none
  | b, _ => fail s!"`{b.print}` with the wrong arguments"

/-- The resource rows a kernel function releases: those whose exit
column names its kernel function. -/
def releasesOf (st : State) (row : CallRow) : List ResourceRow :=
  st.env.prelude.resources.filter fun r =>
    r.normalExit == row.kernel || r.abnormalExit == row.kernel

/-- The arguments of a kernel function fitted to its parameters: a
scalar reduced to its width, a memory parameter given a location. -/
def fitArgs (params : List Core.Param) (args : List Val) : M (List Val) := do
  let mut out : List Val := []
  for (p, v) in params.zip args do
    match ← Sem.norm p.ty, v with
    | .ref .., .loc _ | .view .., .loc _ | .own .., .loc _ => out := out ++ [v]
    | .ref .., _ | .view .., _ | .own .., _ =>
      fail s!"`{p.name}` takes a location"
    | t, .int .. => out := out ++ [← Sem.coerceTo t v]
    | _, _ => fail s!"`{p.name}` takes a scalar"
  return out

/-- What a kernel function does: the arguments fitted, the held rows
consulted, the kernel's answer as `r0` by the row's convention, the
trace appended, and the held stack pushed or popped per the row. -/
def execKernel (K : Kernel) (h : String) (args : List Val) : M Val := do
  let st ← get
  let some row := st.env.prelude.call? h | fail s!"unknown kernel function `{h}`"
  let params ← match row.sig with
    | .fn params _ => pure params
    | .builtin => fail s!"`{h}` is a builtin"
  unless args.length == params.length do fail s!"`{h}` takes {params.length} arguments"
  let vs ← fitArgs params args
  let releases := releasesOf st row
  for held in st.held do
    if Koit.Effects.Effs.forbids held.row.forbidden .call &&
        !releases.any (·.res == held.row.res) then
      fail s!"a call while {held.row.describe} is held"
  match K.helper row vs st with
  | .ok v st' =>
    let st' := st'.record (.call row.name vs (.ok v))
    set st'
    let r0 := match v with
      | some v => v
      | none => Val.mkInt true 64 0
    if let some r := row.acquires then
      if let .loc l := r0 then
        let rrow ← resourceRow st' r
        modify fun st => { st with held := { row := rrow, name := none, obj := some l } :: st.held }
    if let some rrow := releases.head? then
      let obj ← match vs.head? with
        | some (.loc l) => pure (some l)
        | _ => pure none
      let _ ← popHeld rrow.res obj
    return r0
  | .failed n st' =>
    set (st'.record (.call row.name vs (.failed n)))
    return match rowResult row with
      | .ptr => Val.mkInt false 64 0
      | _ => Val.mkInt true 64 n
  | .err m => fail m

/-- `frame x : n`: a fresh zeroed stack region. -/
def execFrame (x : String) (n : Nat) (src : Option Core.Ty) : M Unit := do
  let st ← get
  let (id, st) := st.fresh
  let l : Loc := { region := .stack id, off := 0, ty := src.getD anyTy }
  set ((st.setRegion (.stack id) (zeros n)).bind x (.val (.loc l)))

/-- `store(w) a e`. -/
def execStore (w : Nat) (a : Addr) (e : Expr) : M Unit := do
  let st ← get
  let l ← liftRes (evalAddr st a)
  let v ← liftRes (evalExpr st e)
  let some p := pattern w v | fail "a location is never stored"
  unless admitted st l (w / 8) do
    fail s!"a store of {w} bits at {repr l.region} + {l.off} is not admitted"
  set (st.writeAt l (leBytes p (w / 8)))

/-- `let x : T = e`. -/
def execLet (x : String) (t : Ty) (e : Expr) : M Unit := do
  let st ← get
  let v ← liftRes (evalExpr st e)
  set (st.bind x (.val (fit t v)))

/-- `x := e`, at the type of the value `x` holds. -/
def execAssign (x : String) (e : Expr) : M Unit := do
  let st ← get
  let v ← liftRes (evalExpr st e)
  match st.local? x with
  | some (.val (.int s w _ _)) => set (st.rebind x (.val (fit (.int s w) v)))
  | some (.val _) => set (st.rebind x (.val v))
  | _ => fail s!"`{x}` is unbound"

/-- The arguments of a call to a function of the unit, fitted to its
parameters. -/
def callFrame (d : Fn) (args : List Val) : M (List (String × Binding)) := do
  unless args.length == d.params.length do
    fail s!"`{d.name}` takes {d.params.length} arguments"
  return (d.params.zip args).map fun (p, v) => (p.name, .val (fit p.ty v))

/-! ### The judgments -/

/-- The arguments of a call, evaluated left to right. -/
inductive EvalArgs : State → List Expr → Res (List Val) → Prop
  | nil {st} : EvalArgs st [] (.ok [])
  | cons {st e rest v vs} :
      evalExpr st e = .ok v → EvalArgs st rest (.ok vs) →
      EvalArgs st (e :: rest) (.ok (v :: vs))
  | err {st e rest m} :
      evalExpr st e = .error m → EvalArgs st (e :: rest) (.error m)
  | errRest {st e rest v m} :
      evalExpr st e = .ok v → EvalArgs st rest (.error m) →
      EvalArgs st (e :: rest) (.error m)

/-- The arguments a statement evaluates before it acts, for the error
rule. -/
def stmtArgs : Stmt → Option (List Expr)
  | .call _ _ _ args .. | .builtin _ _ _ args | .kernel _ _ _ args => some args
  | _ => none


/-- The functions of the unit, which the call rule looks up. -/
abbrev Fns := List Fn

def Outcome.isNormal : Outcome → Bool
  | .normal => true
  | _ => false

mutual

/-- `K ⊢ ⟨s, st⟩ ⇓ o, st'`. -/
inductive ExecStmt (K : Kernel) (fns : Fns) : State → Stmt → Outcome → State → Prop
  | «let» {st sp x t e st'} :
      prim (execLet x t e) st = .ok ((), st') →
      ExecStmt K fns st (.«let» sp x t e) .normal st'
  | letErr {st sp x t e m st'} :
      prim (execLet x t e) st = .error (.err m) →
      ExecStmt K fns st (.«let» sp x t e) (.err m) st'
  | assign {st sp x e st'} :
      prim (execAssign x e) st = .ok ((), st') →
      ExecStmt K fns st (.assign sp x e) .normal st'
  | assignErr {st sp x e m} :
      prim (execAssign x e) st = .error (.err m) →
      ExecStmt K fns st (.assign sp x e) (.err m) st
  /-- (Store) and (Store-err). -/
  | store {st sp w a e st'} :
      prim (execStore w a e) st = .ok ((), st') →
      ExecStmt K fns st (.store sp w a e) .normal st'
  | storeErr {st sp w a e m} :
      prim (execStore w a e) st = .error (.err m) →
      ExecStmt K fns st (.store sp w a e) (.err m) st
  | ctxStore {st sp f e v} :
      evalExpr st e = .ok v → (st.ctx.lookup f).isSome →
      ExecStmt K fns st (.ctxStore sp f e) .normal
        { st with ctx := st.ctx.map fun (g, w) => if g == f then (g, v) else (g, w) }
  /-- (Frame): a fresh zeroed region. -/
  | frame {st sp x n src st'} :
      prim (execFrame x n src) st = .ok ((), st') →
      ExecStmt K fns st (.frame sp x n src) .normal st'
  /-- (If). -/
  | iteT {st sp c t e o st'} :
      evalCond st c = .ok true → ExecStmts K fns st t o st' →
      ExecStmt K fns st (.ite sp c t e) o st'
  | iteF {st sp c t e o st'} :
      evalCond st c = .ok false → ExecStmts K fns st e o st' →
      ExecStmt K fns st (.ite sp c t e) o st'
  | iteErr {st sp c t e m} :
      evalCond st c = .error m → ExecStmt K fns st (.ite sp c t e) (.err m) st
  /-- (Block): a `br 0` is consumed, a deeper one decremented. -/
  | blockDone {st sp body o st'} :
      ExecStmts K fns st body o st' → (o = .normal ∨ o = .br 0) →
      ExecStmt K fns st (.block sp body) .normal st'
  | blockBr {st sp body n st'} :
      ExecStmts K fns st body (.br (n + 1)) st' →
      ExecStmt K fns st (.block sp body) (.br n) st'
  | blockExit {st sp body o st'} :
      ExecStmts K fns st body o st' → (o matches .ret _ | .raise .. | .err _) →
      ExecStmt K fns st (.block sp body) o st'
  /-- (Loop): a normal completion or a `br 0` restarts it. -/
  | loopNext {st sp body o st1 o' st2} :
      ExecStmts K fns st body o st1 → (o = .normal ∨ o = .br 0) →
      ExecStmt K fns st1 (.loop sp body) o' st2 →
      ExecStmt K fns st (.loop sp body) o' st2
  | loopBr {st sp body n st'} :
      ExecStmts K fns st body (.br (n + 1)) st' →
      ExecStmt K fns st (.loop sp body) (.br n) st'
  | loopExit {st sp body o st'} :
      ExecStmts K fns st body o st' → (o matches .ret _ | .raise .. | .err _) →
      ExecStmt K fns st (.loop sp body) o st'
  | br {st sp n} : ExecStmt K fns st (.br sp n) (.br n) st
  | retVal {st sp e v} :
      evalExpr st e = .ok v → ExecStmt K fns st (.ret sp (some e)) (.ret (some v)) st
  | retErr {st sp e m} :
      evalExpr st e = .error m → ExecStmt K fns st (.ret sp (some e)) (.err m) st
  | retNone {st sp} : ExecStmt K fns st (.ret sp none) (.ret none) st
  /-- (Raise): the reason is a `u32`. -/
  | raise {st sp k e v} :
      evalExpr st e = .ok v →
      ExecStmt K fns st (.raise sp k e) (.raise k ((pattern 32 v).getD 0)) st
  | raiseErr {st sp k e m} :
      evalExpr st e = .error m → ExecStmt K fns st (.raise sp k e) (.err m) st
  /-- (Call): the callee's body in a fresh frame, its `return` the
  result, the held stack unchanged across the call; absence runs
  `absent`, a failure runs `unwind` and continues outward. -/
  | callRet {st sp x f args u a d vs frame o st1 st2 v} :
      fns.find? (·.name == f) = some d → EvalArgs st args (.ok vs) →
      prim (callFrame d vs) st = .ok (frame, st) →
      ExecStmts K fns { st with locals := frame } d.body o st1 →
      st1.held = st.held →
      (o = .ret (some v) ∨ (o = .normal ∧ x = none ∧ v = Val.mkInt true 64 0)) →
      st2 = { st1 with locals := st.locals } →
      ExecStmt K fns st (.call sp x f args u a) .normal
        (match x with
         | some x => st2.bind x (.val v)
         | none => st2)
  | callAbsent {st sp x f args u a d vs frame st1 o st2} :
      fns.find? (·.name == f) = some d → EvalArgs st args (.ok vs) →
      prim (callFrame d vs) st = .ok (frame, st) →
      ExecStmts K fns { st with locals := frame } d.body (.ret none) st1 →
      st1.held = st.held →
      ExecStmts K fns { st1 with locals := st.locals } (a.getD []) o st2 →
      ExecStmt K fns st (.call sp x f args (u) (a)) o st2
  | callRaise {st sp x f args u a d vs frame k r st1 st2} :
      fns.find? (·.name == f) = some d → EvalArgs st args (.ok vs) →
      prim (callFrame d vs) st = .ok (frame, st) →
      ExecStmts K fns { st with locals := frame } d.body (.raise k r) st1 →
      ExecStmts K fns { st1 with locals := st.locals } (u.getD []) .normal st2 →
      ExecStmt K fns st (.call sp x f args u a) (.raise k r) st2
  | callErr {st sp x f args u a d vs frame m st1} :
      fns.find? (·.name == f) = some d → EvalArgs st args (.ok vs) →
      prim (callFrame d vs) st = .ok (frame, st) →
      ExecStmts K fns { st with locals := frame } d.body (.err m) st1 →
      ExecStmt K fns st (.call sp x f args u a) (.err m) st1
  /-- A builtin. -/
  | builtin {st sp x b args vs v st'} :
      EvalArgs st args (.ok vs) → prim (execBuiltin b vs) st = .ok (v, st') →
      ExecStmt K fns st (.builtin sp x b args) .normal
        (match x, v with
         | some x, some v => st'.bind x (.val v)
         | _, _ => st')
  | builtinErr {st sp x b args vs m} :
      EvalArgs st args (.ok vs) → prim (execBuiltin b vs) st = .error (.err m) →
      ExecStmt K fns st (.builtin sp x b args) (.err m) st
  /-- (Kernel): the row's kernel function through `K`. -/
  | kernel {st sp x h args vs v st'} :
      EvalArgs st args (.ok vs) → prim (execKernel K h vs) st = .ok (v, st') →
      ExecStmt K fns st (.kernel sp x h args) .normal
        (match x with
         | some x => st'.bind x (.val v)
         | none => st')
  | kernelErr {st sp x h args vs m} :
      EvalArgs st args (.ok vs) → prim (execKernel K h vs) st = .error (.err m) →
      ExecStmt K fns st (.kernel sp x h args) (.err m) st
  | argsErr {st s m} :
      (∃ args, stmtArgs s = some args ∧ EvalArgs st args (.error m)) →
      ExecStmt K fns st s (.err m) st

/-- (Seq). -/
inductive ExecStmts (K : Kernel) (fns : Fns) : State → List Stmt → Outcome → State → Prop
  | nil {st} : ExecStmts K fns st [] .normal st
  | consNormal {st s rest o st1 st2} :
      ExecStmt K fns st s .normal st1 → ExecStmts K fns st1 rest o st2 →
      ExecStmts K fns st (s :: rest) o st2
  | consExit {st s rest o st1} :
      ExecStmt K fns st s o st1 → ¬ o.isNormal →
      ExecStmts K fns st (s :: rest) o st1

end

/-- (Program): the body's `return` halts; a failure runs the handler
of its kind with `reason` bound and nothing held; a `syscall` body
may fall off its end; anything else, including a held stack that is
not empty at the exit, is an error. -/
inductive ExecProgram (K : Kernel) (fns : Fns) : State → Program → Sem.ProgOut → State → Prop
  | ret {st p v v' st1} :
      ExecStmts K fns st p.body (.ret (some v)) st1 → st1.held = [] →
      prim (Sem.coerceTo st.kind.verdictTy v) st1 = .ok (v', st1) →
      ExecProgram K fns st p (.halt v') st1
  | fallOff {st p st1} :
      ExecStmts K fns st p.body .normal st1 → st.kind.hasPkt = false → st1.held = [] →
      ExecProgram K fns st p (.halt (Val.mkInt true 32 0)) st1
  | handled {st p k reason h v v' st1 st2} :
      ExecStmts K fns st p.body (.raise k reason) st1 → st1.held = [] →
      p.handlers.find? (·.kind == k) = some h →
      ExecStmts K fns { st1 with locals := [("reason", .val (Val.u32 reason))] }
        h.body (.ret (some v)) st2 →
      prim (Sem.coerceTo st.kind.verdictTy v) st2 = .ok (v', st2) →
      ExecProgram K fns st p (.halt v') st2
  | bodyErr {st p m st1} :
      ExecStmts K fns st p.body (.err m) st1 → ExecProgram K fns st p (.err m) st1
  | heldAtExit {st p o st1} :
      ExecStmts K fns st p.body o st1 → (o matches .ret _ | .raise .. | .normal) →
      st1.held ≠ [] →
      ExecProgram K fns st p (.err "the program exits holding a resource") st1
  | stuck {st p o st1} :
      ExecStmts K fns st p.body o st1 → (o matches .br _ | .ret none) →
      ExecProgram K fns st p (.err "the body ends outside a loop or without a verdict") st1
  | fallOffPacket {st p st1} :
      ExecStmts K fns st p.body .normal st1 → st.kind.hasPkt = true →
      ExecProgram K fns st p (.err "the body fell off its end") st1
  | handlerErr {st p k reason h o st1 st2} :
      ExecStmts K fns st p.body (.raise k reason) st1 → st1.held = [] →
      p.handlers.find? (·.kind == k) = some h →
      ExecStmts K fns { st1 with locals := [("reason", .val (Val.u32 reason))] }
        h.body o st2 → (∀ v, o ≠ .ret (some v)) →
      ExecProgram K fns st p (.err "the handler does not return a verdict") st2

end Koit.LIR
