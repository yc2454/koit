import Koit.LIR.State

/-!
The dynamic semantics of LIR over the state of `State.lean`, whose
shared half is the machine's: maps, packet, layout token, kernel
objects, held stack, and trace are the same objects Core's run acts
on, reached through the same operations of `Koit.Machine.Ops`; the
frame binds each local to a value, an integer at its type or a
location; the kernel `K` is the same parameter and `KernelOk` the
same contract. Expressions are pure and partial functions of the
state, so they are functions here; the builtins and the kernel
functions are deterministic given `K`, so they are functions too,
and the statement, call, and program judgments are the relations the
lowering theorems are stated on. `Interp.lean` is the executable
form of those relations, and the runner compares it with Core's.

The held stack is protocol state: `lock`, `enter`, `reserve`, and an
acquiring row push; `unlock`, `leave`, `submit`, `discard`, and a
releasing row pop and check. A release that does not match the
innermost entry, a call a held row forbids, and a program that ends
holding anything are errors, which is what makes a missing or
misplaced release a divergence the pass-B theorem sees.
-/

namespace Koit.LIR.Sem

open Koit (Span)
open Koit.Core (ArithOp CmpOp AtomicOp Kind Resource)
open Koit.Core.Sem (Val Loc Region Abort)
open Koit.Machine (Kernel toNatMod wrap zeros leBytes ofLe bswap HeldObj)
open Koit.Interface (CallRow ResourceRow)

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

/-- The type a type-agnostic location carries; LIR never reads it. -/
def anyTy : Core.Ty := .int Koit.Interface.noSpan false 8

/-- A value at a Core type of the kind, for the verdict and the
scalar parameters of kernel functions. -/
partial def fitCore (t : Core.Ty) (v : Val) : Val :=
  match t, v with
  | .int _ s w, .int _ _ x _ => Val.mkInt s w x
  | .int _ s w, .bool b => Val.mkInt s w (if b then 1 else 0)
  | .refined _ _ base _, v => fitCore base v
  | _, v => v

abbrev Res (α : Type) := Except String α

/-! ### Expressions -/

mutual

/-- The value of an expression in a state. -/
partial def evalExpr (st : State) : Expr → Res Val
  | .lit w k => return .int false w k
  | .var x =>
    match st.local? x with
    | some v => return v
    | none => throw s!"`{x}` is unbound"
  | .arith op s w l r => do
    let some a := pattern w (← evalExpr st l) | throw "arithmetic on a location"
    let some b := pattern w (← evalExpr st r) | throw "arithmetic on a location"
    return Val.mkInt s w (Machine.arith op s w (ofPattern s w a) (ofPattern s w b))
  | .cast s w s' w' e => do
    let some a := pattern w (← evalExpr st e) | throw "a cast of a location"
    return Val.mkInt s' w' (ofPattern s w a)
  | .bswap w e => do
    let some a := pattern w (← evalExpr st e) | throw "a swap of a location"
    return Val.mkInt false w (bswap w a)
  | .load s w a => do
    let l ← evalAddr st a
    unless st.admits l (w / 8) do
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
    | some (.loc l) => return l
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
    return Machine.compare c.op l.off l'.off
  | .loc _, v | v, .loc _ =>
    match c.op, pattern 64 v with
    | .eq, some 0 => return false
    | .ne, some 0 => return true
    | _, _ => throw "a location compared with a scalar other than zero"
  | a, b =>
    let some x := pattern c.w a | throw "a comparison of a location"
    let some y := pattern c.w b | throw "a comparison of a location"
    return Machine.compare c.op (ofPattern c.signed c.w x) (ofPattern c.signed c.w y)

/-! ### Builtins and kernel functions, in the evaluation monad -/

def liftRes (r : Res α) : M α :=
  match r with
  | .ok v => pure v
  | .error m => fail m

def locOf (v : Val) (what : String) : M Loc :=
  match v with
  | .loc l => pure l
  | _ => fail s!"{what} takes a location"

/-- The object a location names on the held stack. -/
def heldObjOf (l : Loc) (what : String) : M HeldObj :=
  match l.heldObj with
  | some obj => pure obj
  | none => fail s!"{what} takes a place in a map value or a kernel object"

/-- The bytes of a key or value argument, which must be initialized
and admitted. -/
def argBytes (l : Loc) (n : Nat) : M (List UInt8) := do
  let st ← get
  unless st.admits l n do fail "a key or value outside its region"
  return st.bytesAt l n

def norm (t : Core.Ty) : M Core.Ty := do
  match (← get).env.norm t with
  | .ok t => pure t
  | .error d => fail s!"{d}"

def sizeOf (t : Core.Ty) : M Nat := do
  match (← get).env.layout t with
  | .ok (n, _) => pure n
  | .error d => fail s!"{d}"

/-- The row of a resource, by its name. -/
def resourceRow (r : Resource) : M ResourceRow := do
  match (← get).env.interface.resource? r with
  | some row => pure row
  | none => fail s!"no row for `{r}`"

/-- What a builtin does, through the machine: the map operations have
the kernel's answers, the protocol operations push and pop the held
stack, the byte moves and the atomics act on the bytes. -/
def execBuiltin (b : Builtin) (args : List Val) : M (Option Val) := do
  let st ← get
  match b, args with
  | .lookup m, [k] =>
    let some ms := st.maps.lookup m | fail s!"unknown map `{m}`"
    let kl ← locOf k "`lookup`"
    let keySize := match ms.decl.kind with
      | .hash .. => ms.keySize
      | _ => 4
    match ← op (Machine.lookup m (← argBytes kl keySize)) with
    | some r => return some (.loc { region := .shared r, off := 0, ty := ms.valueTy })
    | none => return some (Val.mkInt false 64 0)
  | .update m, [k, v] =>
    let some ms := st.maps.lookup m | fail s!"unknown map `{m}`"
    let kb ← argBytes (← locOf k "`update`") ms.keySize
    let vb ← argBytes (← locOf v "`update`") ms.valueSize
    return some (Val.mkInt true 64 (← op (Machine.update m kb vb)))
  | .delete m, [k] =>
    let some ms := st.maps.lookup m | fail s!"unknown map `{m}`"
    let kb ← argBytes (← locOf k "`delete`") ms.keySize
    return some (Val.mkInt true 64 (← op (Machine.delete m kb)))
  | .reserve m n, [] =>
    let row ← resourceRow ⟨"ringbuf"⟩
    match ← op (Machine.reserve row m n) with
    | some id => return some (.loc { region := .kernel id, off := 0, ty := anyTy })
    | none => return some (Val.mkInt false 64 0)
  | .submit, [r] =>
    op (Machine.submit (← heldObjOf (← locOf r "`submit`") "`submit`"))
    return none
  | .discard, [r] =>
    op (Machine.discard (← heldObjOf (← locOf r "`discard`") "`discard`"))
    return none
  | .lock, [a] =>
    let row ← resourceRow ⟨"spinlock"⟩
    op (Machine.lock row (← heldObjOf (← locOf a "`lock`") "`lock`"))
    return none
  | .unlock, [a] =>
    op (Machine.unlock (← heldObjOf (← locOf a "`unlock`") "`unlock`"))
    return none
  | .enter r, [] =>
    op (Machine.enter (← resourceRow r))
    return none
  | .leave r, [] =>
    op (Machine.leave r)
    return none
  | .copy n, [d, s] =>
    let dl ← locOf d "`copy`"
    let sl ← locOf s "`copy`"
    unless st.admits sl n && st.admits dl n do fail "`copy` outside a region"
    set (st.writeAt dl (st.bytesAt sl n))
    return none
  | .fill n, [d, v] =>
    let dl ← locOf d "`fill`"
    let some b := pattern 8 v | fail "`fill` takes a byte"
    unless st.admits dl n do fail "`fill` outside a region"
    set (st.writeAt dl (List.replicate n (UInt8.ofNat b)))
    return none
  | .printk fmt, vs =>
    op (Machine.print fmt (vs.map Val.observe))
    return none
  | .atomic o s w fetch, a :: vs =>
    let l ← locOf a "an atomic update"
    unless st.admits l (w / 8) do fail "an atomic update outside its region"
    let old : Int := ofPattern s w (ofLe (st.bytesAt l (w / 8)))
    match Machine.atomic o s w old (vs.map fun v => (v.toInt?).getD 0) with
    | some v => set (st.writeAt l (leBytes (toNatMod v w) (w / 8)))
    | none => pure ()
    return if fetch then some (Val.mkInt s w old) else none
  | b, _ => fail s!"`{b.print}` with the wrong arguments"

/-- The arguments of a kernel function as the kernel sees them: a
scalar reduced to its parameter's type, a `ref` or `view` place as
its bytes, an owned reference as its object. -/
def fitArgs (params : List Core.Param) (args : List Val) : M (List Machine.Val) := do
  let mut out : List Machine.Val := []
  for (p, v) in params.zip args do
    match ← norm p.ty, v with
    | .own .., .loc l =>
      match l.region with
      | .shared (.kernel id) => out := out ++ [.object id]
      | _ => fail s!"`{p.name}` takes an owned reference"
    | .ref _ t, .loc l | .view _ t, .loc l =>
      out := out ++ [.bytes (← argBytes l (← sizeOf t))]
    | .ref .., _ | .view .., _ | .own .., _ =>
      fail s!"`{p.name}` takes a location"
    | t, .int .. => out := out ++ [(fitCore t v).observe]
    | _, _ => fail s!"`{p.name}` takes a scalar"
  return out

/-- What a kernel function does: the arguments fitted, the call
through the machine, which consults the held rows, appends the trace
event, and pushes or pops the held stack per the row, and the answer
as `r0` by the row's convention: a location for an owned or
referenced result, the 64-bit signed return otherwise, which carries
the failure signal of a scalar-result row. -/
def execKernel (K : Kernel) (h : String) (args : List Val) : M Val := do
  let st ← get
  let some row := st.env.interface.call? h | fail s!"unknown kernel function `{h}`"
  let params ← match row.sig with
    | .fn params _ => pure params
    | .builtin => fail s!"`{h}` is a builtin"
  unless args.length == params.length do fail s!"`{h}` takes {params.length} arguments"
  let vs ← fitArgs params args
  match ← op (Machine.call st.env.interface K st.kind row vs) with
  | .ok v =>
    match v with
    | some (.scalar x) => return Val.mkInt true 64 x
    | some (.object id) => return .loc { region := .kernel id, off := 0, ty := anyTy }
    | some (.bytes _) => fail s!"`{h}` answers with bytes"
    | none => return Val.mkInt true 64 0
  | .failed n =>
    return match rowResult row with
      | .ptr => Val.mkInt false 64 0
      | _ => Val.mkInt true 64 n

/-- `frame x : n`: a fresh zeroed stack region. -/
def execFrame (x : String) (n : Nat) (src : Option Core.Ty) : M Unit := do
  let st ← get
  let (id, st) := st.freshStack
  let l : Loc := { region := .stack id, off := 0, ty := src.getD anyTy }
  set ((st.setRegion (.stack id) (zeros n)).bind x (.loc l))

/-- `store(w) a e`. -/
def execStore (w : Nat) (a : Addr) (e : Expr) : M Unit := do
  let st ← get
  let l ← liftRes (evalAddr st a)
  let v ← liftRes (evalExpr st e)
  let some p := pattern w v | fail "a location is never stored"
  unless st.admits l (w / 8) do
    fail s!"a store of {w} bits at {repr l.region} + {l.off} is not admitted"
  set (st.writeAt l (leBytes p (w / 8)))

/-- `let x : T = e`. -/
def execLet (x : String) (t : Ty) (e : Expr) : M Unit := do
  let st ← get
  let v ← liftRes (evalExpr st e)
  set (st.bind x (fit t v))

/-- `x := e`, at the type of the value `x` holds. -/
def execAssign (x : String) (e : Expr) : M Unit := do
  let st ← get
  let v ← liftRes (evalExpr st e)
  match st.local? x with
  | some (.int s w _ _) => set (st.rebind x (fit (.int s w) v))
  | some _ => set (st.rebind x v)
  | none => fail s!"`{x}` is unbound"

/-- The arguments of a call to a function of the unit, fitted to its
parameters. -/
def callFrame (d : Fn) (args : List Val) : M (List (String × Val)) := do
  unless args.length == d.params.length do
    fail s!"`{d.name}` takes {d.params.length} arguments"
  return (d.params.zip args).map fun (p, v) => (p.name, fit p.ty v)

/-! ### The judgments -/

/-- A primitive applied in a state. -/
def prim (f : M α) (st : State) : Except Abort (α × State) := f.exec st

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
         | some x => st2.bind x v
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
         | some x, some v => st'.bind x v
         | _, _ => st')
  | builtinErr {st sp x b args vs m} :
      EvalArgs st args (.ok vs) → prim (execBuiltin b vs) st = .error (.err m) →
      ExecStmt K fns st (.builtin sp x b args) (.err m) st
  /-- (Kernel): the row's kernel function through `K`. -/
  | kernel {st sp x h args vs v st'} :
      EvalArgs st args (.ok vs) → prim (execKernel K h vs) st = .ok (v, st') →
      ExecStmt K fns st (.kernel sp x h args) .normal
        (match x with
         | some x => st'.bind x v
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

/-- How a program's run ends. -/
inductive ProgOut where
  | halt (v : Val)
  | err (msg : String)
  deriving Repr, Inhabited

/-- (Program): the body's `return` halts; a failure runs the handler
of its kind with `reason` bound and nothing held; a `syscall` body
may fall off its end; anything else, including a held stack that is
not empty at the exit, is an error. -/
inductive ExecProgram (K : Kernel) (fns : Fns) : State → Program → ProgOut → State → Prop
  | ret {st p v st1} :
      ExecStmts K fns st p.body (.ret (some v)) st1 → st1.held = [] →
      ExecProgram K fns st p (.halt (fitCore st.kind.verdictTy v)) st1
  | fallOff {st p st1} :
      ExecStmts K fns st p.body .normal st1 → st.kind.hasPkt = false → st1.held = [] →
      ExecProgram K fns st p (.halt (Val.mkInt true 32 0)) st1
  | handled {st p k reason h v st1 st2} :
      ExecStmts K fns st p.body (.raise k reason) st1 → st1.held = [] →
      p.handlers.find? (·.kind == k) = some h →
      ExecStmts K fns { st1 with locals := [("reason", Val.u32 reason)] }
        h.body (.ret (some v)) st2 →
      ExecProgram K fns st p (.halt (fitCore st.kind.verdictTy v)) st2
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
      ExecStmts K fns { st1 with locals := [("reason", Val.u32 reason)] }
        h.body o st2 → (∀ v, o ≠ .ret (some v)) →
      ExecProgram K fns st p (.err "the handler does not return a verdict") st2

end Koit.LIR.Sem
