import Koit.Core.Semantics

/-!
The evaluator: a fuel-bounded run of a Core program over a synthetic
packet, zero-filled maps, and a kernel model, the executable form of
the relation in `Semantics.lean`. Statements are executed
structurally, so the continuation frames of the definition are the
recursion: a `break`, `continue`, or `return` is an outcome that the
enclosing loop or call consumes, and a failure or an error is an
abort that every enclosing `hold` releases on its way out, up to the
program's handler for the failure's kind.

`koitc run` uses `runUnit` on a unit the checker has accepted; a
program the checker rejects has no defined run, and the errors here
are the cases the safety theorem makes unreachable.
-/

namespace Koit.Core.Sem

open Koit (Span)
open Koit.Core
open Koit.Check (Env)
open Koit.Interface (KindDecl CallDecl ResourceDecl AcqArg Sig)
open Koit.Machine (Kernel toNatMod wrap zeros arith compare bswap hexOf)

mutual

/-- The value of an expression. -/
partial def evalExpr (K : Kernel) : Expr → M Val
  | .lit _ v _ => return Val.lit v
  | .char _ c => return Val.mkInt false 8 c.toNat
  | .bool _ b => return .bool b
  | .str _ _ => fail "a string appears only as the format of `printk`"
  | .var s x => do
    let st ← get
    match st.local? x with
    | some (.val v) => return v
    | some (.place l) => return .loc l
    | some .moved => fail s!"`{x}` is used after `move`"
    | none =>
      let env := st.env
      if let some d := env.consts.find? (·.name == x) then evalConst K d
      else if let some d := env.config? x then
        match d.init with
        | some e => coerceTo d.ty (← evalExpr K e)
        | none => fail s!"`{x}` has no value for this build"
      else if let some n := st.kind.verdicts.lookup x then return Val.u32 n
      else if let some d := env.interface.const? x then evalConst K d
      else
        let _ := s
        fail s!"unknown name `{x}`"
  | .arith _ op l r => do
    let a ← evalExpr K l
    let b ← evalExpr K r
    match meetInts a b with
    | some (s, w, x, y, poly) => return .int s w (arith op s w x y) poly
    | none => fail s!"`{op.spelling}` on {a.print} and {b.print}"
  | .cmp _ op l r => do
    let a ← evalExpr K l
    let b ← evalExpr K r
    match a, b with
    | .be w x, .be w' y =>
      match meetBe w x w' y with
      | some (x', y') => return .bool (compare op x' y')
      | none => fail s!"`{op.spelling}` on {a.print} and {b.print}"
    | .be w _, .int _ _ y true | .int _ _ y true, .be w _ =>
      -- a byte-order value against an untyped integer, which is
      -- `hton` of itself at the value's width
      let w := if w == 0 then 64 else w
      match fitBe w (.int false 64 y true), fitBe w a with
      | .be _ y', .be _ x' => return .bool (compare op x' y')
      | _, _ => fail s!"`{op.spelling}` on {a.print} and {b.print}"
    | _, _ =>
      match meetInts a b with
      | some (_, _, x, y, _) => return .bool (compare op x y)
      | none =>
        match a, b with
        | .bool x, .bool y => return .bool (compare op (if x then 1 else 0) (if y then 1 else 0))
        | _, _ => fail s!"`{op.spelling}` on {a.print} and {b.print}"
  | .not _ e => do return .bool (!(← evalExpr K e).truthy)
  | .and _ l r => do
    if (← evalExpr K l).truthy then return .bool (← evalExpr K r).truthy
    else return .bool false
  | .or _ l r => do
    if (← evalExpr K l).truthy then return .bool true
    else return .bool (← evalExpr K r).truthy
  | .cast _ e t => do
    let v ← evalExpr K e
    match ← norm t, v with
    | .int _ s w, .int _ _ x _ => return Val.mkInt s w x
    | .int _ s w, .bool b => return Val.mkInt s w (if b then 1 else 0)
    | _, _ => fail s!"a cast of {v.print} to `{t.print}`"
  | .hton _ e => do
    match ← evalExpr K e with
    | .int _ w x poly =>
      if poly then return .be 0 (toNatMod x 64)
      else return .be w (bswap w (toNatMod x w))
    | v => fail s!"`hton` of {v.print}"
  | .ntoh _ e => do
    match ← evalExpr K e with
    | .be 0 x => return Val.mkInt false 64 x
    | .be w x => return Val.mkInt false w (bswap w x)
    | v => fail s!"`ntoh` of {v.print}"
  | .read _ p => do loadPlace (← evalPlace K p)
  | .size _ t => do return Val.lit (← sizeOf t)
  | .move _ x => do
    let st ← get
    match st.local? x with
    | some (.place l) =>
      -- the name is dead, so the scope releases nothing; the sink's
      -- declaration pops the held entry when it runs
      set (st.rebind x .moved)
      return .loc l
    | _ => fail s!"`move {x}` of a name that is not owned"
  | .call s f args => do
    match ← callAny K s f args with
    | some v => return v
    | none => fail s!"`{f}` yields no value"
  | .errno _ => do return Val.mkInt false 32 (← get).errno
  | .invalid _ m => fail m

/-- A constant's value, at its declared type or `poly`. -/
partial def evalConst (K : Kernel) (d : ConstDecl) : M Val := do
  let v ← evalExpr K d.value
  match d.ty with
  | some t => coerceTo t v
  | none => return v

/-- The place an expression of place form denotes. -/
partial def evalPlace (K : Kernel) : Place → M PlaceRef
  | .var _ x => do
    let st ← get
    match st.local? x with
    | some (.val _) => return .local x
    | some (.place l) =>
      -- a view outlives its token only in a program the checker
      -- rejects
      if l.region == .pkt && l.tok != st.layout then
        fail s!"view `{x}` is used after a resize"
      return .mem l
    | some .moved => fail s!"`{x}` is used after `move`"
    | none => fail s!"`{x}` is not a place"
  | .field s p f => do
    match p with
    | .var _ "ctx" => return .ctx f
    | _ =>
      match ← evalPlace K p with
      | .mem l =>
        let (o, ft) ← fieldOf l.ty f
        return .mem { l with off := l.off + o, ty := ft }
      | _ =>
        let _ := s
        fail s!"`{p.print}` has no fields"
  | .index _ p i => do
    let r ← evalPlace K p
    let iv ← evalExpr K i
    match r with
    | .mem l =>
      match ← norm l.ty with
      | .array _ elem n =>
        let len ← constNat n
        let some idx := iv.toInt? | fail "an index must be an integer"
        if idx < 0 || idx ≥ len then
          fail s!"index {idx} out of the bounds of `{l.ty.print}`"
        let esz ← sizeOf elem
        return .mem { l with off := l.off + esz * idx.toNat, ty := elem }
      | _ => fail s!"`{p.print}` is not an array"
    | _ => fail s!"`{p.print}` is not an array"
  | .slot _ m i => do
    let iv ← evalExpr K i
    let st ← get
    match st.maps.lookup m with
    | some ms =>
      let some idx := iv.toInt? | fail "an index must be an integer"
      if idx < 0 || idx ≥ ms.capacity then
        fail s!"index {idx} out of the bounds of `{m}`"
      return .mem { region := .map m idx.toNat, off := 0, ty := ms.valueTy }
    | none => fail s!"unknown map `{m}`"
  | .deref s e => do
    match e with
    | .var _ x => evalPlace K (.var s x)
    | _ => fail "`*` applies to a reference or view"
  | .invalid _ m => fail m

/-- The arguments of a call: values for scalars, fitted to the
parameter's type when the signature is known, places for `ref`,
`view`, and `own` parameters, the map for the map builtins. -/
partial def evalArgs (K : Kernel) (args : List Arg) (params : List Param := []) :
    M (List Val) := do
  let mut vs : List Val := []
  let mut i := 0
  for a in args do
    let pty := (params[i]?).map (·.ty)
    match a with
    | .val e =>
      let v ← evalExpr K e
      let v ← match pty with
        | some t => coerceTo t v
        | none => pure v
      vs := vs ++ [v]
    | .place p =>
      let r ← evalPlace K p
      match r with
      | .mem l =>
        if scalarRef (← get) r then vs := vs ++ [← loadPlace r]
        else vs := vs ++ [.loc l]
      | r => vs := vs ++ [← loadPlace r]
    | .map .. => pure ()
    i := i + 1
  return vs

/-- A call by name: a function of the unit, a builtin, or a kernel
function through the kernel model; `none` when it yields nothing. A
helper that fails here is a call the checker did not mark, an
error. -/
partial def callAny (K : Kernel) (s : Span) (f : String) (args : List Arg) :
    M (Option Val) := do
  let env ← getEnv
  if let some d := env.fn? f then
    return ← callFn K d args
  match env.interface.call? f with
  | some decl =>
    match decl.sig with
    | .builtin => builtin K s f args
    | .fn params ret =>
      let vs ← evalArgs K args params
      match ← kernelCall K decl params ret vs with
      | some v => return v
      | none => fail s!"`{f}` failed with {(← get).errno} at a call the program did not mark"
  | none => fail s!"unknown function `{f}`"

/-- A function of the unit: its parameters bound in a fresh frame, the
body run, its `return` the value. -/
partial def callFn (K : Kernel) (d : Fn) (args : List Arg) : M (Option Val) := do
  useFuel
  let mut frame : List (String × Binding) := []
  for (p, a) in d.params.zip args do
    match ← norm p.ty, a with
    | .ref .., .place q | .view .., .place q =>
      match ← evalPlace K q with
      | .mem l => frame := (p.name, .place l) :: frame
      | _ => fail s!"`{q.print}` is not an aggregate place"
    | .own .., .val e =>
      match ← evalExpr K e with
      | .loc l => frame := (p.name, .place l) :: frame
      | _ => fail s!"`{p.name}` takes an owned reference"
    | t, .val e => frame := (p.name, .val (← coerceTo t (← evalExpr K e))) :: frame
    | t, .place q => frame := (p.name, .val (← coerceTo t (← loadPlace (← evalPlace K q)))) :: frame
    | _, .map .. => pure ()
  let saved := (← get).locals
  modify fun st => { st with locals := frame }
  let restore : M Unit := modify fun st => { st with locals := saved }
  let o ← try execBlock K d.body catch e => do restore; throw e
  restore
  match o with
  | .ret v => return v
  | .normal => return none
  | _ => fail s!"`{d.name}` leaves its body with a loop exit"

/-- The builtins: `copy`, `fill`, `insert`, `delete`, `printk`; the
atomics are statements and `reserve` an acquisition. -/
partial def builtin (K : Kernel) (s : Span) (f : String) (args : List Arg) :
    M (Option Val) := do
  match f, args with
  | "copy", [.place dst, .place src] =>
    match ← evalPlace K dst, ← evalPlace K src with
    | .mem d, .mem sr =>
      let n ← sizeOf d.ty
      let st ← get
      set (st.writeAt d (st.bytesAt sr n))
      return none
    | _, _ => fail "`copy` takes two aggregate places"
  | "fill", [.place dst, .val b] =>
    match ← evalPlace K dst, ← evalExpr K b with
    | .mem d, v =>
      let n ← sizeOf d.ty
      let byte := UInt8.ofNat (toNatMod ((v.toInt?).getD 0) 8)
      modify fun st => st.writeAt d (List.replicate n byte)
      return none
    | _, _ => fail "`fill` takes a place and a byte"
  | "insert", [.map _ m, .place k, .place v] =>
    let st ← get
    let some ms := st.maps.lookup m | fail s!"unknown map `{m}`"
    let kb ← bytesOfPlace (← evalPlace K k) ms.keySize
    let vb ← bytesOfPlace (← evalPlace K v) ms.valueSize
    match ← op (Machine.update m kb vb) with
    | 0 => return none
    | rc => throw (.raise .failed_call (toNatMod rc 32))
  | "delete", [.map _ m, .place k] =>
    let st ← get
    let some ms := st.maps.lookup m | fail s!"unknown map `{m}`"
    let kb ← bytesOfPlace (← evalPlace K k) ms.keySize
    match ← op (Machine.delete m kb) with
    | 0 => return none
    | rc => throw (.raise .failed_call (toNatMod rc 32))
  | "printk", .val (.str _ fmt) :: rest =>
    let vs ← evalArgs K rest
    modify fun st => st.record (.print fmt (vs.map fun v => (settle v).observe))
    return none
  | _, _ =>
    let _ := s
    fail s!"`{f}` has no rule"

/-- A block: its statements in order, its locals dropped after. -/
partial def execBlock (K : Kernel) (ss : List Stmt) : M Outcome := do
  let n := (← get).locals.length
  let o ← try execStmts K ss catch e => do dropTo n; throw e
  dropTo n
  return o

partial def execStmts (K : Kernel) : List Stmt → M Outcome
  | [] => return .normal
  | s :: rest => do
    match ← execStmt K s with
    | .normal => execStmts K rest
    | o => return o

/-- A fallible operation: what it binds, or its failure. A failure of
kind `helper` sets `errno`. -/
partial def execFallible (K : Kernel) : Fallible → M (Option (Option Binding))
  | .view _ off t => do
    let o ← evalExpr K off
    let some ov := o.toInt? | fail "an offset must be an integer"
    let n ← sizeOf t
    let st ← get
    if ov < 0 || ov.toNat + n > st.packet.size then return none
    return some (some (.place { region := .pkt, off := ov.toNat, ty := t,
                                tok := st.layout }))
  | .lookup _ m k => do
    let st ← get
    let some ms := st.maps.lookup m | fail s!"unknown map `{m}`"
    let kb ← bytesOfPlace (← evalPlace K k) ms.keySize
    match ← op (Machine.lookup m kb) with
    | some r => return some (some (.place { region := .shared r, off := 0, ty := ms.valueTy }))
    | none => return none
  | .loadw _ p => do
    match p with
    | .field _ q f =>
      let r ← evalPlace K q
      let v ← loadPlace (← evalPlace K p)
      match r with
      | .mem l =>
        match ← norm l.ty with
        | .struct _ fields =>
          match (fields.find? (·.name == f)).bind (·.pred) with
          | some pred =>
            -- the predicate with the field the value loaded and every
            -- sibling read from the place
            let saved := (← get).locals
            let frame ← siblingFrame l fields f v
            modify fun st => { st with locals := frame }
            let ok ← evalExpr K pred
            modify fun st => { st with locals := saved }
            if ok.truthy then return some (some (.val v)) else return none
          | none => return some (some (.val v))
        | _ => fail "a marked load reads a field"
      | _ => fail "a marked load reads a field of an aggregate"
    | _ => fail "a marked load reads a field"
  | .call _ f args => do
    let env ← getEnv
    match env.interface.call? f with
    | some decl =>
      match decl.sig with
      | .builtin =>
        try
          let v ← builtin K default f args
          return some (v.map .val)
        catch
          | .raise .failed_call r => helperFailed (wrap true 32 r); return none
          | e => throw e
      | .fn params ret =>
        let vs ← evalArgs K args params
        match ← kernelCall K decl params ret vs with
        | some v => return some (v.map bindingOf)
        | none => return none
    | none => fail s!"unknown function `{f}`"
  | .tail _ m i => do
    -- taken, the program is left for the entry; not taken, a failure
    let v ← evalExpr K i
    let idx := toNatMod ((v.toInt?).getD 0) 32
    let st ← get
    match (Machine.tailCall m idx).exec st.machine with
    | .ok (true, mach) =>
      set { st with machine := mach }
      throw (.tail ((mach.tailTo).getD ""))
    | .ok (false, _) => return none
    | .error e => fail e
  | .callopt _ f args => do
    let env ← getEnv
    let some d := env.fn? f | fail s!"unknown function `{f}`"
    match ← callFn K d args with
    | some v => return some (some (.val v))
    | none => return none
  | .coerce _ e t => do
    let v ← evalExpr K e
    match t with
    | .refined _ x _ pred =>
      let saved := (← get).locals
      modify fun st => st.bind x (.val v)
      let ok ← evalExpr K pred
      modify fun st => { st with locals := saved }
      if ok.truthy then return some (some (.val v)) else return none
    | _ => fail "a coercion targets a refinement type"
  | .acquire s r f ty args => do
    let env ← getEnv
    let some decl := env.interface.resource? r | fail s!"no declaration for `{r}`"
    match decl.arg with
    | .place _ =>
      let l ← match args with
        | [.place p] =>
          match ← evalPlace K p with
          | .mem l => pure l
          | _ => fail s!"`{f}` takes a place in a map value"
        | _ => fail s!"`{f}` takes one place"
      let some obj := l.heldObj | fail s!"`{f}` takes a place in a map value"
      op (Machine.lock decl obj)
      return some none
    | .scope =>
      op (Machine.enter decl)
      return some none
    | .call =>
      if f == "reserve" then
        match args, ty with
        | [.map _ m], some t =>
          let n ← sizeOf t
          match ← op (Machine.reserve decl m n) with
          | some id => return some (some (.place { region := .kernel id, off := 0, ty := t }))
          | none =>
            -- the ring is full when its records fill its bytes
            helperFailed (-12)
            return none
        | _, _ => fail "`reserve` takes a ring buffer and a record type"
      else
        -- the call through the machine pushes the object it hands out
        match ← execFallible K (.call s f args) with
        | some (some (.place l)) => return some (some (.place l))
        | some _ => fail s!"`{f}` yields no owned reference"
        | none => return none

partial def execStmt (K : Kernel) (s : Stmt) : M Outcome := do
  match s with
  | .«let» _ _ x ty init =>
    if x == "_" then
      match init with
      | .expr (.call s' f args) => let _ ← callAny K s' f args; return .normal
      | _ => fail "a bare statement is a call"
    match init with
    | .expr e =>
      let v ← evalExpr K e
      let v ← match ty with
        | some t => coerceTo t v
        | none => pure (settle v)
      modify fun st => st.bind x (.val v)
    | .place p =>
      let r ← evalPlace K p
      match r with
      | .mem l =>
        if (← norm l.ty).isScalar then
          let v ← loadPlace r
          let v ← match ty with
            | some t => coerceTo t v
            | none => pure v
          modify fun st => st.bind x (.val v)
        else modify fun st => st.bind x (.place l)
      | _ =>
        let v ← loadPlace r
        modify fun st => st.bind x (.val v)
    | .lit ls fields =>
      let env ← getEnv
      let t ← lift (Koit.Check.structForLiteral env ls ty fields)
      let n ← sizeOf t
      let st ← get
      let (id, st) := st.freshStack
      set (st.setRegion (.stack id) (zeros n))
      let l : Loc := { region := .stack id, off := 0, ty := t }
      for fi in fields do
        let (o, ft) ← fieldOf t fi.name
        storePlace (.mem { l with off := o, ty := ft }) (← evalExpr K fi.value)
      modify fun st => st.bind x (.place l)
    return .normal
  | .assign _ p e =>
    let v ← evalExpr K e
    storePlace (← evalPlace K p) v
    return .normal
  | .ite _ c t e =>
    if (← evalExpr K c).truthy then execBlock K t else execBlock K e
  | .loop _ n body =>
    let cnt ← evalExpr K n
    let some k := cnt.toInt? | fail "a count must be an integer"
    loopN K k.toNat body
  | .«for» _ x lo hi body =>
    let a ← evalExpr K lo
    let b ← evalExpr K hi
    let some av := a.toInt? | fail "a bound must be an integer"
    let some bv := b.toInt? | fail "a bound must be an integer"
    forRange K x av bv body
  | .brk _ => return .brk
  | .cont _ => return .cont
  | .ret _ v =>
    match v with
    | some e => return .ret (some (← evalExpr K e))
    | none => return .ret none
  | .raise _ k r =>
    let v ← evalExpr K r
    throw (.raise k (toNatMod ((v.toInt?).getD 0) 32))
  | .«try» _ x f thn els _ =>
    match ← execFallible K f with
    | some b =>
      let n := (← get).locals.length
      match x, b with
      | "_", _ | _, none => pure ()
      | x, some b => modify fun st => st.bind x b
      let o ← try execBlock K thn catch e => do dropTo n; throw e
      dropTo n
      return o
    | none => execBlock K els
  | .hold _ _ x acq body els =>
    match ← execFallible K acq with
    | some b =>
      let n := (← get).locals.length
      match x, b with
      | some x, some b => modify fun st => st.bind x b
      | _, _ => pure ()
      -- released on the way out unless `move` handed it away, which
      -- the binding records
      let o ← try execBlock K body catch e => do
        release K false ((← get).moved x); dropTo n; throw e
      release K (o matches .normal) ((← get).moved x)
      dropTo n
      return o
    | none =>
      match els with
      | some e => execBlock K e
      | none => fail "an acquisition that cannot fail failed"
  | .atomic _ x op p args =>
    let r ← evalPlace K p
    let old ← loadPlace r
    let vs ← args.mapM (evalExpr K)
    let some o := old.toInt? | fail "an atomic update needs an integer"
    let (s, w) := match old with
      | .int s w _ _ => (s, w)
      | _ => (false, 64)
    let new := atomicResult op s w o vs
    if let some v := new then storePlace r (Val.mkInt s w v)
    if let some x := x then modify fun st => st.bind x (.val old)
    return .normal
  | .invalid _ m => fail m

/-- `loop n s`: the body `n` times, `break` ending it and `continue`
the iteration. -/
partial def loopN (K : Kernel) (n : Nat) (body : List Stmt) : M Outcome := do
  match n with
  | 0 => return .normal
  | k + 1 =>
    useFuel
    match ← execBlock K body with
    | .normal | .cont => loopN K k body
    | .brk => return .normal
    | o => return o

/-- `for x in a..b`: the index a `u64` local of the body. -/
partial def forRange (K : Kernel) (x : String) (i b : Int) (body : List Stmt) :
    M Outcome := do
  if i ≥ b then return .normal
  useFuel
  let n := (← get).locals.length
  modify fun st => st.bind x (.val (Val.mkInt false 64 i))
  let o ← try execBlock K body catch e => do dropTo n; throw e
  dropTo n
  match o with
  | .normal | .cont => forRange K x (i + 1) b body
  | .brk => return .normal
  | o => return o

end

/-! ### Programs and units -/

/-- A run's result: the verdict, the map state, and `printk`'s
lines. -/
structure Halt where
  verdict : Val
  state   : State

/-- A program from its initial state: the body, then the handler of
the failure's kind with `reason` bound, each ending in a `return`.
A `syscall` body may fall off its end, returning 0. -/
def runProgram (K : Kernel) (st : State) (p : Program) : Except String Halt := do
  let heldEmpty : M Unit := do
    unless (← get).held.isEmpty do fail "the program exits holding a resource"
  let body : M Val := do
    match ← execBlock K p.body with
    | .ret (some v) => heldEmpty; coerceTo st.kind.verdictTy v
    | .normal =>
      if st.kind.hasPkt then fail "the body fell off its end"
      heldEmpty
      return Val.mkInt true 32 0
    | _ => fail "the body ends with a loop exit"
  let handled : M Val := do
    try body catch
      | .raise k reason =>
        heldEmpty
        let some h := p.handlers.find? (·.kind == k)
          | fail s!"no handler for `{k}`"
        modify fun st => { st with locals := [("reason", .val (Val.u32 reason))] }
        match ← execBlock K h.body with
        | .ret (some v) => coerceTo st.kind.verdictTy v
        | _ => fail s!"the handler for `{k}` fell off its end"
      | .err m => throw (.err m)
      | .tail p => throw (.tail p)
  -- a taken tail call leaves the program with the entry recorded on
  -- the machine; the verdict is the entry's, which the driver runs
  -- next on this state
  let escaped : M Val := do
    try handled catch
      | .tail _ => pure (Val.mkInt true 32 0)
      | e => throw e
  match escaped.exec st with
  | .ok (v, st') => return { verdict := v, state := st' }
  | .error (.err m) => throw m
  | .error (.raise k _) => throw s!"an unhandled failure of kind `{k}`"
  | .error (.tail p) => throw s!"a tail call to `{p}` escaped"

/-- The map state of a unit at the start of a run: every map empty
or zero-filled. -/
def initMaps (env : Env) (u : CompUnit) :
    Except String (List (String × Machine.MapState)) := do
  let mut ms : List (String × Machine.MapState) := []
  for d in u.maps do
    let lay (t : Ty) : Except String Nat :=
      match env.layout t with
      | .ok (n, _) => .ok n
      | .error e => .error s!"{e}"
    let cap (e : Expr) : Except String Nat :=
      match env.evalConst e with
      | some v => .ok v.toNat
      | none => .error s!"the capacity of `{d.name}` is not constant"
    let m ← match d.kind with
      | .array n v | .percpu n v =>
        let size ← lay v
        -- the initializer's constants as the entries' bytes
        let mut slots : List (Nat × ByteArray) := []
        for h : i in [0:d.init.length] do
          match env.evalConst d.init[i] with
          | some x =>
            slots := slots ++ [(i, ByteArray.mk (Machine.leBytes (Machine.toNatMod x (8 * size)) size).toArray)]
          | none => throw s!"the initializer of `{d.name}` is not constant"
        -- the compiler's bytes fill the one entry of a data map
        if !d.bytes.isEmpty then slots := [(0, ByteArray.mk d.bytes.toArray)]
        pure { decl := d, valueTy := v, valueSize := size, capacity := ← cap n, slots }
      | .hash n k v =>
        pure { decl := d, valueTy := v, valueSize := ← lay v, keyTy := some k,
               keySize := ← lay k, capacity := ← cap n }
      | .ringbuf n =>
        pure { decl := d, valueTy := .int d.span false 8, valueSize := 1,
               capacity := ← cap n }
      | .progArray n _ =>
        -- the entries are the programs the initializer names
        let progs := (List.range d.init.length).filterMap fun i =>
          match (d.init[i]? : Option Expr) with
          | some (Expr.var _ p) => some (i, p)
          | _ => none
        pure { decl := d, valueTy := .int d.span false 32, valueSize := 4,
               keyTy := some (.int d.span false 32), keySize := 4,
               capacity := ← cap n, progs }
    ms := ms ++ [(d.name, m)]
  return ms

/-- The name of a verdict value in the kind's declaration, or the number. -/
def verdictName (decl : KindDecl) (v : Val) : String :=
  match v with
  | .int _ _ x _ =>
    match decl.verdicts.find? fun (_, n) => (n : Int) == x with
    | some (name, _) => name
    | none => toString x
  | v => v.print

/-! ### Reporting -/

/-- A value of type `t` at `bs`, printed by its type: structs by
field, byte arrays as hex, other arrays element by element, a slot
as its name. -/
partial def printBytes (env : Env) (t : Ty) (bs : List UInt8) (fuel : Nat := 32) :
    String :=
  if fuel == 0 then "..." else
  match env.norm t with
  | .ok (.struct _ fields) =>
    let parts := fields.filterMap fun fd =>
      match Koit.Check.fieldOffset env t fd.name, env.layout fd.ty with
      | .ok (some o), .ok (n, _) =>
        some s!"{fd.name}: {printBytes env fd.ty ((bs.drop o).take n) (fuel - 1)}"
      | _, _ => none
    "{ " ++ ", ".intercalate parts ++ " }"
  | .ok (.array _ elem n) =>
    match env.norm elem, env.layout elem, env.evalConst n with
    | .ok (.int _ false 8), _, _ =>
      let shown := bs.take 32
      "0x" ++ hexOf shown ++ (if bs.length > 32 then s!"... ({bs.length} bytes)" else "")
    | _, .ok (esz, _), some len =>
      let count := min len.toNat 16
      let parts := (List.range count).map fun i =>
        printBytes env elem ((bs.drop (i * esz)).take esz) (fuel - 1)
      "[" ++ ", ".intercalate parts ++ (if len.toNat > 16 then ", ..." else "") ++ "]"
    | _, _, _ => "?"
  | .ok (.slot _ n) => n
  | .ok t' =>
    match decode t' bs with
    | some (.be _ v) => "0x" ++ hexOf (bs)  ++ (let _ := v; "")
    | some v => v.print
    | none => "?"
  | .error _ => "?"

/-- The map state, one line per map: the slots or entries that are
not all zero, or a note that none is. -/
def printMaps (env : Env) (maps : List (String × Machine.MapState)) : List String :=
  -- the compiler's own data map, the formats, is not the program's
  (maps.filter (·.2.decl.bytes.isEmpty)).map fun (name, ms) =>
    match ms.decl.kind with
    | .progArray .. =>
      if ms.progs.isEmpty then s!"map {name}: no programs" else
      s!"map {name}:" ++ String.join (ms.progs.map fun (i, p) => s!"\n  [{i}] = {p}")
    | .ringbuf _ =>
      s!"map {name}: {ms.ring.length} record(s)" ++
        String.join (ms.ring.map fun r => s!"\n  0x{hexOf r.toList}")
    | .hash .. =>
      if ms.entries.isEmpty then s!"map {name}: empty" else
      -- by key, so that the kernel's report compares
      let sorted := ms.entries.toArray.qsort (fun a b => a.2.1 < b.2.1) |>.toList
      s!"map {name}:" ++ String.join (sorted.map fun (_, k, v) =>
        s!"\n  {printBytes env (ms.keyTy.getD ms.valueTy) k} => \
          {printBytes env ms.valueTy v.toList}")
    | _ =>
      let live := (ms.slots.filter fun (_, b) => b.toList.any (· != 0))
        |>.toArray.qsort (fun a b => a.1 < b.1) |>.toList
      if live.isEmpty then s!"map {name}: all zero" else
      s!"map {name}:" ++ String.join (live.map fun (i, b) =>
        s!"\n  [{i}] = {printBytes env ms.valueTy b.toList}")

/-- The bytes of a hex string, `0x` optional; `none` when it is not
hex. -/
def parseHex (s : String) : Option ByteArray := do
  let s := if s.startsWith "0x" then s.drop 2 |>.toString else s
  let s := String.ofList (s.toList.filter fun c => c != ' ' && c != '_')
  let cs := s.toList
  if cs.length % 2 != 0 then none
  let rec go : List Char → Option (List UInt8)
    | [] => some []
    | a :: b :: rest => do
      let hi ← a.toNat |> fun _ => hexDigit a
      let lo ← hexDigit b
      let tl ← go rest
      some (UInt8.ofNat (hi * 16 + lo) :: tl)
    | _ => none
  return ByteArray.mk (← go cs).toArray
where
  hexDigit (c : Char) : Option Nat :=
    if c.isDigit then some (c.toNat - '0'.toNat)
    else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
    else if 'A' ≤ c && c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
    else none

/-- What one program's run reports. -/
structure Report where
  program : String
  verdict : String
  log     : List String

/-- A unit's programs run in order over one map state, each from the
same input packet and context, on the synthetic kernel; with `only`,
the named program alone. The unit must have passed the checker. -/
def runUnit (pre : Interface) (u : CompUnit) (packet : ByteArray)
    (ctx : List (String × Nat)) (only : Option String) (fuel : Nat) :
    Except String (List Report × List String) := do
  let env : Env := { interface := pre, license := u.license.map (·.2),
                     types := u.types, consts := u.consts,
                     configs := u.configs, maps := u.maps, fns := u.fns,
                     contracts := u.contracts }
  let mut maps ← initMaps env u
  let mut reports : List Report := []
  for p in u.programs do
    if only.isSome && only != some p.name then continue
    let some decl := pre.kind? p.kind | throw s!"unknown kind `{p.kind}`"
    let st := initState env decl packet ctx maps fuel
    let mut h ← runProgram Machine.synthetic st p
    -- a taken tail call: the entry runs on the same machine state,
    -- its trace continuing, and its verdict is the invocation's
    let mut hops := 0
    while h.state.machine.tailTo.isSome && hops ≤ Machine.maxTailCalls do
      let some name := h.state.machine.tailTo | break
      let some q := u.programs.find? (·.name == name) | throw s!"no program `{name}`"
      let some qdecl := pre.kind? q.kind | throw s!"unknown kind `{q.kind}`"
      let mach := { h.state.machine with tailTo := none }
      let st2 := { initState env qdecl packet ctx mach.maps fuel with machine := mach }
      h ← runProgram Machine.synthetic st2 q
      hops := hops + 1
    maps := h.state.maps
    reports := reports ++ [{ program := p.name, verdict := verdictName decl h.verdict,
                             log := h.state.log }]
  return (reports, printMaps env maps)

/-- The evaluator agrees with the relation: a run it completes is a
derivation. Stated now, proved after the design settles. -/
theorem interp_sound (K : Kernel) (st : State) (p : Core.Program) (h : Halt) :
    runProgram K st p = .ok h → ExecProgram K st p (.halt h.verdict) h.state := by
  sorry

end Koit.Core.Sem
