import Koit.LIR.Print

/-!
Well-formedness of LIR: the check the lowering satisfies by
construction and the flattening assumes. Each name is declared once,
every operator and comparison is applied at the type of its operands,
addresses are `ptr` locals or the packet's bounds, `br` stays inside
its constructs, `return` and `raise` appear where they may, a call
matches its callee's signature and carries `unwind` and `absent`
exactly when the callee needs them, and handlers end in `return`.
-/

namespace Koit.LIR

open Koit (Span)
open Koit.Core (ArithOp CmpOp AtomicOp Kind Resource)

/-- The result of a builtin, when it has one: a location for a
lookup or a reservation, a signed 64-bit return code for an update
or a delete, the previous value for an atomic fetch. -/
def Builtin.result : Builtin → Option Ty
  | .lookup _ | .reserve .. => some .ptr
  | .update _ | .delete _ => some .i64
  | .atomic _ s w true => some (.int s w)
  | _ => none

/-- The result of a kernel function's row, as its `r0`: a location
when the row yields an owned or referenced place, the 64-bit signed
return otherwise, which carries the failure signal of a scalar-result
row. -/
def rowResult (row : Prelude.CallRow) : Ty :=
  match row.sig with
  | .fn _ (some (.own ..)) | .fn _ (some (.ref ..)) => .ptr
  | _ => .i64

/-- What the well-formedness check knows about the code around a
statement. -/
structure WfCtx where
  pre     : Prelude
  kind    : Option Prelude.KindRow
  fns     : List Fn
  /-- The result type of the function, or the verdict type of the
  program or handler. -/
  ret     : Option Ty
  opt     : Bool
  /-- Whether `raise` may appear: a `fails` function or a program
  body. -/
  mayRaise : Bool
  inHandler : Bool
  depth   : Nat := 0

abbrev Γ := List (String × Ty)

abbrev W := Except String

def wfErr (msg : String) : W α := throw msg

mutual

/-- The type of an expression under `Γ`; a literal takes the type
`expected`, when there is one, at its width. -/
partial def typeOf (K : WfCtx) (Γ : Γ) (expected : Option Ty) : Expr → W Ty
  | .lit w k => do
    unless k < 2 ^ w do wfErr s!"the literal {k} does not fit in {w} bits"
    match expected with
    | some (.int s w') =>
      unless w' == w do wfErr s!"a literal of width {w} where {w'} is expected"
      return .int s w
    | _ => return .int false w
  | .var x =>
    match Γ.lookup x with
    | some t => return t
    | none => wfErr s!"`{x}` is not declared"
  | .arith op s w l r => do
    let tl ← typeOf K Γ (some (.int s w)) l
    let tr ← typeOf K Γ (some (.int s w)) r
    unless tl == .int s w && tr == .int s w do
      wfErr s!"`{op.spelling}({Ty.print (.int s w)})` on `{tl.print}` and \
        `{tr.print}`"
    return .int s w
  | .cast s w s' w' e => do
    let t ← typeOf K Γ (some (.int s w)) e
    unless t == .int s w do
      wfErr s!"a cast from `{Ty.print (.int s w)}` of a `{t.print}`"
    return .int s' w'
  | .bswap w e => do
    let t ← typeOf K Γ (some (.int false w)) e
    unless t == .int false w do wfErr s!"`bswap({w})` of a `{t.print}`"
    return .int false w
  | .load s w a => do
    typeOfAddr K Γ a
    return .int s w
  | .ctx f =>
    match K.kind with
    | some row =>
      match row.ctx.find? (·.name == f) with
      | some cf =>
        match cf.ty with
        | .int _ s w => return .int s w
        | _ => wfErr s!"the context field `{f}` is not an integer"
      | none => wfErr s!"the context has no field `{f}`"
    | none => wfErr "`ctx` outside a program"
  | .addr a => do
    typeOfAddr K Γ a
    return .ptr

partial def typeOfAddr (K : WfCtx) (Γ : Γ) : Addr → W Unit
  | .var x =>
    match Γ.lookup x with
    | some .ptr => return ()
    | some t => wfErr s!"`{x}` is a `{t.print}`, not an address"
    | none => wfErr s!"`{x}` is not declared"
  | .plus a _ => typeOfAddr K Γ a
  | .index a e _ => do
    typeOfAddr K Γ a
    match ← typeOf K Γ none e with
    | .int .. => return ()
    | .ptr => wfErr "an index is a scalar"
  | .pktData | .pktEnd =>
    -- in a function, the bounds serve the element test of a view
    -- parameter, and a view exists in packet kinds only
    match K.kind with
    | some row => if row.hasPkt then return () else wfErr "no packet in this kind"
    | none => return ()
  | .mapval .. => return ()

end

def wfCond (K : WfCtx) (Γ : Γ) (c : Cond) : W Unit := do
  let tl ← typeOf K Γ (some (.int c.signed c.w)) c.l
  let tr ← typeOf K Γ (some (.int c.signed c.w)) c.r
  match tl, tr with
  | .ptr, .ptr => return ()
  | .ptr, .int .. | .int .., .ptr =>
    let isZero := match c.l, c.r with
      | .lit 64 0, _ | _, .lit 64 0 => true
      | _, _ => false
    unless isZero && (c.op == .eq || c.op == .ne) do
      wfErr "an address compares with an address, or with `0(64)` under \
        `==` or `!=`"
  | .int .., .int .. =>
    unless tl == .int c.signed c.w && tr == .int c.signed c.w do
      wfErr s!"`{c.op.spelling}({Ty.print (.int c.signed c.w)})` on \
        `{tl.print}` and `{tr.print}`"

/-- The names a block declares, at any depth, for the declare-once
rule. -/
partial def declared : List Stmt → List String
  | [] => []
  | s :: rest =>
    (match s with
     | .«let» _ x .. | .frame _ x .. => [x]
     | .ite _ _ t e => declared t ++ declared e
     | .block _ b | .loop _ b => declared b
     | .call _ x _ _ u a =>
       x.toList ++ (u.map declared).getD [] ++ (a.map declared).getD []
     | .builtin _ x .. | .kernel _ x .. => x.toList
     | _ => []) ++ declared rest

/-- Whether a block ends in `return` on every path. -/
partial def returns : List Stmt → Bool
  | [] => false
  | ss =>
    match ss.getLast! with
    | .ret .. | .raise .. | .br .. => true
    | .ite _ _ t e => returns t && returns e
    | .block _ b => returns b
    | _ => false

/-- Whether a block is made of releases only, as an `unwind` is. -/
def releasesOnly (K : WfCtx) (ss : List Stmt) : Bool :=
  ss.all fun
    | .builtin _ none .unlock _ | .builtin _ none .discard _ => true
    | .builtin _ none (.leave _) _ => true
    | .kernel _ none h _ =>
      match K.pre.call? h with
      | some row => K.pre.resources.any fun r =>
          r.normalExit == row.kernel || r.abnormalExit == row.kernel
      | none => false
    | _ => false

mutual

/-- A block under `Γ`, yielding the environment after it. -/
partial def wfStmts (K : WfCtx) (Γ : Γ) : List Stmt → W Koit.LIR.Γ
  | [] => return Γ
  | s :: rest => do
    let Γ ← wfStmt K Γ s
    wfStmts K Γ rest

partial def wfStmt (K : WfCtx) (Γ : Γ) (s : Stmt) : W Koit.LIR.Γ := do
  match s with
  | .«let» _ x t e =>
    let t' ← typeOf K Γ (some t) e
    unless t' == t do
      wfErr s!"`let {x} : {t.print}` from a `{t'.print}`"
    return (x, t) :: Γ
  | .assign _ x e =>
    match Γ.lookup x with
    | some t =>
      let t' ← typeOf K Γ (some t) e
      unless t' == t do wfErr s!"`{x} := ...` stores a `{t'.print}` into a `{t.print}`"
      return Γ
    | none => wfErr s!"`{x}` is not declared"
  | .store _ w a e =>
    typeOfAddr K Γ a
    match ← typeOf K Γ (some (.int false w)) e with
    | .int _ w' => unless w' == w do wfErr s!"`store({w})` of a {w'}-bit value"
    | .ptr => wfErr "a location is never stored"
    return Γ
  | .ctxStore _ f e =>
    match K.kind with
    | some row =>
      match row.ctx.find? (·.name == f) with
      | some cf =>
        unless cf.writable do wfErr s!"the context field `{f}` is read-only"
        match cf.ty with
        | .int _ s w =>
          let t ← typeOf K Γ (some (.int s w)) e
          unless t == .int s w do wfErr s!"`ctx {f} <- ...` of a `{t.print}`"
        | _ => wfErr s!"the context field `{f}` is not an integer"
      | none => wfErr s!"the context has no field `{f}`"
    | none => wfErr "`ctx` outside a program"
    return Γ
  | .frame _ x _ _ => return (x, .ptr) :: Γ
  | .ite _ c t e =>
    wfCond K Γ c
    let _ ← wfStmts K Γ t
    let _ ← wfStmts K Γ e
    return Γ
  | .block _ b | .loop _ b =>
    let _ ← wfStmts { K with depth := K.depth + 1 } Γ b
    return Γ
  | .br _ n =>
    unless n < K.depth do wfErr s!"`br {n}` inside {K.depth} constructs"
    return Γ
  | .ret _ none =>
    if K.ret.isSome && !K.opt then wfErr "`return` without a value"
    return Γ
  | .ret _ (some e) =>
    match K.ret with
    | some t =>
      let t' ← typeOf K Γ (some t) e
      unless t' == t do wfErr s!"`return` of a `{t'.print}` where `{t.print}` is expected"
    | none => wfErr "`return e` in a function without a result"
    return Γ
  | .raise _ _ e =>
    unless K.mayRaise do wfErr "`raise` outside a `fails` function or a program body"
    let t ← typeOf K Γ (some .u32) e
    unless t == .u32 do wfErr "a reason is a `u32`"
    return Γ
  | .call _ x f args u a =>
    let some d := K.fns.find? (·.name == f) | wfErr s!"unknown function `{f}`"
    unless args.length == d.params.length do
      wfErr s!"`{f}` takes {d.params.length} arguments, {args.length} given"
    for (p, e) in d.params.zip args do
      let t ← typeOf K Γ (some p.ty) e
      unless t == p.ty do
        wfErr s!"`{f}` takes `{p.name} : {p.ty.print}`, a `{t.print}` given"
    unless u.isSome == d.fails do
      wfErr s!"a call to `{f}` carries `unwind` exactly when `{f}` is `fails`"
    unless a.isSome == d.opt do
      wfErr s!"a call to `{f}` carries `absent` exactly when `{f}` returns `T ?`"
    if d.fails && K.inHandler then
      wfErr s!"a handler calls the `fails` function `{f}`"
    if let some u := u then
      unless releasesOnly K u do wfErr "an `unwind` holds releases only"
    if let some a := a then
      let _ ← wfStmts K Γ a
    match x, d.ret with
    | some x, some t => return (x, t) :: Γ
    | some _, none => wfErr s!"`{f}` returns nothing"
    | none, _ => return Γ
  | .builtin _ x b args =>
    for e in args do
      let _ ← typeOf K Γ none e
    match x, b.result with
    | some x, some t => return (x, t) :: Γ
    | some x, none => wfErr s!"`{b.print}` yields nothing to bind to `{x}`"
    | none, _ => return Γ
  | .kernel _ x h args =>
    let some row := K.pre.call? h | wfErr s!"unknown kernel function `{h}`"
    for e in args do
      let _ ← typeOf K Γ none e
    match x with
    | some x => return (x, rowResult row) :: Γ
    | none => return Γ

end

/-- Every name declared once. -/
def declareOnce (what : String) (ss : List Stmt) (params : List String) : W Unit := do
  let names := params ++ declared ss
  let dup := names.find? fun x => names.count x > 1
  if let some x := dup then wfErr s!"{what} declares `{x}` twice"

/-- A unit is well-formed: every function against its signature,
every program body and handler as section 4 of the design says. -/
def wf (pre : Prelude) (u : CompUnit) : W Unit := do
  for f in u.fns do
    let K : WfCtx := { pre, kind := none, fns := u.fns, ret := f.ret, opt := f.opt,
                       mayRaise := f.fails, inHandler := false }
    declareOnce s!"`{f.name}`" f.body (f.params.map (·.name))
    let Γ0 := f.params.map fun p => (p.name, p.ty)
    let _ ← wfStmts K Γ0 f.body
      |>.mapError (s!"in `{f.name}`: " ++ ·)
  for p in u.programs do
    let some row := pre.kind? p.kind | wfErr s!"unknown kind `{p.kind}`"
    let vt : Ty := match row.verdictTy with
      | .int _ s w => .int s w
      | _ => .u32
    let K : WfCtx := { pre, kind := some row, fns := u.fns, ret := some vt, opt := false,
                       mayRaise := true, inHandler := false }
    declareOnce s!"`{p.name}`" p.body []
    let _ ← wfStmts K [] p.body |>.mapError (s!"in `{p.name}`: " ++ ·)
    if row.hasPkt && !returns p.body then
      wfErr s!"the body of `{p.name}` does not end in `return` on every path"
    for h in p.handlers do
      let Kh := { K with mayRaise := false, inHandler := true }
      declareOnce s!"the handler for `{h.kind}` of `{p.name}`" h.body ["reason"]
      let _ ← wfStmts Kh [("reason", .u32)] h.body
        |>.mapError (s!"in the handler for `{h.kind}` of `{p.name}`: " ++ ·)
      unless returns h.body do
        wfErr s!"the handler for `{h.kind}` of `{p.name}` does not end in `return`"

end Koit.LIR
