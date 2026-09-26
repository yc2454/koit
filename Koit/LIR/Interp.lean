import Koit.LIR.Semantics
import Koit.Core.Interp

/-!
The LIR evaluator: the executable form of the relations in
`Semantics.lean`, run by `koitc run --lir` over the same synthetic
kernel, packet, and maps as Core's evaluator, so that the runner can
compare the two level by level. Statements are executed
structurally; a `br` and a `return` are outcomes the enclosing
construct consumes, and a failure or an error is an abort that the
`unwind` of each enclosing call intercepts on its way to the
program's handler. The reporting is Core's, so that the two runs
print alike.
-/

namespace Koit.LIR.Sem

open Koit.Core (Kind)
open Koit.Core.Sem (Val Loc Abort)
open Koit.Machine (Kernel HeldRes)

/-- How a statement ends when it does not abort. -/
inductive LOut where
  | normal
  | br (n : Nat)
  | ret (v : Option Val)
  deriving Repr, Inhabited

/-- Two held stacks read as declarations and objects. -/
def heldEq (a b : List HeldRes) : Bool :=
  a.length == b.length && (a.zip b).all fun (h, h') => h.same h'

/-- The arguments' values; a map named among them is not evaluated. -/
def evalArgs (args : List Expr) : M (List Val) := do
  let st ← get
  (args.filter fun e => match e with | .mapPtr _ => false | _ => true).mapM
    fun e => liftRes (evalExpr st e)

def bindOpt (x : Option String) (v : Option Val) : M Unit := do
  match x, v with
  | some x, some v => modify fun st => st.bind x v
  | some x, none => fail s!"nothing to bind to `{x}`"
  | none, _ => pure ()

mutual

partial def execStmts (K : Kernel) (fns : Fns) : List Stmt → M LOut
  | [] => return .normal
  | s :: rest => do
    match ← execStmt K fns s with
    | .normal => execStmts K fns rest
    | o => return o

partial def execStmt (K : Kernel) (fns : Fns) (s : Stmt) : M LOut := do
  match s with
  | .«let» _ x t e => execLet x t e; return .normal
  | .assign _ x e => execAssign x e; return .normal
  | .store _ w a e => execStore w a e; return .normal
  | .ctxStore _ f e =>
    let st ← get
    let v ← liftRes (evalExpr st e)
    unless (st.ctx.lookup f).isSome do fail s!"the context has no field `{f}`"
    set { st with ctx := st.ctx.map fun (g, w) => if g == f then (g, v) else (g, w) }
    return .normal
  | .frame _ x n src => execFrame x n src; return .normal
  | .ite _ c t e =>
    if ← liftRes (evalCond (← get) c) then execStmts K fns t else execStmts K fns e
  | .block _ body =>
    match ← execStmts K fns body with
    | .normal | .br 0 => return .normal
    | .br (n + 1) => return .br n
    | o => return o
  | .loop _ body => runLoop K fns body
  | .br _ n => return .br n
  | .ret _ none => return .ret none
  | .ret _ (some e) => return .ret (some (← liftRes (evalExpr (← get) e)))
  | .raise _ k e =>
    let v ← liftRes (evalExpr (← get) e)
    throw (.raise k ((pattern 32 v).getD 0))
  | .call _ x f args u a =>
    let some d := fns.find? (·.name == f) | fail s!"unknown function `{f}`"
    let vs ← evalArgs args
    let frame ← callFrame d vs
    useFuel
    let st0 ← get
    set { st0 with locals := frame }
    let restore : M Unit := modify fun st => { st with locals := st0.locals }
    let o ← try execStmts K fns d.body catch e => do
      restore
      match e with
      | .raise .. =>
        -- the releases the call site owes, then the failure goes on
        let _ ← execStmts K fns (u.getD [])
        throw e
      | .err _ | .tail _ => throw e
    restore
    unless heldEq (← get).held st0.held do
      fail s!"`{f}` returns holding something it did not hold at entry"
    match o with
    | .ret (some v) => bindOpt x (some v); return .normal
    | .ret none => execStmts K fns (a.getD [])
    | .normal =>
      if x.isSome then fail s!"`{f}` ends without a value"
      return .normal
    | .br _ => fail s!"`{f}` leaves its body with a loop exit"
  | .builtin _ x b args =>
    let vs ← evalArgs args
    let v ← execBuiltin b vs
    match x with
    | some _ => bindOpt x v
    | none => pure ()
    return .normal
  | .kernel _ x h args =>
    let vs ← evalArgs args
    let v ← execKernel K h (mapPtrArg? args) vs
    bindOpt x (some v)
    return .normal

partial def runLoop (K : Kernel) (fns : Fns) (body : List Stmt) : M LOut := do
  useFuel
  match ← execStmts K fns body with
  | .normal | .br 0 => runLoop K fns body
  | .br (n + 1) => return .br n
  | o => return o

end

/-- A run's result: the verdict and the state. -/
structure Halt where
  verdict : Val
  state   : State

/-- A program from its initial state, as Core's `runProgram` runs
Core's. -/
def runProgram (K : Kernel) (fns : Fns) (st : State) (p : Program) : Except String Halt := do
  let heldEmpty : M Unit := do
    unless (← get).held.isEmpty do fail "the program exits holding a resource"
  let body : M Val := do
    match ← execStmts K fns p.body with
    | .ret (some v) => heldEmpty; return fitCore st.kind.verdictTy v
    | .normal =>
      if st.kind.hasPkt then fail "the body fell off its end"
      heldEmpty
      return Val.mkInt true 32 0
    | .ret none => fail "the body ends without a verdict"
    | .br _ => fail "the body ends outside a loop"
  let handled : M Val := do
    try body catch
      | .raise k reason =>
        heldEmpty
        let some h := p.handlers.find? (·.kind == k) | fail s!"no handler for `{k}`"
        modify fun st => { st with locals := [("reason", Val.u32 reason)] }
        match ← execStmts K fns h.body with
        | .ret (some v) => return fitCore st.kind.verdictTy v
        | _ => fail s!"the handler for `{k}` does not return a verdict"
      | .err m => throw (.err m)
      | .tail p => throw (.tail p)
  -- a taken tail call leaves the program with the entry recorded on
  -- the machine, for the driver
  let escaped : M Val := do
    try handled catch
      | .tail _ => pure (Val.mkInt true 32 0)
      | e => throw e
  match escaped.exec st with
  | .ok (v, st') => return { verdict := v, state := st' }
  | .error (.err m) => throw m
  | .error (.raise k _) => throw s!"an unhandled failure of kind `{k}`"
  | .error (.tail p) => throw s!"a tail call to `{p}` escaped"

/-- A unit's programs run in order over one map state, as Core's
`runUnit` does, reporting the same lines. -/
def runUnit (pre : Interface) (core : Core.CompUnit) (u : CompUnit) (packet : ByteArray)
    (ctx : List (String × Nat)) (only : Option String) (fuel : Nat) :
    Except String (List Core.Sem.Report × List String) := do
  let env : Check.Env := { interface := pre, license := core.license.map (·.2),
                           types := core.types, consts := core.consts,
                           configs := core.configs, maps := core.maps, fns := core.fns,
                           contracts := core.contracts }
  let mut maps ← Core.Sem.initMaps env core
  let mut reports : List Core.Sem.Report := []
  for p in u.programs do
    if only.isSome && only != some p.name then continue
    let some decl := pre.kind? p.kind | throw s!"unknown kind `{p.kind}`"
    let st := initState env decl packet ctx maps fuel
    let mut h ← runProgram Machine.synthetic u.fns st p
    -- a taken tail call: the entry runs on the same machine state
    let mut hops := 0
    while h.state.machine.tailTo.isSome && hops ≤ Machine.maxTailCalls do
      let some name := h.state.machine.tailTo | break
      let some q := u.programs.find? (·.name == name) | throw s!"no program `{name}`"
      let some qdecl := pre.kind? q.kind | throw s!"unknown kind `{q.kind}`"
      let mach := { h.state.machine with tailTo := none }
      let st2 := { initState env qdecl packet ctx mach.maps fuel with machine := mach }
      h ← runProgram Machine.synthetic u.fns st2 q
      hops := hops + 1
    maps := h.state.maps
    reports := reports ++ [{ program := p.name, verdict := Core.Sem.verdictName decl h.verdict,
                             log := h.state.log }]
  return (reports, Core.Sem.printMaps env maps)

/-- The evaluator agrees with the relation: a run it completes is a
derivation. Stated now, proved after the design settles. -/
theorem lirInterp_sound (K : Kernel) (fns : Fns) (st : State) (p : Program) (h : Halt) :
    runProgram K fns st p = .ok h → ExecProgram K fns st p (.halt h.verdict) h.state := by
  sorry

end Koit.LIR.Sem
