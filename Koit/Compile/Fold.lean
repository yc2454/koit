import Koit.Core.Interp

/-!
Pass A, fold and select, Core to Core: every constant expression
with an integer value becomes a literal, at its type when it has one;
every `if` whose condition is a constant becomes its live branch;
every `array[1]` map is marked for direct value access and every
other map for lookup by helper; and the cap of each `for` loop, from
the checker, travels with the result for the flattening. Nothing else
changes. A constant whose value is a byte-order pattern, `hton` of a
constant, has no Core literal and stays a name, which the lowering
folds to an immediate at its width.

This is the free pass, separate so that the lowering never sees a
constant or a dead branch; its theorem says a run of the folded
program is a run of the source.
-/

namespace Koit.Compile

open Koit (Span)
open Koit.Core
open Koit.Check (Env Checked)
open Koit.Facts (Caps)

/-- What the fold yields: the unit, the maps reached by direct value
access, and the loop caps. -/
structure Folded where
  unit   : CompUnit
  direct : List String
  caps   : Caps
  deriving Inhabited

/-- The value of a constant expression, through Core's own evaluator
on an empty frame; `none` when the expression is not constant. -/
def constVal (env : Env) (row : Interface.KindRow) (e : Expr) : Option Sem.Val :=
  if env.isConstExpr e then
    let st := Sem.initState env row ByteArray.empty [] [] 64
    match (Sem.evalExpr Machine.synthetic e).exec st with
    | .ok (v, _) => some v
    | .error _ => none
  else none

/-- A literal for a constant's value: bare for a value of no type
yet, cast to its type otherwise, which is what the value's type is
in the evaluator. -/
def litOf (s : Span) (v : Sem.Val) : Option Expr :=
  match v with
  | .int _ _ x true => some (.lit s (Machine.toNatMod x 64) (toString (Machine.toNatMod x 64)))
  | .int sg w x false =>
    let n := Machine.toNatMod x w
    some (.cast s (.lit s n (toString n)) (.int s sg w))
  | .bool b => some (.bool s b)
  | _ => none

mutual

partial def foldExpr (env : Env) (row : Interface.KindRow) (e : Expr) : Expr :=
  match e with
  | .lit .. | .char .. | .bool .. | .str .. | .errno .. | .invalid .. => e
  | .var s x =>
    if (env.local? x).isSome then e else
    match constVal env row e with
    | some v => (litOf s v).getD e
    | none => e
  | .size s t =>
    match constVal env row e with
    | some v => (litOf s v).getD e
    | none => e
  | .arith s op l r =>
    match constVal env row e with
    | some v => (litOf s v).getD (.arith s op (foldExpr env row l) (foldExpr env row r))
    | none => .arith s op (foldExpr env row l) (foldExpr env row r)
  | .cmp s op l r => .cmp s op (foldExpr env row l) (foldExpr env row r)
  | .not s e => .not s (foldExpr env row e)
  | .and s l r => .and s (foldExpr env row l) (foldExpr env row r)
  | .or s l r => .or s (foldExpr env row l) (foldExpr env row r)
  | .cast s e t =>
    match constVal env row (.cast s e t) with
    | some v => (litOf s v).getD (.cast s (foldExpr env row e) t)
    | none => .cast s (foldExpr env row e) t
  | .hton s e => .hton s (foldExpr env row e)
  | .ntoh s e => .ntoh s (foldExpr env row e)
  | .read s p => .read s (foldPlace env row p)
  | .move .. => e
  | .call s f args => .call s f (args.map (foldArg env row))

partial def foldPlace (env : Env) (row : Interface.KindRow) : Place → Place
  | .field s p f => .field s (foldPlace env row p) f
  | .index s p i => .index s (foldPlace env row p) (foldExpr env row i)
  | .slot s m i => .slot s m (foldExpr env row i)
  | .deref s e => .deref s (foldExpr env row e)
  | p => p

partial def foldArg (env : Env) (row : Interface.KindRow) : Arg → Arg
  | .val e => .val (foldExpr env row e)
  | .place p => .place (foldPlace env row p)
  | a => a

end

def foldFallible (env : Env) (row : Interface.KindRow) : Fallible → Fallible
  | .view s off t => .view s (foldExpr env row off) t
  | .lookup s m k => .lookup s m (foldPlace env row k)
  | .loadw s p => .loadw s (foldPlace env row p)
  | .call s f args => .call s f (args.map (foldArg env row))
  | .acquire s r f t args => .acquire s r f t (args.map (foldArg env row))
  | .callopt s f args => .callopt s f (args.map (foldArg env row))
  | .coerce s e t => .coerce s (foldExpr env row e) t

def foldInit (env : Env) (row : Interface.KindRow) : Init → Init
  | .expr e => .expr (foldExpr env row e)
  | .place p => .place (foldPlace env row p)
  | .lit s fs => .lit s (fs.map fun f => { f with value := foldExpr env row f.value })

/-- Whether a condition is a constant, and which branch it selects.
The names a local shadows are not constants. -/
def decided (env : Env) (row : Interface.KindRow) (c : Expr) : Option Bool :=
  match constVal env row c with
  | some v => some v.truthy
  | none => none

mutual

/-- A block, with each `if` on a constant replaced by its live
branch. Locals shadow constants, so the environment tracks the
names bound so far. -/
partial def foldStmts (env : Env) (row : Interface.KindRow) : List Stmt → List Stmt
  | [] => []
  | s :: rest =>
    let (ss, env') := foldStmt env row s
    ss ++ foldStmts env' row rest

partial def foldStmt (env : Env) (row : Interface.KindRow) (s : Stmt) :
    List Stmt × Env :=
  let bindName (x : String) : Env :=
    env.bind { name := x, ty := .bool s.span, mutable := false, origin := .stack }
  match s with
  | .«let» sp m x ty init =>
    ([.«let» sp m x ty (foldInit env row init)], if x == "_" then env else bindName x)
  | .assign sp p e => ([.assign sp (foldPlace env row p) (foldExpr env row e)], env)
  | .ite sp c t e =>
    match decided env row c with
    | some true => (foldStmts env row t, env)
    | some false => (foldStmts env row e, env)
    | none => ([.ite sp (foldExpr env row c) (foldStmts env row t) (foldStmts env row e)], env)
  | .loop sp n body => ([.loop sp (foldExpr env row n) (foldStmts env row body)], env)
  | .«for» sp x lo hi body =>
    ([.«for» sp x (foldExpr env row lo) (foldExpr env row hi)
        (foldStmts (bindName x) row body)], env)
  | .ret sp (some e) => ([.ret sp (some (foldExpr env row e))], env)
  | .raise sp k e => ([.raise sp k (foldExpr env row e)], env)
  | .«try» sp x f thn els ex =>
    ([.«try» sp x (foldFallible env row f)
        (foldStmts (if x == "_" then env else bindName x) row thn)
        (foldStmts env row els) ex], env)
  | .hold sp r x acq body els =>
    ([.hold sp r x (foldFallible env row acq)
        (foldStmts (match x with | some x => bindName x | none => env) row body)
        (els.map (foldStmts env row))], env)
  | .atomic sp x op p args =>
    ([.atomic sp x op (foldPlace env row p) (args.map (foldExpr env row))],
     match x with | some n => bindName n | none => env)
  | s => ([s], env)

end

/-- A function's body folded; a function has no kind, so the verdict
names do not occur in it and any row serves. -/
def foldFn (env : Env) (row : Interface.KindRow) (f : Fn) : Fn :=
  let env := f.params.foldl (fun env p =>
    env.bind { name := p.name, ty := p.ty, mutable := false, origin := .stack }) env.top
  { f with body := foldStmts env row f.body }

def foldProgram (env : Env) (p : Program) : Program :=
  match env.interface.kind? p.kind with
  | some row =>
    let env := { env.top with kind := some row }
    { p with body := foldStmts env row p.body,
             handlers := p.handlers.map fun h =>
               { h with body := foldStmts (env.bind { name := "reason", ty := Interface.tU32,
                                                       mutable := false, origin := .stack })
                                  row h.body } }
  | none => p

/-- Whether a map is reached by direct value access: a plain array
map with one slot. -/
def isDirect (env : Env) (d : MapDecl) : Bool :=
  match d.kind with
  | .array n _ => env.evalConst n == some 1
  | _ => false

/-- Pass A on a checked unit. -/
def fold (pre : Interface) (u : CompUnit) (checked : Checked) : Folded :=
  let env : Env := { interface := pre, license := u.license.map (·.2), types := u.types,
                     consts := u.consts, configs := u.configs, maps := u.maps,
                     fns := u.fns, contracts := u.contracts }
  let row := pre.kinds.head?.getD default
  { unit := { u with fns := u.fns.map (foldFn env row),
                     programs := u.programs.map (foldProgram env) },
    direct := (u.maps.filter (isDirect env)).map (·.name),
    caps := checked.caps }

/-- The environment of a folded unit, as the state carries it. -/
def foldEnv (pre : Interface) (u : CompUnit) (checked : Checked) (env : Env) : Env :=
  { env with fns := (fold pre u checked).unit.fns }

/-- Theorem A: a run of a program is a run of its folded form, over
the folded unit's functions. A constant evaluates to its value by the
rules for names, and a folded conditional takes the branch its
condition selects. Stated now, proved after the design settles. -/
theorem fold_correct (pre : Interface) (u : CompUnit) (checked : Checked) (K : Machine.Kernel) :
    Check.checkUnit pre u = .ok checked →
    ∀ p ∈ u.programs, ∀ st o st',
      Sem.ExecProgram K st p o st' ↔
      Sem.ExecProgram K { st with env := foldEnv pre u checked st.env }
        (foldProgram st.env p) o { st' with env := foldEnv pre u checked st'.env } := by
  sorry

end Koit.Compile
