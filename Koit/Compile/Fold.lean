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
def constVal (env : Env) (decl : Interface.KindDecl) (e : Expr) : Option Sem.Val :=
  if env.isConstExpr e then
    let st := Sem.initState env decl ByteArray.empty [] [] 64
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

partial def foldExpr (env : Env) (decl : Interface.KindDecl) (e : Expr) : Expr :=
  match e with
  | .lit .. | .char .. | .bool .. | .str .. | .errno .. | .invalid .. => e
  | .var s x =>
    if (env.local? x).isSome then e else
    match constVal env decl e with
    | some v => (litOf s v).getD e
    | none => e
  | .size s t =>
    match constVal env decl e with
    | some v => (litOf s v).getD e
    | none => e
  | .arith s op l r =>
    match constVal env decl e with
    | some v => (litOf s v).getD (.arith s op (foldExpr env decl l) (foldExpr env decl r))
    | none => .arith s op (foldExpr env decl l) (foldExpr env decl r)
  | .cmp s op l r => .cmp s op (foldExpr env decl l) (foldExpr env decl r)
  | .not s e => .not s (foldExpr env decl e)
  | .and s l r => .and s (foldExpr env decl l) (foldExpr env decl r)
  | .or s l r => .or s (foldExpr env decl l) (foldExpr env decl r)
  | .cast s e t =>
    match constVal env decl (.cast s e t) with
    | some v => (litOf s v).getD (.cast s (foldExpr env decl e) t)
    | none => .cast s (foldExpr env decl e) t
  | .hton s e => .hton s (foldExpr env decl e)
  | .ntoh s e => .ntoh s (foldExpr env decl e)
  | .read s p => .read s (foldPlace env decl p)
  | .move .. => e
  | .call s f args => .call s f (args.map (foldArg env decl))

partial def foldPlace (env : Env) (decl : Interface.KindDecl) : Place → Place
  | .field s p f => .field s (foldPlace env decl p) f
  | .index s p i => .index s (foldPlace env decl p) (foldExpr env decl i)
  | .slot s m i => .slot s m (foldExpr env decl i)
  | .deref s e => .deref s (foldExpr env decl e)
  | p => p

partial def foldArg (env : Env) (decl : Interface.KindDecl) : Arg → Arg
  | .val e => .val (foldExpr env decl e)
  | .place p => .place (foldPlace env decl p)
  | a => a

end

def foldFallible (env : Env) (decl : Interface.KindDecl) : Fallible → Fallible
  | .view s off t => .view s (foldExpr env decl off) t
  | .lookup s m k => .lookup s m (foldPlace env decl k)
  | .loadw s p => .loadw s (foldPlace env decl p)
  | .call s f args => .call s f (args.map (foldArg env decl))
  | .acquire s r f t args => .acquire s r f t (args.map (foldArg env decl))
  | .callopt s f args => .callopt s f (args.map (foldArg env decl))
  | .coerce s e t => .coerce s (foldExpr env decl e) t
  | .tail s m i => .tail s m (foldExpr env decl i)

def foldInit (env : Env) (decl : Interface.KindDecl) : Init → Init
  | .expr e => .expr (foldExpr env decl e)
  | .place p => .place (foldPlace env decl p)
  | .lit s fs => .lit s (fs.map fun f => { f with value := foldExpr env decl f.value })

/-- Whether a condition is a constant, and which branch it selects.
The names a local shadows are not constants. -/
def decided (env : Env) (decl : Interface.KindDecl) (c : Expr) : Option Bool :=
  match constVal env decl c with
  | some v => some v.truthy
  | none => none

mutual

/-- A block, with each `if` on a constant replaced by its live
branch. Locals shadow constants, so the environment tracks the
names bound so far. -/
partial def foldStmts (env : Env) (decl : Interface.KindDecl) : List Stmt → List Stmt
  | [] => []
  | s :: rest =>
    let (ss, env') := foldStmt env decl s
    ss ++ foldStmts env' decl rest

partial def foldStmt (env : Env) (decl : Interface.KindDecl) (s : Stmt) :
    List Stmt × Env :=
  let bindName (x : String) : Env :=
    env.bind { name := x, ty := .bool s.span, mutable := false, origin := .stack }
  match s with
  | .«let» sp m x ty init =>
    ([.«let» sp m x ty (foldInit env decl init)], if x == "_" then env else bindName x)
  | .assign sp p e => ([.assign sp (foldPlace env decl p) (foldExpr env decl e)], env)
  | .ite sp c t e =>
    match decided env decl c with
    | some true => (foldStmts env decl t, env)
    | some false => (foldStmts env decl e, env)
    | none => ([.ite sp (foldExpr env decl c) (foldStmts env decl t) (foldStmts env decl e)], env)
  | .loop sp n body => ([.loop sp (foldExpr env decl n) (foldStmts env decl body)], env)
  | .«for» sp x lo hi body =>
    ([.«for» sp x (foldExpr env decl lo) (foldExpr env decl hi)
        (foldStmts (bindName x) decl body)], env)
  | .ret sp (some e) => ([.ret sp (some (foldExpr env decl e))], env)
  | .raise sp k e => ([.raise sp k (foldExpr env decl e)], env)
  | .«try» sp x f thn els ex =>
    ([.«try» sp x (foldFallible env decl f)
        (foldStmts (if x == "_" then env else bindName x) decl thn)
        (foldStmts env decl els) ex], env)
  | .hold sp r x acq body els =>
    ([.hold sp r x (foldFallible env decl acq)
        (foldStmts (match x with | some x => bindName x | none => env) decl body)
        (els.map (foldStmts env decl))], env)
  | .atomic sp x op p args =>
    ([.atomic sp x op (foldPlace env decl p) (args.map (foldExpr env decl))],
     match x with | some n => bindName n | none => env)
  | s => ([s], env)

end

/-- A function's body folded; a function has no kind, so the verdict
names do not occur in it and any declaration serves. -/
def foldFn (env : Env) (decl : Interface.KindDecl) (f : Fn) : Fn :=
  let env := f.params.foldl (fun env p =>
    env.bind { name := p.name, ty := p.ty, mutable := false, origin := .stack }) env.top
  { f with body := foldStmts env decl f.body }

def foldProgram (env : Env) (p : Program) : Program :=
  match env.interface.kind? p.kind with
  | some decl =>
    let env := { env.top with kind := some decl }
    { p with body := foldStmts env decl p.body,
             handlers := p.handlers.map fun h =>
               { h with body := foldStmts (env.bind { name := "reason", ty := Interface.tU32,
                                                       mutable := false, origin := .stack })
                                  decl h.body } }
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
  let decl := pre.kinds.head?.getD default
  { unit := { u with fns := u.fns.map (foldFn env decl),
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
