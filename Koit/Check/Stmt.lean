import Koit.Check.Expr

/-!
The statement rules: bindings, assignment, branches, loops, exits,
`raise`, `try`, `hold`, and atomic updates, with the shape rules of
failure handling, and the facts `F` carried through them. A block is
checked with the facts on entry in `K` and yields the facts on exit:
a branch condition enters its branch and its negation the other, a
marked load, a coercion, a `check`, and a view carve add what they
established, a loop head keeps what its body cannot change, a store
records what was stored after dropping what it may have changed, a
call drops every fact about shared places, and two paths meet with
what both know. The demands here are the field predicate at a store
and in a struct literal, the refinement of a local at its binding and
at every store to it, and `return` against a refined result or the
verdict set. No held sets or effects yet; those premises come with
effects, and the comments name each rule they will complete.
Declarations and programs are in `Decl.lean`.
-/

namespace Koit.Check

open Koit (Span)
open Koit.Core
open Koit.Interface (tU32 tU64 AcqArg)
open Koit.Facts (Origin Facts Fact Scope)
open Koit.Effects (Eff Effs Conflict Held HeldEntry)

/-- Whether a block ends in an exit: its
last statement exits on every path through it. -/
partial def exits : List Stmt → Bool
  | [] => false
  | ss =>
    match ss.getLast! with
    | .ret .. | .raise .. | .brk .. | .cont .. => true
    | .ite _ _ t e => exits t && exits e
    | .«try» _ _ _ t e _ => exits t && exits e
    | .hold _ _ _ _ body els => exits body && (els.map exits).getD true
    | _ => false

def exitForms : String := "a verdict, `fail`, `return`, `break`, or `continue`"

/-- The struct type a literal has:
the binding's declared type, or the one declared type with exactly
its field names in its order. -/
def structForLiteral (env : Env) (span : Span) (declared : Option Ty)
    (fields : List FieldInit) : M Ty := do
  let names := fields.map (·.name)
  match declared with
  | some t =>
    match ← env.norm t with
    | .struct .. => return t
    | _ =>
      err span s!"a struct literal has a struct type; `{t.print}` is not one \
       "
  | none =>
    let mut found : List TypeDecl := []
    for d in env.types ++ env.interface.types do
      match ← env.norm d.ty with
      | .struct _ fs =>
        if fs.map (·.name) == names then found := found ++ [d]
      | _ => pure ()
    match found with
    | [d] => return .named span d.name
    | [] =>
      err span s!"no declared struct type has the fields \
        `{", ".intercalate names}`; annotate the binding with the type \
       "
    | ds =>
      err span s!"the fields `{", ".intercalate names}` belong to several \
        declared types ({", ".intercalate (ds.map (·.name))}); annotate the \
        binding with the type"

/-! ### Facts from the environment and from calls -/

/-- The refinement of every refined local in scope, as facts: a
refined local's predicate holds wherever the local is, since every
store to it is checked against it. -/
def refinementFacts (env : Env) : List Fact :=
  env.locals.filterMap fun l =>
    match l.ty with
    | .refined _ v _ pred => some (.pred (pred.subst v (.var l.ty.span l.name)))
    | _ => none

/-- Whether a call may write shared state: a function of the unit, or
a interface call with the `call` effect. -/
def callKills (env : Env) (f : String) : Bool :=
  if (env.fn? f).isSome then true
  else match env.interface.call? f with
    | some decl => decl.effects.any fun
      | .call => true
      | _ => false
    | none => false

mutual

/-- The calls inside an expression, with their arguments. -/
partial def callsInExpr : Expr → List (String × List Arg)
  | .call _ f args => (f, args) :: callsInArgs args
  | .arith _ _ l r | .cmp _ _ l r | .and _ l r | .or _ l r =>
    callsInExpr l ++ callsInExpr r
  | .not _ e | .cast _ e _ | .hton _ e | .ntoh _ e => callsInExpr e
  | .read _ p => callsInPlace p
  | _ => []

partial def callsInPlace : Place → List (String × List Arg)
  | .field _ p _ => callsInPlace p
  | .index _ p i => callsInPlace p ++ callsInExpr i
  | .slot _ _ i => callsInExpr i
  | .deref _ e => callsInExpr e
  | _ => []

partial def callsInArgs (args : List Arg) : List (String × List Arg) :=
  args.flatMap fun
    | .val e => callsInExpr e
    | .place p => callsInPlace p
    | .map .. => []

end

def callsInFallible : Fallible → List (String × List Arg)
  | .view _ off _ => callsInExpr off
  | .lookup _ _ k => callsInPlace k
  | .loadw _ p => callsInPlace p
  | .call _ f args | .callopt _ f args => (f, args) :: callsInArgs args
  | .tail _ _ i => callsInExpr i
  | .acquire _ _ f _ args => (f, args) :: callsInArgs args
  | .coerce _ e _ => callsInExpr e

/-- The facts after the calls in a statement: a call that may write
shared state drops every fact about a shared place, and any place
passed to a call may have been written. -/
def afterCalls (env : Env) (sc : Scope) (F : Facts)
    (calls : List (String × List Arg)) : Facts :=
  calls.foldl (fun F (f, args) =>
    let F := if callKills env f then F.killShared sc else F
    args.foldl (fun F a => match a with
      | .place p => F.kill sc p
      | _ => F) F) F

mutual

/-- The places a block may write: assignment and atomic targets, and
every place passed to a call, through nested blocks. -/
partial def assignedIn (ss : List Stmt) : List Place :=
  ss.flatMap fun
    | .«let» _ _ _ _ (.expr e) => placeArgs (callsInExpr e)
    | .«let» _ _ _ _ (.place p) => placeArgs (callsInPlace p)
    | .«let» _ _ _ _ (.lit _ fs) =>
      placeArgs (fs.flatMap fun f => callsInExpr f.value)
    | .assign _ p e => p :: placeArgs (callsInPlace p ++ callsInExpr e)
    | .ite _ c t e => placeArgs (callsInExpr c) ++ assignedIn t ++ assignedIn e
    | .loop _ _ b => assignedIn b
    | .«for» _ _ lo hi b =>
      placeArgs (callsInExpr lo ++ callsInExpr hi) ++ assignedIn b
    | .ret _ (some e) | .raise _ _ e => placeArgs (callsInExpr e)
    | .«try» _ _ f t e _ =>
      placeArgs (callsInFallible f) ++ assignedIn t ++ assignedIn e
    | .hold _ _ _ acq b e =>
      placeArgs (callsInFallible acq) ++ assignedIn b ++
        (e.map assignedIn).getD []
    | .atomic _ _ _ p args => p :: placeArgs (args.flatMap callsInExpr)
    | _ => []

partial def placeArgs (calls : List (String × List Arg)) : List Place :=
  calls.flatMap fun (_, args) => args.filterMap fun
    | .place p => some p
    | _ => none

end

/-! ### What a statement mentions -/

/-- The arguments of a call as expressions, a place read. -/
def argExprs (args : List Arg) : List Expr :=
  args.filterMap fun
    | .val e => some e
    | .place p => some (.read p.span p)
    | .map .. => none

/-- The operands of a fallible operation. -/
def fallibleExprs : Fallible → List Expr
  | .view _ off _ => [off]
  | .lookup _ _ k => [.read k.span k]
  | .loadw _ p => [.read p.span p]
  | .coerce _ e _ => [e]
  | .call _ _ args | .callopt _ _ args | .acquire _ _ _ _ args => argExprs args
  | .tail _ _ i => [i]

/-- The expressions a statement evaluates itself, apart from its
blocks. -/
def ownExprs : Stmt → List Expr
  | .«let» _ _ _ _ (.expr e) => [e]
  | .«let» _ _ _ _ (.place p) => [.read p.span p]
  | .«let» _ _ _ _ (.lit _ fs) => fs.map (·.value)
  | .assign _ p e => [.read p.span p, e]
  | .ite _ c .. => [c]
  | .loop _ n _ => [n]
  | .«for» _ _ lo hi _ => [lo, hi]
  | .ret _ (some e) => [e]
  | .raise _ _ r => [r]
  | .«try» _ _ f .. => fallibleExprs f
  | .hold _ _ _ f .. => fallibleExprs f
  | .atomic _ _ _ p args => .read p.span p :: args
  | _ => []

mutual

/-- The names an expression mentions, with their positions, through
calls; with `movesOnly`, the names it moves. -/
partial def namesInExpr (movesOnly : Bool) : Expr → List (Span × String)
  | .var s x => if movesOnly then [] else [(s, x)]
  | .move s x => [(s, x)]
  | .arith _ _ l r | .cmp _ _ l r | .and _ l r | .or _ l r =>
    namesInExpr movesOnly l ++ namesInExpr movesOnly r
  | .not _ e | .cast _ e _ | .hton _ e | .ntoh _ e => namesInExpr movesOnly e
  | .read _ p => namesInPlace movesOnly p
  | .call _ _ args => args.flatMap fun
    | .val e => namesInExpr movesOnly e
    | .place p => namesInPlace movesOnly p
    | .map .. => []
  | _ => []

partial def namesInPlace (movesOnly : Bool) : Place → List (Span × String)
  | .var s x => if movesOnly then [] else [(s, x)]
  | .field _ p _ => namesInPlace movesOnly p
  | .index _ p i => namesInPlace movesOnly p ++ namesInExpr movesOnly i
  | .slot _ _ i => namesInExpr movesOnly i
  | .deref _ e => namesInExpr movesOnly e
  | .invalid .. => []

end

/-! ### Guards -/

/-- Whether a call has the `resize` effect: a interface declaration that says
so, or a function of the unit whose summary has it. -/
def resizes (env : Env) (f : String) : Bool :=
  match env.interface.call? f with
  | some decl => (Effs.ofCore decl.effects).has .resize
  | none => ((env.fnEffects.lookup f).map (·.has .resize)).getD false

/-- The call as the programmer names it: `adjust_head` for the
interface's `pkt.adjust_head`. -/
def callSpelling (f : String) : String :=
  if f.startsWith "pkt." then (f.drop 4).toString else f

/-- The calls a statement makes itself, apart from its blocks: the
fallible operation of a `try` or `hold`, and the calls in its
expressions. -/
def ownCalls : Stmt → List (String × List Arg)
  | .«try» _ _ f .. | .hold _ _ _ f .. => callsInFallible f
  | s => (ownExprs s).flatMap callsInExpr

/-- The first resizing call among a statement's own calls, with where
it is. -/
def resizerOf (env : Env) (s : Stmt) : Option (Span × String) :=
  (ownCalls s).findSome? fun (f, _) =>
    if resizes env f then some (s.span, callSpelling f) else none

/-- The first resizing call in a block, at any depth. -/
partial def resizeIn (env : Env) (ss : List Stmt) : Option (Span × String) :=
  ss.findSome? fun s =>
    resizerOf env s <|>
    match s with
    | .ite _ _ t e => resizeIn env t <|> resizeIn env e
    | .loop _ _ b | .«for» _ _ _ _ b => resizeIn env b
    | .«try» _ _ _ t e _ => resizeIn env t <|> resizeIn env e
    | .hold _ _ _ _ b e => resizeIn env b <|> (e.bind (resizeIn env))
    | _ => none

/-- The views in scope: the locals of a `view` type. -/
def viewsInScope (env : Env) : List String :=
  env.locals.filterMap fun l => match l.ty with
    | .view .. => some l.name
    | _ => none

/-- The context a statement is checked in, for its guards: a mention
of a view whose token was dropped is an error at the use, naming the
statement that dropped it; then, if the statement itself resizes the
packet, every view in scope is dead for its blocks and after it. -/
def guardCtx (env : Env) (K : Ctx) (s : Stmt) : M Ctx := do
  for (sp, x) in (ownExprs s).flatMap (namesInExpr false) do
    if let some (at_, f) := K.facts.dead? x then
      err sp s!"view `{x}` was invalidated by `{f}` at line {at_.start.line}; \
        carve it again after the resize"
  match resizerOf env s with
  | some (sp, f) =>
    return { K with facts := K.facts.killViews (viewsInScope env) sp f }
  | none => return K


/-- The increments `x += e` of a block outside its nested loops, each
with its target and its addend. -/
partial def increments : List Stmt → List (String × Expr)
  | [] => []
  | s :: rest =>
    (match s with
     | .assign _ (.var _ x) (.arith _ .add (.read _ (.var _ y)) e) =>
       if x == y then [(x, e)] else []
     | .ite _ _ t e => increments t ++ increments e
     | .«try» _ _ _ t e _ => increments t ++ increments e
     | .hold _ _ _ _ b e => increments b ++ (e.map increments).getD []
     | _ => []) ++ increments rest

/-- The bounds a loop of at most `iters` iterations keeps on an
unsigned stack local that its body changes only by `x += e`, each
increment outside the nested loops and each addend bounded above in
the state before the loop by a value the body does not change: the
local starts below its bound and gains at most the sum of the
addends' bounds per iteration, so, when the total stays within the
type, it never wraps and never exceeds the start plus `iters` times
that sum. The verifier re-derives the same bound by walking the
loop to its count, so the fact is one it will see. -/
def incrementBounds (sc : Scope) (F : Facts) (body : List Stmt)
    (iters : Nat) : List Fact :=
  let st := F.state sc
  let assigned := assignedIn body
  let incs := increments body
  let targets := (incs.map (·.1)).eraseDups
  targets.flatMap fun x =>
    let p : Place := .var Koit.Facts.noSpan x
    let mine := incs.filter (·.1 == x)
    -- every assignment to `x` in the body is one of its increments
    if (assigned.filter fun q => q.root == some x).length != mine.length
    then [] else
    match sc.place p, Koit.Facts.lookup sc st p with
    | some (.stack, .int false w), .int a =>
      let ubs := mine.map fun (_, e) =>
        if e.atoms.any (fun q => assigned.any (Koit.Facts.overlaps sc q ·))
        then none else
        match Koit.Facts.eval sc st e with
        | .int b => if !b.isEmpty && b.lo ≥ 0 then some b.hi else none
        | .poly v => if v ≥ 0 then some v else none
        | _ => none
      if ubs.any (·.isNone) || a.isEmpty then [] else
      let hi := a.hi + iters * (ubs.filterMap id).foldl (· + ·) 0
      if hi > Koit.Facts.typeHi false w then [] else
      Facts.factsOf sc p
        (.int (Koit.Facts.Abs.reduce { Koit.Facts.Abs.top false w with
                                         lo := a.lo, hi }))
    | _, _ => []

/-- The facts at a loop head: what the body may write is dropped,
with every shared place, the refinements in scope hold again, and a
local the body only increments keeps the bound of `incrementBounds`
when the loop's iteration count `iters` is known; if the body resizes
the packet, every view in scope is dead. -/
def loopHead (env : Env) (sc : Scope) (F : Facts) (body : List Stmt)
    (iters : Option Nat) : Facts :=
  let F' := (refinementFacts env).foldl Facts.add (F.inv sc (assignedIn body))
  let F' := match iters with
    | some n => (incrementBounds sc F body n).foldl Facts.add F'
    | none => F'
  match resizeIn env body with
  | some (sp, f) => F'.killViews (viewsInScope env) sp f
  | none => F'

/-- The iteration count of `repeat n`, when `n` is constant. -/
def loopIters (env : Env) (n : Expr) : Option Nat :=
  (env.evalConst n).map (·.toNat)

/-! ### Bindings -/

/-- A binding: the local it introduces and the facts after it. -/
def bindInit (env : Env) (K : Ctx) (span : Span) (mutable : Bool) (x : String)
    (ty : Option Ty) (init : Init) : M (Local × Facts) := do
  let sc := scope env K
  let F := K.facts.dropNames [x]
  match init with
  | .expr e =>
    let t ← match ty with
      | some t =>
        -- a declared refinement is demanded of the initializer
        match ← env.refinement? t with
        | some (v, base, pred) =>
          check env K e base
          demand env K span s!"`{x}: {t.print}`" (pred.subst v e)
        | none => check env K e t
        pure t
      | none => synth env K e
    let tn ← env.norm t
    unless tn.isScalar do
      err span s!"`{x}` would be a `{t.print}`; a binding whose right side is \
        not a place takes a scalar (P3)"
    let l : Local := { name := x, ty := t, mutable, origin := .stack }
    let F := afterCalls env sc F (callsInExpr e)
    -- the binding's equation, in the scope that has the name, and the
    -- refinement now in force
    let sc := scope (env.bind l) K
    let F := F.record sc (.var span x) e
    let F := match ← env.refinement? t with
      | some (v, _, pred) => F.add (.pred (pred.subst v (.var span x)))
      | none => F
    -- a function's postcondition is a fact at the call site, with its
    -- parameters replaced by the value arguments
    let F ← match e with
      | .call _ f args =>
        match env.fn? f with
        | some d =>
          match ← env.refinement? (d.ret.getD (.bool span)) with
          | some (r, _, pred) =>
            let P := (d.params.zip args).foldl (fun P (p, a) => match a with
              | .val v => P.subst p.name v
              | .place q => P.subst p.name (.read q.span q)
              | .map .. => P) pred
            pure (F.assume sc (P.subst r (.var span x)))
          | none => pure F
        | none => pure F
      | _ => pure F
    return (l, F)
  | .place p =>
    let info ← placeTyUse env K p
    let tn ← env.norm info.ty
    -- (Read): a scalar place is read into the name, at its base type;
    -- a declared refinement is demanded of the value read
    if tn.isScalar then
      let t ← match ty with
        | some t =>
          unless ← env.eqv t tn do mismatch env p.span t info.ty
          if let some (v, _, pred) ← env.refinement? t then
            demand env K span s!"`{x}: {t.print}`"
              (pred.subst v (.read p.span p))
          pure t
        | none => pure tn
      let l : Local := { name := x, ty := t, mutable, origin := .stack }
      let F := F.record (scope (env.bind l) K) (.var span x) (.read p.span p)
      let F := match ← env.refinement? t with
        | some (v, _, pred) => F.add (.pred (pred.subst v (.var span x)))
        | none => F
      return (l, F)
    match tn with
    | .slot _ n =>
      err span s!"a `{n}` is a slot: it is not bound; it is named by \
        {env.slotUse n}"
    | _ => pure ()
    -- (P3): an aggregate place is named
    if mutable then
      err span "`var` binds a scalar; an aggregate place is named with `let` \
       "
    if let some t := ty then
      unless ← env.eqv t info.ty do mismatch env p.span t info.ty
    let pty := if info.origin == .pkt then Ty.view span info.ty
      else Ty.ref span info.ty
    let F := F.alias x (F.resolve p)
    return ({ name := x, ty := pty, mutable := false, origin := info.origin },
            F)
  | .lit ls fields =>
    if mutable then
      err span "`var` binds a scalar; a struct literal is a place, named with \
        `let`"
    let st ← structForLiteral env ls ty fields
    let fs ← match ← env.norm st with
      | .struct _ fs => pure fs
      | _ => err ls "a struct literal has a struct type"
    unless fs.map (·.name) == fields.map (·.name) do
      err ls s!"a struct literal gives every field of `{st.print}` in order: \
        {", ".intercalate (fs.map (·.name))}"
    let mut F := F
    for (fd, fi) in fs.zip fields do
      let ftn ← env.norm fd.ty
      unless ftn.isScalar do
        err fi.span s!"field `{fd.name}` of `{st.print}` is a `{fd.ty.print}`; \
          struct literals have scalar fields only"
      check env K fi.value fd.ty
      -- the field's predicate, with every sibling its initializer
      if let some pred := fd.pred then
        let P := fields.foldl (fun P g => P.subst g.name g.value) pred
        demand env K fi.span s!"the field `{fd.name}` of the literal" P
      F := afterCalls env sc F (callsInExpr fi.value)
    -- the literal's own place holds what was written into it
    let l : Local := { name := x, ty := .ref span st, mutable := false,
                       origin := .stack }
    let sc := scope (env.bind l) K
    for fi in fields do
      F := F.record sc (.field fi.span (.var span x) fi.name) fi.value
    return (l, F)

/-- `return` against what the context returns to: the type, then the
verdict set or the refined result as a demand. -/
def checkRet (env : Env) (K : Ctx) (span : Span) (v : Option Expr) :
    M Unit := do
  let sc := scope env K
  match K.ret, v with
  | .program ty, some e | .handler ty, some e =>
    check env K e ty
    match K.verdictSet with
    | some vset =>
      let decl := env.kind.get!
      let vals := vset.filterMap fun n => (decl.verdicts.lookup n).map Int.ofNat
      let setText := "{" ++ ", ".intercalate vset ++ "}"
      unless Koit.Facts.entailsIn sc K.facts e vals do
        -- a value the facts pin down is named
        match Koit.Facts.constOf sc K.facts e with
        | some c =>
          match decl.verdicts.find? (·.2 == c.toNat) with
          | some (n, _) =>
            err e.span s!"`{n}` is not in the verdict set {setText}"
          | none => err e.span s!"the verdict {c} is not in the verdict set \
              {setText}"
        | none =>
          let P := vset.foldl (fun P n =>
            let eq := Expr.cmp e.span .eq e (.var e.span n)
            match P with
            | some P => some (Expr.or e.span P eq)
            | none => some eq) none
          err e.span (demandMsg "the return under the verdict set" P.get!)
    | none => pure ()
  | .program _, none | .handler _, none =>
    err span "a program returns a verdict"
  | .fn _ none, none => pure ()
  | .fn f none, some _ => err span s!"`{f}` returns nothing"
  -- absence from a function returning `T?`
  | .fn _ (some (.opt ..)), none => pure ()
  | .fn f (some (.opt _ t)), some e => retValue f e t
  | .fn f (some t), none =>
    err span s!"`return` needs a value: `{f}` returns `{t.print}`"
  | .fn f (some t), some e => retValue f e t
where
  /-- A function's result: the base type, then the postcondition. -/
  retValue (f : String) (e : Expr) (t : Ty) : M Unit := do
    match ← env.refinement? t with
    | some (r, base, pred) =>
      check env K e base
      demand env K e.span s!"the result of `{f}`" (pred.subst r e)
    | none => check env K e t

/-- Whether a head-normal integer type has a width the atomic
instructions exist at. -/
def atomicWidth : Ty → Bool
  | .int _ _ w => w == 32 || w == 64
  | _ => false

/-- The acquiring function of a `hold`, for messages. -/
def acqName : Fallible → String
  | .acquire _ _ f .. => f
  | f => f.print

/-- The acquisition as the programmer wrote it after `hold`:
`lock(c.lk)`, `rcu`, `sk_lookup_tcp(t)`. -/
def acqSpelling : Fallible → String
  | .acquire _ _ f ty args =>
    let targ := match ty with
      | some t => "<" ++ t.print ++ ">"
      | none => ""
    if args.isEmpty && ty.isNone then f
    else f ++ targ ++ "(" ++ Arg.printList args ++ ")"
  | f => f.print

/-- The facts a fallible operation establishes in its then-branch for
the name it binds, and in its else-branch. -/
def fallibleFacts (env : Env) (K : Ctx) (x : String) (f : Fallible)
    (b : Bound) : M (Facts × Facts) := do
  let sc := scope env K
  let F := afterCalls env sc K.facts (callsInFallible f)
  match f with
  | .view _ off _ =>
    -- the view's offset, for the write effects
    return (F.add (.off x (F.resolveExpr off)), F)
  | .loadw s (.field _ q fname) =>
    -- the field's predicate holds of the value loaded, with every
    -- sibling read from the place
    match b.ty with
    | some (.refined _ _ _ pred) =>
      let info ← placeTy env K q
      let sibs ← match ← env.norm info.ty with
        | .struct _ fs => pure (fs.map (·.name))
        | _ => pure []
      let P := sibs.foldl (fun P g =>
        if g == fname then P else P.subst g (.read s (.field s q g))) pred
      let P := P.subst fname (.var s x)
      return (F.assume sc P, F)
    | _ => return (F, F)
  | .coerce s e (.refined _ v _ pred) =>
    -- `check P` is the coercion of `P` to `{b: bool | b}` bound to `_`:
    -- the fact is `P` itself, and its negation on the other path
    match x, pred with
    | "_", .var _ b' =>
      if b' == v then return (F.assume sc e, F.assume sc (Facts.negate e))
      else return (F, F)
    | _, _ => return (F.assume sc (pred.subst v (.var s x)), F)
  | .call s _ _ | .callopt s _ _ | .acquire s .. =>
    -- a refined result, such as `redirect`'s
    match b.ty with
    | some t =>
      match ← env.refinement? t with
      | some (v, _, pred) => return (F.assume sc (pred.subst v (.var s x)), F)
      | none => return (F, F)
    | none => return (F, F)
  | _ => return (F, F)

/-- The facts after `F1` then, on another path, `F2`. -/
def meetK (env : Env) (K : Ctx) (F1 F2 : Facts) : Facts :=
  Facts.meet (scope env K) F1 F2


/-! ### Ownership -/

/-- The context a statement is checked in: a mention of a name moved
on this path is an error, since the name is dead after its `move`;
then the statement's own moves are recorded, each name once, before
its blocks are checked. -/
def moveCtx (K : Ctx) (s : Stmt) : M Ctx := do
  let es := ownExprs s
  for (sp, x) in es.flatMap (namesInExpr false) do
    if let some m := K.facts.moved? x then
      err sp s!"`{x}` was moved at line {m.start.line} and is dead after it \
       "
  let mut F := K.facts
  for (sp, x) in es.flatMap (namesInExpr true) do
    if (F.moved? x).isSome then
      err sp s!"`{x}` is moved twice in one statement"
    F := F.addMoved x sp
  return { K with facts := F }

/-- Where two live paths meet, each owned name is moved on both or on
neither, so that the scope's release is unconditional. -/
def joinMoved (span : Span) (F1 F2 : Facts) : M Unit := do
  if F1.bottom || F2.bottom then return
  let only (F G : Facts) : Option (String × Span) :=
    F.moved.find? fun (x, _) => (G.moved? x).isNone
  if let some (x, m) := only F1 F2 <|> only F2 F1 then
    err span s!"`{x}` moved on one branch and held on the other at this join \
      (`move {x}` at line {m.start.line}): move it on both paths, or after \
      the join"

/-- A path back to a loop's head, at `continue` or the end of the
body, or out of it at `break`, holds what was held at the head:
a name bound outside the loop is moved inside it only on a path that
leaves the program or function. -/
def loopMovedOk (K : Ctx) (span : Span) (F : Facts) (next : String) :
    M Unit := do
  if F.bottom then return
  if let some (x, m) := F.moved.find? fun (x, _) => !K.loopMoved.contains x then
    err span s!"`{x}` moved inside the loop (`move {x}` at line \
      {m.start.line}) and held at the loop head, so {next} would find it \
      moved: move it on a path that leaves the program, or after the loop"

/-! ### The fact transformers of the statement rules, shared with the
judgment of `Rules.lean` so that the two cannot drift apart. -/

/-- The named interface type the place's root name refers to, when
that type is read-only: `tp.snd_cwnd` under `tp : ref TcpSock`. -/
def readOnlyRoot (env : Env) (p : Place) : Option String := do
  let root ← p.root
  let l ← env.local? root
  let n ← match l.ty with
    | .ref _ (.named _ n) | .own _ (.named _ n) | .view _ (.named _ n) => some n
    | _ => none
  let d ← env.type? n
  if d.readOnly then some n else none

/-- The owned names of the same allocation type as the place's root,
other than the root itself: two may own one object (a reference-count
acquisition), so a store through one kills the facts about all. -/
def ownedAliases (env : Env) (p : Place) : List String :=
  match p.root >>= env.local? with
  | some l =>
    match l.ty with
    | .own _ t =>
      env.locals.filterMap fun m =>
        match m.ty with
        | .own _ t' =>
          if m.name != l.name && t'.print == t.print then some m.name else none
        | _ => none
    | _ => []
  | none => []

/-- After `p = e`: the kills of the calls in it, the store recorded,
and a refined local's refinement in force again. -/
def assignAfter (env : Env) (K : Ctx) (p : Place) (e : Expr) : Facts :=
  let sc := scope env K
  let F := afterCalls env sc K.facts (callsInPlace p ++ callsInExpr e)
  let F := F.record sc p e
  -- a store through an owned name: the facts about every owned name
  -- of the same type go too, since two may own one object
  let F := (ownedAliases env p).foldl (fun F y => F.kill sc (.var p.span y)) F
  match p with
  | .var s x =>
    match env.local? x with
    | some l =>
      match l.ty with
      | .refined _ v _ pred => F.add (.pred (pred.subst v (.var s x)))
      | _ => F
    | none => F
  | _ => F

/-- The facts a condition's branches start from: the condition in
the one, its negation in the other. -/
def iteEntry (env : Env) (K : Ctx) (c : Expr) : Facts × Facts :=
  let sc := scope env K
  let F := afterCalls env sc K.facts (callsInExpr c)
  (F.assume sc c, F.assume sc (Facts.negate c))

/-- Whether the facts decide a condition (IfConst), and how. -/
def iteDecided (env : Env) (K : Ctx) (c : Expr) : Option Bool :=
  let sc := scope env K
  let F := afterCalls env sc K.facts (callsInExpr c)
  match Koit.Facts.eval sc (F.state sc) (F.resolveExpr c) with
  | .bool .yes => some true
  | .bool .no => some false
  | _ => none

/-- After a conditional: what the two branches meet at, or the live
branch alone when the facts decide the condition (IfConst). -/
def iteAfter (env : Env) (K : Ctx) (c : Expr) (Ft Fe : Facts) : Facts :=
  match iteDecided env K c with
  | some true => { Ft with caps := Ft.caps ++ Fe.caps }
  | some false => { Fe with caps := Ft.caps ++ Fe.caps }
  | none => meetK env K Ft Fe

/-- The cap of `for i in lo..hi`: the bound's largest value under the
facts, or the top of its type. -/
def forCap (env : Env) (K : Ctx) (hi : Expr) : Nat :=
  match Koit.Facts.upperOf (scope env K) K.facts hi with
  | some v => v.toNat
  | none => 2 ^ 64 - 1

/-- The index local of a `for` loop. -/
def forLocal (s : Span) (x : String) : Local :=
  { name := x, ty := .int s false 64, mutable := false, origin := .stack }

/-- The facts a `for` body starts from: the loop head's, with the
cap recorded and `lo <= i < hi`. -/
def forEntry (env : Env) (K : Ctx) (s : Span) (x : String) (lo hi : Expr)
    (body : List Stmt) : Facts :=
  let cap := forCap env K hi
  let Fh := loopHead env (scope env K) K.facts body (some cap)
  let Fh := { Fh with caps := Fh.caps ++ [(s, cap)] }
  let sc' := scope (env.bind (forLocal s x)) K
  (Fh.assume sc' (.cmp s .le lo (.var s x))).assume sc'
    (.cmp s .lt (.var s x) hi)

/-- The join of a conditional's branches, unless the facts decide the
condition and one branch is dead. -/
def iteJoin (env : Env) (K : Ctx) (span : Span) (c : Expr) (Ft Fe : Facts) :
    M Unit := do
  if (iteDecided env K c).isNone then joinMoved span Ft Fe

/-- The context of a loop body: inside a loop, from the facts `F`,
with what is moved at the head recorded. -/
def loopCtx (K : Ctx) (F : Facts) : Ctx :=
  { K with inLoop := true, loopMoved := K.facts.moved.map (·.1), facts := F }

/-- After a loop: the head's facts, with the caps the body gathered. -/
def loopAfter (env : Env) (K : Ctx) (body : List Stmt) (Fb : Facts)
    (iters : Option Nat) : Facts :=
  { loopHead env (scope env K) K.facts body iters with caps := Fb.caps }

/-- The facts a `hold` body starts from: the acquisition's kills when
it is a kernel call. -/
def holdEntry (env : Env) (K : Ctx) (isCall : Bool) (acq : Fallible) : Facts :=
  if isCall then afterCalls env (scope env K) K.facts (callsInFallible acq)
  else K.facts

/-- The context of a `hold` body: the acquisition's facts, and the
resource pushed onto the held set with the name it binds. -/
def holdCtx (env : Env) (K : Ctx) (span : Span) (decl : Interface.ResourceDecl)
    (x : Option String) (acq : Fallible) : Ctx :=
  { K with facts := holdEntry env K (decl.arg == .call) acq,
           held := { decl, name := x, what := acqSpelling acq, span } :: K.held }

/-- After an atomic update on `p`: the place's facts go. -/
def atomicAfter (env : Env) (K : Ctx) (p : Place) (args : List Expr)
    (x : Option String) : Facts :=
  let sc := scope env K
  let F := (afterCalls env sc K.facts (args.flatMap callsInExpr)).kill sc p
  match x with
  | some n => F.dropNames [n]
  | none => F


/-! ### Effects -/

/-- The calls in an initializer. -/
def callsInInit : Init → List (String × List Arg)
  | .expr e => callsInExpr e
  | .place p => callsInPlace p
  | .lit _ fs => fs.flatMap fun f => callsInExpr f.value

/-- A literal expression for a byte count. -/
def litNat (s : Span) (n : Nat) : Expr := .lit s n (toString n)

/-- `e + n`, folded when `e` is a literal, and `e` when `n` is zero. -/
def plusNat (e : Expr) (n : Nat) : Expr :=
  match e with
  | .lit s v _ => litNat s (v + n)
  | _ => if n == 0 then e else .arith e.span .add e (litNat e.span n)

/-- The byte offset of field `f` in a struct type; `none` when the type
has no such field. -/
def fieldOffset (env : Env) (t : Ty) (f : String) : M (Option Nat) := do
  match ← env.norm t with
  | .struct _ fields =>
    let mut off := 0
    for fd in fields do
      let (sz, al) ← env.layout fd.ty
      off := (off + al - 1) / al * al
      if fd.name == f then return some off
      off := off + sz
    return none
  | _ => return none

/-- The name a place is reached through and the constant byte offset
of the place within it, through fields and literal indexes; the
offset is `none` when an index is not a literal. -/
partial def placeOffset (env : Env) (K : Ctx) (p : Place) :
    M (Option (String × Option Nat)) := do
  match p with
  | .var _ x | .deref _ (.var _ x) => return some (x, some 0)
  | .field _ q f =>
    match ← placeOffset env K q with
    | some (x, some k) =>
      let info ← placeTy env K q
      match ← fieldOffset env info.ty f with
      | some o => return some (x, some (k + o))
      | none => return some (x, none)
    | r => return r
  | .index _ q i =>
    match ← placeOffset env K q with
    | some (x, some k) =>
      let info ← placeTy env K q
      match ← env.norm info.ty with
      | .array _ elem _ =>
        let (sz, _) ← env.layout elem
        match env.evalConst i with
        | some v => return some (x, some (k + sz * v.toNat))
        | none => return some (x, none)
      | _ => return some (x, none)
    | r => return r
  | _ => return none

/-- The view parameters of the function under check. -/
def viewParams (env : Env) (K : Ctx) : List String :=
  match K.fnName.bind env.fn? with
  | some d => d.params.filterMap fun p => match p.ty with
    | .view .. => some p.name
    | _ => none
  | none => []

/-- The packet write of a store to the bytes `[lo, hi)` of the place
`q`, which lies in the packet: the range from the view's offset, when
the facts have it; the range relative to the view parameter, inside a
function; the whole packet otherwise. A store at an offset that is
not constant, an element at a variable index, is the view's whole
extent. -/
def pktWrite (env : Env) (K : Ctx) (q : Place) (lo hi : Nat) : M Eff := do
  let q := K.facts.resolve q
  let some (h, k?) ← placeOffset env K q | return .pktAll
  let some l := env.local? h | return .pktAll
  let vsz ← match l.ty with
    | .view _ vt => (env.layout vt).map (·.1)
    | _ => return .pktAll
  let (rlo, rhi) := match k? with
    | some k => (k + lo, k + hi)
    | none => (0, vsz)
  match K.facts.offsetOf h with
  | some o =>
    -- a constant offset, `EthHdr.size`, is folded to its bytes
    let o := match env.evalConst o with
      | some v => litNat o.span v.toNat
      | none => o
    return .pkt (plusNat o rlo) (plusNat o rhi)
  | none =>
    if (viewParams env K).contains h then return .viaView h rlo rhi
    else return .pktAll

/-- The write effect of a store to `p`: the map it lies in, the
context field, the packet range through its view, or the parameter it
is reached through inside a function; nothing for the stack. -/
def writesOf (env : Env) (K : Ctx) (p : Place) : M Effs := do
  let info ← placeTy env K p
  match info.origin with
  | .stack | .kernel => return {}
  | .map m => return Effs.ofList [.map m]
  | .ctx =>
    match p with
    | .field _ _ f => return Effs.ofList [.ctx f]
    | _ => return {}
  | .param =>
    match ← placeOffset env K (K.facts.resolve p) with
    | some (x, _) => return Effs.ofList [.viaRef x]
    | none => return {}
  | .pkt =>
    let (sz, _) ← env.layout info.ty
    return Effs.ofList [← pktWrite env K p 0 sz]

/-- The effects of a call: a function of the unit contributes its
summary instantiated on the arguments, the writes through its `ref`
and `view` parameters becoming writes to what was passed; a interface
call contributes its declaration, with the writes of `copy`, `fill`,
`insert`, and `delete` from their place or map argument. -/
def callEffects (env : Env) (K : Ctx) (f : String) (args : List Arg) :
    M Effs := do
  if let some d := env.fn? f then
    let E := (env.fnEffects.lookup f).getD {}
    let argOf (x : String) : Option Arg :=
      ((d.params.zip args).find? (·.1.name == x)).map (·.2)
    let mut R : Effs := {}
    for e in E.effs do
      match e with
      | .viaRef x =>
        if let some (.place q) := argOf x then
          R := R.union (← writesOf env K q)
      | .viaView h lo hi =>
        if let some (.place q) := argOf h then
          R := R.add (← pktWrite env K q lo hi)
      | e => R := R.add e
    return R
  match env.interface.call? f with
  | some decl =>
    let mut R := (Effs.ofCore decl.effects decl.lockSafe).addAll
      (decl.requires.map fun r => .needs r.name)
    match f, args with
    | "copy", .place dst :: _ | "fill", .place dst :: _ =>
      R := R.union (← writesOf env K dst)
    | "insert", .map _ m :: _ | "delete", .map _ m :: _ =>
      R := R.add (.map m)
    | _, _ => pure ()
    return R
  | none =>
    -- an acquisition by scope or by a place, `rcu` or `lock(p)`, is
    -- the call of the kernel function behind its declaration
    match env.interface.resources.find? fun d =>
        d.arg != .call && d.acquirers.contains f with
    | some d =>
      return (Effs.ofList [if d.lockSafe then .callSafe else .call]).addAll
        (d.requires.map fun r => .needs r.name)
    | none => return {}

def effectsOfCalls (env : Env) (K : Ctx) (calls : List (String × List Arg)) :
    M Effs := do
  let mut R : Effs := {}
  for (f, args) in calls do
    R := R.union (← callEffects env K f args)
  return R

/-- The effects of a fallible operation: the calls in its operands,
and the call itself for a helper, a `T?` function, or an acquiring
kernel function. -/
def fallibleEffects (env : Env) (K : Ctx) : Fallible → M Effs
  | .view _ off _ => effectsOfCalls env K (callsInExpr off)
  | .lookup _ _ k => effectsOfCalls env K (callsInPlace k)
  | .loadw _ p => effectsOfCalls env K (callsInPlace p)
  | .coerce _ e _ => effectsOfCalls env K (callsInExpr e)
  | .call _ f args | .callopt _ f args | .acquire _ _ f _ args =>
    effectsOfCalls env K ((f, args) :: callsInArgs args)
  | .tail _ _ i => do return (← effectsOfCalls env K (callsInExpr i)).add .call

/-- The effects of a statement itself, apart from the blocks inside
it: the calls in its expressions, the write of its store, and `fail`
for a `raise`. -/
def stmtEffects (env : Env) (K : Ctx) : Stmt → M Effs
  | .«let» _ _ _ _ init => effectsOfCalls env K (callsInInit init)
  | .assign _ p e => do
    return (← writesOf env K p).union
      (← effectsOfCalls env K (callsInPlace p ++ callsInExpr e))
  | .ite _ c .. => effectsOfCalls env K (callsInExpr c)
  | .loop _ n _ => effectsOfCalls env K (callsInExpr n)
  | .«for» _ _ lo hi _ =>
    effectsOfCalls env K (callsInExpr lo ++ callsInExpr hi)
  | .ret _ (some e) => effectsOfCalls env K (callsInExpr e)
  | .raise _ _ r => do return (← effectsOfCalls env K (callsInExpr r)).add .fail
  | .«try» _ _ f .. => fallibleEffects env K f
  | .hold _ _ _ acq .. => fallibleEffects env K acq
  | .atomic _ _ _ p args => do
    return (← writesOf env K p).union
      (← effectsOfCalls env K (args.flatMap callsInExpr))
  | _ => return {}

/-- The held set against the effects of one statement: an effect a
held declaration forbids is an error at the statement, naming the resource
and the `hold` that acquired it. A sleeping call is also refused in
a program kind whose declaration does not permit it. -/
def checkHeld (env : Env) (K : Ctx) (span : Span) (E : Effs) : M Unit := do
  if let some (e, h) := K.held.forbidden E then
    err span s!"the {e.print} effect is forbidden while {h.decl.describe} is \
      held (`hold {h.what}` at line {h.span.start.line}); move it outside \
      the block"
  if E.has .sleep then
    if let some decl := env.kind then
      unless decl.sleep do
        err span s!"a sleeping call is not permitted in {article decl.name} \
          `{decl.name}` program"

/-- Whether a required resource is held. A required RCU section is
satisfied the way the kernel tests it: by an RCU section, a spin
lock, a preempt-off or IRQ-off section in the held set, or a program
kind that cannot sleep. -/
def needSatisfied (env : Env) (K : Ctx) (res : String) : Bool :=
  let heldAny (names : List String) := names.any fun n => (K.held.holds ⟨n⟩).isSome
  if res == "rcu" then
    heldAny ["rcu", "spinlock", "preempt", "irq"] ||
      (match env.kind with | some row => !row.sleep | none => false)
  else heldAny [res]

/-- The demands of a statement's calls against the held set: a demand
met here is discharged; one not met is an error in a program body,
and in a function body it stays in the effect set, a demand on the
function's callers. -/
def resolveNeeds (env : Env) (K : Ctx) (span : Span) (E : Effs) : M Effs := do
  let mut R : Effs := {}
  for e in E.effs do
    match e with
    | .needs r =>
      if needSatisfied env K r then pure ()
      else if K.fnName.isSome then R := R.add e
      else
        let what := match env.interface.resource? ⟨r⟩ with
          | some d => d.describe
          | none => r
        let how := match env.interface.resource? ⟨r⟩ with
          | some d => match d.acquirers with
            | a :: _ => s!"; open one with `hold {a}`"
            | [] => ""
          | none => ""
        err span s!"a call here requires {what} to be held{how}"
    | e => R := R.add e
  return R

/-- A resource acquired while an instance of it is held, when its declaration
does not nest. -/
def checkNesting (K : Ctx) (span : Span) (decl : Interface.ResourceDecl) :
    M Unit := do
  if let some h := K.held.nestingConflict decl then
    err span s!"{decl.describe} cannot be held inside another: `hold \
      {h.what}` at line {h.span.start.line} is still held"

/-- What a write effect touches, for a message. -/
def describeWrite : Eff → String
  | .pkt lo hi => s!"the packet bytes [{lo.printPred} .. {hi.printPred})"
  | .pktAll => "the packet"
  | .map m => s!"the map `{m}`"
  | .ctx f => s!"the context field `{f}`"
  | e => s!"`{e.print}`"

/-- The program's preserved regions against the effects of one
statement: a write into a preserved region or a resize under a
preserved packet region is an error at the statement, and a packet
write against a packet range demands, of the facts, that the two
ranges be disjoint. -/
def checkPreserved (env : Env) (K : Ctx) (span : Span) (E : Effs) :
    M Unit := do
  for r in K.preserved do
    for e in E.effs do
      match Koit.Effects.conflict r e with
      | .none => pure ()
      | .always =>
        match e with
        | .resize =>
          err span s!"this statement resizes the packet, which \
            `{r.printClause}` forbids: a resize moves every byte; drop the \
            clause or the resize"
        | _ =>
          err span s!"this statement writes {describeWrite e}, which \
            `{r.printClause}` forbids; drop the clause or the write"
      | .demand P =>
        unless Koit.Facts.entails (scope env K) K.facts P do
          err span s!"the write to {describeWrite e} under \
            `{r.printClause}` demands `{P.printPred}`; the facts here do \
            not entail it: `check` the offset, or narrow the clause"

mutual

/-- A block: the facts on exit, with those about its own locals
dropped, and the effects of its statements. -/
partial def checkStmts (env : Env) (K : Ctx) (ss : List Stmt) :
    M (Facts × Effs) := do
  let mut env := env
  let mut F := K.facts
  let mut E : Effs := {}
  let mut declared : List String := []
  for s in ss do
    let (env', F', names, E') ← checkStmt env { K with facts := F } s
    env := env'
    F := F'
    E := E.union E'
    declared := declared ++ names
  return (F.dropNames declared, E)

/-- One statement: the environment after it, the facts after it, the
names it declared, and its effects, its own checked against the
preserved regions and joined with those of the blocks inside it. -/
partial def checkStmt (env : Env) (K : Ctx) (s : Stmt) :
    M (Env × Facts × List String × Effs) := do
  let K ← guardCtx env K s
  let K ← moveCtx K s
  let (env', F', names, Esub) ← checkStmtBody env K s
  let E ← stmtEffects env K s
  checkPreserved env K s.span E
  checkHeld env K s.span E
  let E ← resolveNeeds env K s.span E
  return (env', F', names, E.union Esub)

/-- The typing of one statement, yielding the effects of the blocks
inside it. -/
partial def checkStmtBody (env : Env) (K : Ctx) (s : Stmt) :
    M (Env × Facts × List String × Effs) := do
  let sc := scope env K
  let F := K.facts
  match s with
  | .«let» span mutable x ty init =>
    if x == "_" then
      -- a bare expression statement is a call
      match init with
      | .expr (.call s' f args) =>
        let _ ← synthCall env K s' f args false
        return (env, afterCalls env sc F ((f, args) :: callsInArgs args), [],
                {})
      | .expr (.invalid s' m) => err s' m
      | _ => err span "a bare expression statement must be a call"
    else
      let (l, F') ← bindInit env K span mutable x ty init
      return (env.bind l, F', [x], {})
  | .assign span p e =>
    -- (Assign), (AssignW): a mutable scalar place, the field
    -- predicate or the local's refinement demanded, the store
    -- recorded
    let info ← placeTyUse env K p
    unless info.mutable do
      match p, info.origin with
      | .field _ _ f, .ctx =>
        let decl := env.kind.get!
        let writable := (decl.ctx.filter (·.writable)).map (·.name)
        err span s!"the context field `{f}` is not writable in \
          {article decl.name} `{decl.name}` program; \
          {if writable.isEmpty then "none of its fields is" else
            "the writable fields are " ++ ", ".intercalate writable}"
      | _, .map m =>
        err span s!"`{p.print}` is in the read-only map `{m}`, which the \
          program never writes"
      | _, _ =>
        err span s!"`{p.print}` is immutable; declare it with `var` to \
          assign to it"
    let tn ← env.norm info.ty
    match tn with
    | .slot _ n =>
      err span s!"a `{n}` is a slot: it is not assigned; it is named by \
        {env.slotUse n}"
    | _ => pure ()
    -- a kernel object the verifier admits loads from only
    if let some n := readOnlyRoot env p then
      err span s!"`{p.print}` is a field of a `{n}`, which the kernel lets \
        a program read and never write"
    unless tn.isScalar do
      err span s!"`{p.print}` is an aggregate of type `{info.ty.print}`; \
        assign its fields, or use `copy` (P3)"
    check env K e tn
    match p with
    | .field _ (.var _ "ctx") _ => pure ()
    | .field s q f =>
      let qinfo ← placeTy env K q
      match ← env.norm qinfo.ty with
      | .struct _ fields =>
        if let some fd := fields.find? (·.name == f) then
          if let some pred := fd.pred then
            let P := fields.foldl (fun P g =>
              if g.name == f then P
              else P.subst g.name (.read s (.field s q g.name))) pred
            demand env K span s!"the store to `{p.print}`" (P.subst f e)
      | _ => pure ()
    | .var s x =>
      match env.local? x with
      | some l =>
        if let some (v, _, pred) ← env.refinement? l.ty then
          demand env K span s!"the store to `{x}: {l.ty.print}`"
            (pred.subst v e)
          let _ := s
      | none => pure ()
    | _ => pure ()
    return (env, assignAfter env K p e, [], {})
  | .ite _ c t e =>
    check env K c (.bool c.span)
    let (Fthn, Fels) := iteEntry env K c
    let (Ft, Et) ← checkStmts env { K with facts := Fthn } t
    let (Fe, Ee) ← checkStmts env { K with facts := Fels } e
    -- (IfConst), and a condition the facts decide: one branch is dead;
    -- (Meet): the branches agree on what is moved
    iteJoin env K s.span c Ft Fe
    return (env, iteAfter env K c Ft Fe, [], Et.union Ee)
  | .loop _ n body =>
    -- (Repeat)
    checkCount env K "the count of `repeat`" n
    let iters := loopIters env n
    let (Fb, Eb) ← checkStmts env (loopCtx K (loopHead env sc F body iters))
      body
    loopMovedOk K s.span Fb "the next iteration"
    return (env, loopAfter env K body Fb iters, [], Eb)
  | .«for» span x lo hi body =>
    -- (For): the cap is the bound's largest value under the facts, or
    -- the top of its type; the body has `lo <= i < hi`
    check env K lo tU64
    check env K hi tU64
    let (Fb, Eb) ← checkStmts (env.bind (forLocal span x))
      (loopCtx K (forEntry env K span x lo hi body)) body
    loopMovedOk K span Fb "the next iteration"
    return (env, loopAfter env K body Fb (some (forCap env K hi)), [], Eb)
  | .brk span =>
    unless K.inLoop do err span "`break` outside a loop"
    loopMovedOk K span F "the code after the loop"
    return (env, F.bot, [], {})
  | .cont span =>
    unless K.inLoop do err span "`continue` outside a loop"
    loopMovedOk K span F "the next iteration"
    return (env, F.bot, [], {})
  | .ret span v =>
    checkRet env K span v
    return (env, F.bot, [], {})
  | .raise span _ r =>
    -- (Mark), (Fail): the context may fail
    unless K.mayFail do
      if K.inHandler then
        err span "a handler is a non-failing context: no marker and no \
          `fail` may appear in it"
      err span s!"`{K.fnName.getD "?"}` is not marked `fails`, so it may not \
        contain a marker, `check`, or `fail`"
    check env K r tU32
    return (env, F.bot, [], {})
  | .«try» span x f thn els elseExits =>
    let b ← fallibleTy env K f
    let env' ← match x, b.ty with
      | "_", _ => pure env
      | _, some t =>
        pure (env.bind { name := x, ty := t, mutable := false,
                         origin := b.origin })
      | _, none =>
        err span s!"`{x}` binds nothing: the operation yields no value; \
          write `_`"
    let (Fthn, Fels) ← fallibleFacts env' K x f b
    -- a result derived from an argument is bound under that argument's
    -- name: the argument must be a name bound by `hold` or itself
    -- derived, and the binding is recorded for (Move)
    let derived ← match f with
      | .call _ fn args =>
        match env.interface.call? fn with
        | some decl =>
          match decl.derivedFrom, decl.sig with
          | some pname, .fn params _ =>
            let arg := (params.zip args).find? (·.1.name == pname)
            let parent ← match arg with
              | some (_, .place (.var _ y)) | some (_, .val (.var _ y)) => pure y
              | _ => err span s!"`{fn}` derives its result from `{pname}`, \
                  which must be a name"
            let held := K.held.any (·.name == some parent) ||
              K.derived.any (·.1 == parent)
            unless held do
              err span s!"`{fn}` derives its result from `{pname}`: `{parent}` \
                must be a name bound by `hold`, or derived from one"
            pure (if x == "_" then K.derived else (x, parent) :: K.derived)
          | _, _ => pure K.derived
        | none => pure K.derived
      | _ => pure K.derived
    let (Ft, Et) ← checkStmts env' { K with facts := Fthn, derived } thn
    let (Fe, Ee) ← checkStmts env
      { K with facts := Fels, errnoOk := fallibleKind env f == .failed_call } els
    if elseExits && !exits els then
      err span s!"the `else` block must end in an exit: {exitForms} \
       "
    joinMoved span (Ft.dropNames [x]) Fe
    return (env, meetK env K (Ft.dropNames [x]) Fe, [], Et.union Ee)
  | .hold span r x acq body els =>
    -- (Hold): the body under the resource, which its declaration must allow
    -- to nest; `move` consistency comes with ownership
    let b ← fallibleTy env K acq
    let decl ← match env.interface.resource? r with
      | some decl => pure decl
      | none => err span s!"`{r}` is not a resource the interface declares"
    match decl.fails, els with
    | some _, some _ =>
      if decl.holdsOnFailure then
        err span s!"`{acqName acq}` holds on failure: the kernel keeps the \
          reference whether or not it obtained anything, so the acquisition \
          cannot fail here and takes no `?` or `else`"
    | some k, none =>
      unless decl.holdsOnFailure do
        err span s!"`{acqName acq}` can fail (kind `{k}`); the acquisition \
          needs `?` or `else`"
    | none, some _ =>
      err span s!"`{acqName acq}` cannot fail, so it takes no `?` or `else`"
    | _, _ => pure ()
    let env' ← match x, b.ty with
      | some n, some t =>
        pure (env.bind { name := n, ty := t, mutable := false,
                         origin := .kernel })
      | none, none => pure env
      | some _, none =>
        err span s!"`{acqName acq}` binds nothing: it is a scope-only \
          resource, `hold {acqName acq} \{ ... }`"
      | none, some _ =>
        err span s!"`{acqName acq}` yields a value; bind it with \
          `hold x = ...`"
    checkNesting K span decl
    let F := holdEntry env K (decl.arg == .call) acq
    let (Fb, Eb) ← checkStmts env' (holdCtx env K span decl x acq) body
    let Fb := match x with
      | some n => Fb.dropNames [n]
      | none => Fb
    match els with
    | some e =>
      let (Fe, Ee) ← checkStmts env
        { K with facts := F, errnoOk := decl.fails == some .failed_call } e
      unless exits e do
        err span s!"the `else` block must end in an exit: {exitForms} \
         "
      joinMoved span Fb Fe
      return (env, meetK env K Fb Fe, [], Eb.union Ee)
    | none => return (env, Fb, [], Eb)
  | .atomic span x op p args =>
    let info ← placeTyUse env K p
    unless info.mutable do err span s!"`{p.print}` is immutable"
    let tn ← env.norm info.ty
    unless tn.isIntTy do
      err span s!"atomic updates apply to an integer place; `{p.print}` is a \
        `{info.ty.print}`"
    -- the instruction set has no narrower atomic operation
    unless atomicWidth tn do
      err span s!"an atomic update needs a 32- or 64-bit place; `{p.print}` \
        is a `{info.ty.print}`"
    match info.origin with
    | .stack | .map _ => pure ()
    | _ =>
      err span "atomic updates apply to a place in a map value or on the \
        stack"
    let n := if op == .cmpxchg then 2 else 1
    unless args.length == n do
      err span s!"`{op.spelling}` takes a place and {n} value(s) \
       "
    for a in args do
      check env K a tn
    let F := atomicAfter env K p args x
    match x with
    | some n =>
      let l : Local := { name := n, ty := tn, mutable := false,
                         origin := .stack }
      return (env.bind l, F, [n], {})
    | none => return (env, F, [], {})
  | .invalid span m => err span m

end

end Koit.Check
