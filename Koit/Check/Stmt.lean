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
open Koit.Prelude (tU32 tU64 AcqArg)
open Koit.Facts (Origin Facts Fact Scope)
open Koit.Effects (Eff Effs Conflict)

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
    for d in env.types ++ env.prelude.types do
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
a prelude call with the `call` effect. -/
def callKills (env : Env) (f : String) : Bool :=
  if (env.fn? f).isSome then true
  else match env.prelude.call? f with
    | some row => row.effects.any fun
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

/-- The facts at a loop head: what the body may write is dropped,
with every shared place, and the refinements in scope hold again. -/
def loopHead (env : Env) (sc : Scope) (F : Facts) (body : List Stmt) :
    Facts :=
  (refinementFacts env).foldl Facts.add (F.inv sc (assignedIn body))

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
      let row := env.kind.get!
      let vals := vset.filterMap fun n => (row.verdicts.lookup n).map Int.ofNat
      let setText := "{" ++ ", ".intercalate vset ++ "}"
      unless Koit.Facts.entailsIn sc K.facts e vals do
        -- a value the facts pin down is named
        match Koit.Facts.constOf sc K.facts e with
        | some c =>
          match row.verdicts.find? (·.2 == c.toNat) with
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

/-- The acquiring function of a `hold`, for messages. -/
def acqName : Fallible → String
  | .acquire _ _ f .. => f
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

/-! ### The fact transformers of the statement rules, shared with the
judgment of `Rules.lean` so that the two cannot drift apart. -/

/-- After `p = e`: the kills of the calls in it, the store recorded,
and a refined local's refinement in force again. -/
def assignAfter (env : Env) (K : Ctx) (p : Place) (e : Expr) : Facts :=
  let sc := scope env K
  let F := afterCalls env sc K.facts (callsInPlace p ++ callsInExpr e)
  let F := F.record sc p e
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

/-- After a conditional: what the two branches meet at, or the live
branch alone when the facts decide the condition (IfConst). -/
def iteAfter (env : Env) (K : Ctx) (c : Expr) (Ft Fe : Facts) : Facts :=
  let sc := scope env K
  let F := afterCalls env sc K.facts (callsInExpr c)
  match Koit.Facts.eval sc (F.state sc) (F.resolveExpr c) with
  | .bool .yes => { Ft with caps := Ft.caps ++ Fe.caps }
  | .bool .no => { Fe with caps := Ft.caps ++ Fe.caps }
  | _ => meetK env K Ft Fe

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
  let Fh := loopHead env (scope env K) K.facts body
  let Fh := { Fh with caps := Fh.caps ++ [(s, forCap env K hi)] }
  let sc' := scope (env.bind (forLocal s x)) K
  (Fh.assume sc' (.cmp s .le lo (.var s x))).assume sc'
    (.cmp s .lt (.var s x) hi)

/-- After a loop: the head's facts, with the caps the body gathered. -/
def loopAfter (env : Env) (K : Ctx) (body : List Stmt) (Fb : Facts) : Facts :=
  { loopHead env (scope env K) K.facts body with caps := Fb.caps }

/-- The facts a `hold` body starts from: the acquisition's kills when
it is a kernel call. -/
def holdEntry (env : Env) (K : Ctx) (isCall : Bool) (acq : Fallible) : Facts :=
  if isCall then afterCalls env (scope env K) K.facts (callsInFallible acq)
  else K.facts

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
and `view` parameters becoming writes to what was passed; a prelude
call contributes its row, with the writes of `copy`, `fill`,
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
  match env.prelude.call? f with
  | some row =>
    let mut R := Effs.ofCore row.effects
    match f, args with
    | "copy", .place dst :: _ | "fill", .place dst :: _ =>
      R := R.union (← writesOf env K dst)
    | "insert", .map _ m :: _ | "delete", .map _ m :: _ =>
      R := R.add (.map m)
    | _, _ => pure ()
    return R
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
  let (env', F', names, Esub) ← checkStmtBody env K s
  let E ← stmtEffects env K s
  checkPreserved env K s.span E
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
        err span s!"the context field `{f}` is not writable in \
          {article (env.kind.map (·.name)).get!} \
          `{(env.kind.map (·.name)).get!}` program"
      | _, _ =>
        err span s!"`{p.print}` is immutable; declare it with `var` to \
          assign to it"
    let tn ← env.norm info.ty
    match tn with
    | .slot _ n =>
      err span s!"a `{n}` is a slot: it is not assigned; it is named by \
        {env.slotUse n}"
    | _ => pure ()
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
    -- (IfConst), and a condition the facts decide: one branch is dead
    return (env, iteAfter env K c Ft Fe, [], Et.union Ee)
  | .loop _ n body =>
    -- (Repeat)
    checkCount env K "the count of `repeat`" n
    let (Fb, Eb) ← checkStmts env { K with inLoop := true,
                                           facts := loopHead env sc F body }
      body
    return (env, loopAfter env K body Fb, [], Eb)
  | .«for» span x lo hi body =>
    -- (For): the cap is the bound's largest value under the facts, or
    -- the top of its type; the body has `lo <= i < hi`
    check env K lo tU64
    check env K hi tU64
    let (Fb, Eb) ← checkStmts (env.bind (forLocal span x))
      { K with inLoop := true, facts := forEntry env K span x lo hi body } body
    return (env, loopAfter env K body Fb, [], Eb)
  | .brk span =>
    unless K.inLoop do err span "`break` outside a loop"
    return (env, F.bot, [], {})
  | .cont span =>
    unless K.inLoop do err span "`continue` outside a loop"
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
    let (Ft, Et) ← checkStmts env' { K with facts := Fthn } thn
    let (Fe, Ee) ← checkStmts env
      { K with facts := Fels, errnoOk := fallibleKind env f == .helper } els
    if elseExits && !exits els then
      err span s!"the `else` block must end in an exit: {exitForms} \
       "
    return (env, meetK env K (Ft.dropNames [x]) Fe, [], Et.union Ee)
  | .hold span r x acq body els =>
    -- (Hold); the held set, forbidden effects, nesting, and `move`
    -- consistency come with resources
    let b ← fallibleTy env K acq
    let row ← match env.prelude.resource? r with
      | some row => pure row
      | none => err span s!"`{r}` has no row in the resource table"
    match row.fails, els with
    | some k, none =>
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
    let F := holdEntry env K (row.arg == .call) acq
    let (Fb, Eb) ← checkStmts env' { K with facts := F } body
    let Fb := match x with
      | some n => Fb.dropNames [n]
      | none => Fb
    match els with
    | some e =>
      let (Fe, Ee) ← checkStmts env
        { K with facts := F, errnoOk := row.fails == some .helper } e
      unless exits e do
        err span s!"the `else` block must end in an exit: {exitForms} \
         "
      return (env, meetK env K Fb Fe, [], Eb.union Ee)
    | none => return (env, Fb, [], Eb)
  | .atomic span x op p args =>
    let info ← placeTyUse env K p
    unless info.mutable do err span s!"`{p.print}` is immutable"
    let tn ← env.norm info.ty
    unless tn.isIntTy do
      err span s!"atomic updates apply to an integer place; `{p.print}` is a \
        `{info.ty.print}`"
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
