import Koit.Check.Decl

/-!
The typing judgment of Core as a proposition: the expression and
place rules with their demands `F |= P` as `Entails` premises, the
semantic entailment of `Facts.lean`, and the statement rules carrying
the facts from one statement to the next; the held set and the
effects come with effects as further premises of the same
constructors.

`checkUnit` (Decl.lean) is the decision procedure for this judgment;
`check_sound` states that a unit it accepts is well-typed, and rests
on `entails_sound`, which says the procedure decides a subset of
`Entails`. The judgment is declarative where the checker is
algorithmic: (Arith) here takes any integer type both operands check
against, and the checker picks the operand with a type of its own.
Where a statement rule's content is a computation on the facts, the
premise names the checker's own function for it, `bindInit`,
`afterCalls`, `loopHead`, `fallibleFacts`, `meetK`, so that the
judgment and the checker cannot drift apart on those; the demands the
rules name are explicit premises. T1, safety, will be stated on
`UnitOk` once the Core semantics is defined.

The proofs are deferred: definitions, then corpus, then proofs.
-/

namespace Koit.Check

open Koit (Span)
open Koit.Core
open Koit.Prelude (KindRow CallRow AcqArg Home tU32 tU64)
open Koit.Facts (Facts Caps Entails)

/-- The comparisons a byte-order value admits. -/
def isCmpBe : CmpOp → Bool
  | .eq | .ne => true
  | _ => false

mutual

/-- `G;K |- e => T`, synthesis. -/
inductive Synth : Env → Ctx → Expr → Ty → Prop
  /-- (Var), a local. -/
  | var {env K s x l} :
      env.local? x = some l → Synth env K (.var s x) l.ty
  /-- (Var), a typed constant or a configuration constant. -/
  | constTyped {env K s x d t} :
      env.local? x = none → env.const? x = some d → d.ty = some t →
      Synth env K (.var s x) t
  | config {env K s x d} :
      env.local? x = none → env.const? x = none → env.config? x = some d →
      Synth env K (.var s x) d.ty
  /-- An untyped constant takes its type from each use. -/
  | constUntyped {env K s x d t env'} :
      env.local? x = none → env.const? x = some d → d.ty = none →
      constEnv env x s = .ok env' → Synth env' K d.value t →
      Synth env K (.var s x) t
  /-- The verdict names of the program's kind. -/
  | verdict {env K s x t} :
      env.local? x = none → env.const? x = none → env.config? x = none →
      env.verdict? x = some t → Synth env K (.var s x) t
  /-- (LitDef). -/
  | litDef {env K s v t} : v < 2 ^ 64 → Synth env K (.lit s v t) tU64
  | char {env K s c} : Synth env K (.char s c) (.int s false 8)
  | bool {env K s b} : Synth env K (.bool s b) (.bool s)
  /-- (Arith). -/
  | arith {env K s op l r tn} :
      tn.isIntTy → Check env K l tn → Check env K r tn →
      Synth env K (.arith s op l r) tn
  /-- (Cmp). -/
  | cmp {env K s op l r t tn} :
      Synth env K l t → env.norm t = .ok tn → tn.isIntTy →
      Check env K r tn →
      Synth env K (.cmp s op l r) (.bool s)
  /-- (CmpBe). -/
  | cmpBe {env K s op l r t s' w} :
      isCmpBe op → Synth env K l t → env.norm t = .ok (.be s' w) →
      Check env K r (.be s' w) → Synth env K (.cmp s op l r) (.bool s)
  | not {env K s e} :
      Check env K e (.bool s) → Synth env K (.not s e) (.bool s)
  | and {env K s l r} :
      Check env K l (.bool s) → Check env K r (.bool s) →
      Synth env K (.and s l r) (.bool s)
  | or {env K s l r} :
      Check env K l (.bool s) → Check env K r (.bool s) →
      Synth env K (.or s l r) (.bool s)
  /-- (Cast), integer to integer. -/
  | cast {env K s e t tn src sn} :
      env.norm t = .ok tn → tn.isIntTy → Synth env K e src →
      env.norm src = .ok sn → sn.isIntTy → Synth env K (.cast s e t) t
  /-- `bool as uN`. -/
  | castBool {env K s e t s' w src s''} :
      env.norm t = .ok (.int s' false w) → Synth env K e src →
      env.norm src = .ok (.bool s'') → Synth env K (.cast s e t) t
  /-- (Hton). -/
  | hton {env K s e t s' w} :
      Synth env K e t → env.norm t = .ok (.int s' false w) →
      (w = 16 ∨ w = 32 ∨ w = 64) → Synth env K (.hton s e) (.be s w)
  /-- (Ntoh). -/
  | ntoh {env K s e t s' w} :
      Synth env K e t → env.norm t = .ok (.be s' w) →
      Synth env K (.ntoh s e) (.int s false w)
  /-- (Read): a scalar place at its base type. -/
  | read {env K s p info tn} :
      PlaceOf env K p info → env.norm info.ty = .ok tn → tn.isScalar →
      Synth env K (.read s p) tn
  /-- `size T` of a sized type, typed as a literal. -/
  | size {env K s t sz} : env.layout t = .ok sz → Synth env K (.size s t) tU64
  /-- The call rule for a function of the unit. -/
  | callFn {env K s f args d t} :
      env.fn? f = some d → ArgsOk env K f d.params args →
      (d.fails → K.mayFail) → d.ret = some t →
      (∀ s' t', t ≠ .opt s' t') →
      Synth env K (.call s f args) t
  /-- A prelude call with a signature. -/
  | callPrelude {env K s f args row params t} :
      env.fn? f = none → env.prelude.call? f = some row →
      row.acquires = none →
      row.fails = none → row.sig = .fn params (some t) →
      PreludeOk env K s row → ArgsOk env K f params args →
      Synth env K (.call s f args) t
  /-- `errno` in the `else` of a helper call. -/
  | errno {env K s} : K.errnoOk → Synth env K (.errno s) tU32

/-- `G;K |- e <= T`, checking. -/
inductive Check : Env → Ctx → Expr → Ty → Prop
  /-- (Lit). -/
  | lit {env K s v text t s' signed w} :
      env.norm t = .ok (.int s' signed w) → representable v signed w →
      Check env K (.lit s v text) t
  /-- An untyped constant checked at its use. -/
  | constUntyped {env K s x d t env'} :
      env.local? x = none → env.const? x = some d → d.ty = none →
      constEnv env x s = .ok env' → Check env' K d.value t →
      Check env K (.var s x) t
  /-- (Arith) in checking mode. -/
  | arith {env K s op l r t tn} :
      env.norm t = .ok tn → tn.isIntTy → Check env K l tn →
      Check env K r tn →
      Check env K (.arith s op l r) t
  /-- (Hton) in checking mode: the width comes from the context. -/
  | hton {env K s e t s' w} :
      env.norm t = .ok (.be s' w) → Check env K e (.int s false w) →
      Check env K (.hton s e) t
  /-- (Sub), refinement weakening: `{v:T | P} <: T` through base-type
  equality. -/
  | sub {env K e t t'} :
      env.refinement? t = .ok none →
      Synth env K e t' → env.eqv t' t = .ok true → Check env K e t
  /-- (Sub) against a refinement `{v:T | Q}`: the base, then `Q` of
  the value is a demand. -/
  | refine {env K e t v base pred} :
      env.refinement? t = .ok (some (v, base, pred)) →
      Check env K e base →
      Entails (scope env K) K.facts (pred.subst v e) →
      Check env K e t

/-- `G;K |- p : T place [mut]`, with the origin of the place. -/
inductive PlaceOf : Env → Ctx → Place → PlaceInfo → Prop
  /-- (PVar): a scalar local. -/
  | var {env K s x l} :
      env.local? x = some l → ¬ l.ty.isPlaceTy →
      PlaceOf env K (.var s x)
        { ty := l.ty, mutable := l.mutable, origin := l.origin }
  /-- (PDeref) for a reference named by a binding: `x.f` reads
  through `x`. The guard premise is session 4. -/
  | refVar {env K s x l s' t} :
      env.local? x = some l → l.ty = .ref s' t →
      PlaceOf env K (.var s x) { ty := t, mutable := true, origin := l.origin }
  | viewVar {env K s x l s' t} :
      env.local? x = some l → l.ty = .view s' t →
      PlaceOf env K (.var s x) { ty := t, mutable := true, origin := .pkt }
  /-- An owned reference names a place of its type. -/
  | ownVar {env K s x l s' t} :
      env.local? x = some l → l.ty = .own s' t →
      PlaceOf env K (.var s x) { ty := t, mutable := true, origin := .kernel }
  /-- A context field, per the kind's table. -/
  | ctx {env K s s' f row cf} :
      env.kind = some row → row.ctx.find? (·.name == f) = some cf →
      PlaceOf env K (.field s (.var s' "ctx") f)
        { ty := cf.ty, mutable := cf.writable, origin := .ctx }
  /-- (PField). -/
  | field {env K s q f info s' fields fd} :
      PlaceOf env K q info → env.norm info.ty = .ok (.struct s' fields) →
      fields.find? (·.name == f) = some fd →
      PlaceOf env K (.field s q f)
        { ty := fd.ty, mutable := info.mutable, origin := info.origin }
  /-- (PIndex): the index is unsigned and `F |= e < n`. -/
  | index {env K s q i info s' elem n} :
      PlaceOf env K q info → env.norm info.ty = .ok (.array s' elem n) →
      IndexOk env K i →
      Entails (scope env K) K.facts (.cmp s .lt i n) →
      PlaceOf env K (.index s q i)
        { ty := elem, mutable := info.mutable, origin := info.origin }
  /-- (PArr) for `array` and `percpu_array`: `F |= e < n`. -/
  | slotArray {env K s m i d n v} :
      env.map? m = some d → d.kind = .array n v → IndexOk env K i →
      Entails (scope env K) K.facts (.cmp s .lt i n) →
      PlaceOf env K (.slot s m i) { ty := v, mutable := true, origin := .map m }
  | slotPercpu {env K s m i d n v} :
      env.map? m = some d → d.kind = .percpu n v → IndexOk env K i →
      Entails (scope env K) K.facts (.cmp s .lt i n) →
      PlaceOf env K (.slot s m i) { ty := v, mutable := true, origin := .map m }
  /-- (PDeref), explicit, for a scalar pointee. -/
  | derefRef {env K s s' x l s'' t tn} :
      env.local? x = some l → l.ty = .ref s'' t → env.norm t = .ok tn →
      tn.isScalar →
      PlaceOf env K (.deref s (.var s' x))
        { ty := t, mutable := true, origin := l.origin }
  | derefView {env K s s' x l s'' t tn} :
      env.local? x = some l → l.ty = .view s'' t → env.norm t = .ok tn →
      tn.isScalar →
      PlaceOf env K (.deref s (.var s' x))
        { ty := t, mutable := true, origin := .pkt }

/-- An index is an unsigned integer. -/
inductive IndexOk : Env → Ctx → Expr → Prop
  | poly {env K i} : env.isPoly i → Check env K i tU64 → IndexOk env K i
  | typed {env K i t s w} :
      ¬ env.isPoly i → Synth env K i t →
      env.norm t = .ok (.int s false w) →
      IndexOk env K i

/-- Arguments against parameters. -/
inductive ArgsOk : Env → Ctx → String → List Param → List Arg → Prop
  | nil {env K f} : ArgsOk env K f [] []
  /-- A scalar parameter takes a value; a `const` parameter a constant
  expression; a refined parameter's predicate is a precondition. -/
  | val {env K f p ps e as} :
      (∀ s t, p.ty ≠ .ref s t) → (∀ s t, p.ty ≠ .view s t) →
      (∀ s t, p.ty ≠ .own s t) →
      (p.isConst = true → env.isConstExpr e = true) →
      Check env K e p.ty →
      (∀ q, p.pred = some q →
        Entails (scope env K) K.facts (q.subst p.name e)) →
      ArgsOk env K f ps as →
      ArgsOk env K f (p :: ps) (.val e :: as)
  /-- A scalar parameter takes a scalar place, read. -/
  | scalarPlace {env K f p ps q as info tn pn} :
      (∀ s t, p.ty ≠ .ref s t) → (∀ s t, p.ty ≠ .view s t) →
      (∀ s t, p.ty ≠ .own s t) → p.isConst = false →
      PlaceOf env K q info →
      env.norm info.ty = .ok tn → tn.isScalar → env.norm p.ty = .ok pn →
      env.eqv tn pn = .ok true →
      (∀ q', p.pred = some q' →
        Entails (scope env K) K.facts (q'.subst p.name (.read q.span q))) →
      ArgsOk env K f ps as →
      ArgsOk env K f (p :: ps) (.place q :: as)
  /-- A `ref T` parameter takes a stack or map place of type `T`. -/
  | ref {env K f p ps q as s t info} :
      p.ty = .ref s t → PlaceOf env K q info → info.origin ≠ .pkt →
      env.eqv info.ty t = .ok true → ArgsOk env K f ps as →
      ArgsOk env K f (p :: ps) (.place q :: as)
  /-- A `view T` parameter takes a place in the packet of type `T`. -/
  | view {env K f p ps q as s t info} :
      p.ty = .view s t → PlaceOf env K q info → info.origin = .pkt →
      env.eqv info.ty t = .ok true → ArgsOk env K f ps as →
      ArgsOk env K f (p :: ps) (.place q :: as)
  /-- (Move): an `own T` parameter is a sink; the moved-state premise
  is session 4. -/
  | move {env K f p ps s x as s' t l s'' t'} :
      p.ty = .own s' t → env.local? x = some l → l.ty = .own s'' t' →
      env.eqv t t' = .ok true → ArgsOk env K f ps as →
      ArgsOk env K f (p :: ps) (.val (.move s x) :: as)

/-- A prelude call's availability and license. -/
inductive PreludeOk : Env → Ctx → Span → CallRow → Prop
  | mk {env K s row} :
      (row.name.startsWith "pkt." → ∃ r, env.kind = some r ∧ r.hasPkt) →
      (∀ k, env.kind = some k → row.kinds ≠ [] →
        row.kinds.contains k.name) →
      (row.gplOnly → env.gplCompatible) → PreludeOk env K s row

end

/-- What a fallible operation binds, the base premises. -/
inductive FallibleOk : Env → Ctx → Fallible → Bound → Prop
  /-- (View): the offset is a `u64`, the type packet-representable. -/
  | view {env K s off t row sz} :
      env.kind = some row → row.hasPkt → Check env K off tU64 →
      env.notRepresentable t false = .ok none → env.layout t = .ok sz →
      FallibleOk env K (.view s off t)
        { ty := some (.view s t), origin := .pkt }
  /-- (Lookup). -/
  | lookup {env K s m k d n kt vt info} :
      env.map? m = some d → d.kind = .hash n kt vt →
      PlaceOf env K k info →
      env.eqv info.ty kt = .ok true →
      FallibleOk env K (.lookup s m k)
        { ty := some (.ref s vt), origin := .map m }
  /-- (LoadW): the field's predicate becomes the refinement. -/
  | loadw {env K s s' q f info s'' fields fd pred} :
      PlaceOf env K q info → env.norm info.ty = .ok (.struct s'' fields) →
      fields.find? (·.name == f) = some fd → fd.pred = some pred →
      FallibleOk env K (.loadw s (.field s' q f))
        { ty := some (.refined s f fd.ty pred), origin := .stack }
  /-- A fallible helper. -/
  | call {env K s f args row params ret} :
      env.fn? f = none → env.prelude.call? f = some row →
      row.acquires = none →
      row.fails ≠ none → row.sig = .fn params ret →
      PreludeOk env K s row →
      ArgsOk env K f params args →
      FallibleOk env K (.call s f args) { ty := ret, origin := .stack }
  /-- A function returning `T?`. -/
  | callopt {env K s f args d s' t} :
      env.fn? f = some d → ArgsOk env K f d.params args →
      (d.fails → K.mayFail) → d.ret = some (.opt s' t) →
      FallibleOk env K (.callopt s f args) { ty := some t, origin := .stack }
  /-- (Coerce): the coercion to a refinement type. -/
  | coerce {env K s e s' v base pred bn} :
      env.norm base = .ok bn → bn.isScalar → Check env K e base →
      checkPred env
        [{ name := v, ty := base, mutable := false, origin := .stack }]
        pred = .ok () →
      FallibleOk env K (.coerce s e (.refined s' v base pred))
        { ty := some (.refined s' v base pred), origin := .stack }
  /-- An acquisition whose row takes a place of a slot type, in one of
  the slot's homes. -/
  | acquireSlot {env K s r f t p info s' slot row srow m} :
      env.prelude.resource? r = some row → row.arg = .place slot →
      PlaceOf env K p info → env.norm info.ty = .ok (.slot s' slot) →
      env.prelude.slot? slot = some srow → info.origin = .map m →
      srow.homes.contains .mapValue = true →
      FallibleOk env K (.acquire s r f t [.place p]) { ty := none }
  /-- A scope-only acquisition. -/
  | acquireScope {env K s r f t row} :
      env.prelude.resource? r = some row → row.arg = .scope →
      FallibleOk env K (.acquire s r f t []) { ty := none }
  /-- An acquisition through a kernel function's row: the result is
  `own T`, bound by `hold`. -/
  | acquireCall {env K s r f args row crow params ret} :
      env.prelude.resource? r = some row → row.arg = .call →
      env.prelude.call? f = some crow → crow.sig = .fn params ret →
      PreludeOk env K s crow → ArgsOk env K f params args →
      FallibleOk env K (.acquire s r f none args)
        { ty := ret, origin := .kernel }
  /-- A ring-buffer record, the one acquiring builtin. -/
  | acquireReserve {env K s r s' m t d n sz row} :
      env.prelude.resource? r = some row → row.arg = .call →
      env.map? m = some d → d.kind = .ringbuf n →
      env.notRepresentable t false = .ok none → env.layout t = .ok sz →
      FallibleOk env K (.acquire s r "reserve" (some t) [.map s' m])
        { ty := some (.own s t), origin := .kernel }

/-- A local from what a fallible operation binds. -/
def boundLocal (x : String) (t : Ty) (b : Bound) : Local :=
  { name := x, ty := t, mutable := false, origin := b.origin }

/-- The field predicate a store to `p.f` must establish, with the
value stored for `f` and every sibling read from the place; `none`
when the field has none. -/
def storeDemand (env : Env) (K : Ctx) (s : Span) (q : Place) (f : String)
    (e : Expr) : Option Expr :=
  match placeTy env K q with
  | .ok info =>
    match env.norm info.ty with
    | .ok (.struct _ fields) =>
      (fields.find? (·.name == f)).bind fun fd => fd.pred.map fun pred =>
        (fields.foldl (fun P g =>
          if g.name == f then P
          else P.subst g.name (.read s (.field s q g.name))) pred).subst f e
    | _ => none
  | .error _ => none

/-- The refinement of a local, if it has one. -/
def localRefinement (env : Env) (x : String) : Option (String × Ty × Expr) :=
  (env.local? x).bind fun l => (env.refinement? l.ty).toOption.bind id

mutual

/-- `G;F;K |- s -| F'`: one statement, with the environment and the
facts after it and the names it declared. -/
inductive StmtOk :
    Env → Ctx → Stmt → Env → Facts → List String → Prop
  /-- A call for its effect: the facts about shared places go. -/
  | callStmt {env K s s' f args r} :
      synthCall env K s' f args false = .ok r →
      StmtOk env K (.«let» s false "_" none (.expr (.call s' f args))) env
        (afterCalls env (scope env K) K.facts ((f, args) :: callsInArgs args))
        []
  /-- `let x = e`, `var x = e`, `let x = p`, and the struct literal:
  the local, and the facts `bindInit` derives, with the demands of a
  declared refinement and of the literal's field predicates inside
  it. -/
  | «let» {env K s m x ty init l F'} :
      x ≠ "_" → bindInit env K s m x ty init = .ok (l, F') →
      StmtOk env K (.«let» s m x ty init) (env.bind l) F' [x]
  /-- (Assign), (AssignW): a mutable scalar place; the field predicate
  with siblings read, or the local's refinement, is a demand; the
  store is recorded after its kills. -/
  | assign {env K s p e info tn} :
      PlaceOf env K p info → info.mutable → env.norm info.ty = .ok tn →
      tn.isScalar → Check env K e tn →
      (∀ s' q f P, p = .field s' q f →
        storeDemand env K s' q f e = some P →
        Entails (scope env K) K.facts P) →
      (∀ s' x v base pred, p = .var s' x →
        localRefinement env x = some (v, base, pred) →
        Entails (scope env K) K.facts (pred.subst v e)) →
      StmtOk env K (.assign s p e) env (assignAfter env K p e) []
  /-- Both branches, the condition in one and its negation in the
  other; a condition the facts decide leaves one branch dead. -/
  | ite {env K s c t e Ft Fe} :
      Check env K c (.bool c.span) →
      BlockOk env { K with facts := (iteEntry env K c).1 } t Ft →
      BlockOk env { K with facts := (iteEntry env K c).2 } e Fe →
      StmtOk env K (.ite s c t e) env (iteAfter env K c Ft Fe) []
  /-- (Repeat): the body under the loop head's facts. -/
  | loop {env K s n body Fb} :
      checkCount env K "the count of `repeat`" n = .ok () →
      BlockOk env { K with inLoop := true,
                           facts := loopHead env (scope env K) K.facts body }
        body Fb →
      StmtOk env K (.loop s n body) env (loopAfter env K body Fb) []
  /-- (For): the index is a `u64` with `lo <= i < hi` in the body; the
  cap is the bound's largest value under the facts. -/
  | «for» {env K s x lo hi body Fb} :
      Check env K lo tU64 → Check env K hi tU64 →
      BlockOk (env.bind (forLocal s x))
        { K with inLoop := true, facts := forEntry env K s x lo hi body }
        body Fb →
      StmtOk env K (.«for» s x lo hi body) env (loopAfter env K body Fb) []
  | brk {env K s} : K.inLoop → StmtOk env K (.brk s) env K.facts.bot []
  | cont {env K s} : K.inLoop → StmtOk env K (.cont s) env K.facts.bot []
  /-- (Return): the value against the context, the verdict set or the
  refined result demanded inside `checkRet`. -/
  | ret {env K s v} :
      checkRet env K s v = .ok () → StmtOk env K (.ret s v) env K.facts.bot []
  /-- (Mark), (Fail): the context may fail; the reason is a `u32`. -/
  | raise {env K s k r} :
      K.mayFail → Check env K r tU32 →
      StmtOk env K (.raise s k r) env K.facts.bot []
  /-- (Else), (IfLet), (Coerce), (Mark), (LoadW), (View): `try` binds
  the operation's result in the then-branch with the facts the
  operation establishes; a tail's `else` exits. -/
  | «try» {env K s x f thn els ex b t Fthn Fels Ft Fe} :
      FallibleOk env K f b → b.ty = some t → x ≠ "_" →
      fallibleFacts (env.bind (boundLocal x t b)) K x f b = .ok (Fthn, Fels) →
      BlockOk (env.bind (boundLocal x t b)) { K with facts := Fthn } thn Ft →
      BlockOk env { K with facts := Fels,
                           errnoOk := fallibleKind env f == .helper } els Fe →
      (ex = true → exits els = true) →
      StmtOk env K (.«try» s x f thn els ex) env
        (meetK env K (Ft.dropNames [x]) Fe) []
  | tryDiscard {env K s f thn els ex b Fthn Fels Ft Fe} :
      FallibleOk env K f b →
      fallibleFacts env K "_" f b = .ok (Fthn, Fels) →
      BlockOk env { K with facts := Fthn } thn Ft →
      BlockOk env { K with facts := Fels,
                           errnoOk := fallibleKind env f == .helper } els Fe →
      (ex = true → exits els = true) →
      StmtOk env K (.«try» s "_" f thn els ex) env (meetK env K Ft Fe) []
  /-- (Hold), scope-only: the held set comes with effects. -/
  | holdScope {env K s r acq body row Fb} :
      FallibleOk env K acq { ty := none } →
      env.prelude.resource? r = some row →
      row.fails = none →
      BlockOk env { K with facts := holdEntry env K (row.arg == .call) acq }
        body Fb →
      StmtOk env K (.hold s r none acq body none) env Fb []
  /-- (Hold), value-yielding, with the tail as `else`. -/
  | holdValue {env K s r x acq body els row b t Fb Fe} :
      FallibleOk env K acq b → b.ty = some t →
      env.prelude.resource? r = some row → row.fails ≠ none →
      BlockOk (env.bind { name := x, ty := t, mutable := false,
                          origin := .kernel })
        { K with facts := holdEntry env K (row.arg == .call) acq } body Fb →
      BlockOk env { K with facts := holdEntry env K (row.arg == .call) acq,
                           errnoOk := row.fails == some .helper } els Fe →
      exits els →
      StmtOk env K (.hold s r (some x) acq body (some els)) env
        (meetK env K (Fb.dropNames [x]) Fe) []
  /-- (Atomic): an integer place in a map value or on the stack; the
  place's facts go. -/
  | atomic {env K s x op p args info tn} :
      PlaceOf env K p info → info.mutable → env.norm info.ty = .ok tn →
      tn.isIntTy → (info.origin = .stack ∨ ∃ m, info.origin = .map m) →
      args.length = (if op = .cmpxchg then 2 else 1) →
      (∀ a ∈ args, Check env K a tn) →
      StmtOk env K (.atomic s x op p args)
        (match x with
         | some n => env.bind { name := n, ty := tn, mutable := false,
                                origin := .stack }
         | none => env)
        (atomicAfter env K p args x)
        (match x with
         | some n => [n]
         | none => [])

/-- `G;F;K |- s* -| F'`: a sequence, each statement under the facts
the previous left, with the names declared. -/
inductive StmtsOk : Env → Ctx → List Stmt → Facts → List String → Prop
  | nil {env K} : StmtsOk env K [] K.facts []
  | cons {env K s rest env' F' ns F'' ns'} :
      StmtOk env K s env' F' ns →
      StmtsOk env' { K with facts := F' } rest F'' ns' →
      StmtsOk env K (s :: rest) F'' (ns ++ ns')

/-- A block: its statements, with the facts about its own locals
dropped on exit. -/
inductive BlockOk : Env → Ctx → List Stmt → Facts → Prop
  | mk {env K ss F ns} :
      StmtsOk env K ss F ns → BlockOk env K ss (F.dropNames ns)

end

/-- A function against its signature: the signature's
well-formedness is `checkFn`'s, which checks the body from the
parameters' refinements. -/
inductive FnOk : Env → Fn → Prop
  | mk {env f caps} :
      checkFn env f = .ok caps → FnOk env f

/-- The environment of a program body: the kind in scope. -/
def programEnv (env : Env) (row : KindRow) : Env :=
  { env with kind := some row }

/-- The names of a program's verdict set, if it has one. -/
def verdictNames (p : Program) : Option (List String) :=
  p.verdicts.map (·.map (·.2))

/-- The environment of a handler: the kind, and `reason`. -/
def handlerEnv (env : Env) (row : KindRow) : Env :=
  (programEnv env row).bind
    { name := "reason", ty := tU32, mutable := false, origin := .stack }

def handlerCtx (row : KindRow) (vs : Option (List String)) : Ctx :=
  { mayFail := false, ret := .handler row.verdictTy, inHandler := true,
    verdictSet := vs }

def programCtx (row : KindRow) (vs : Option (List String)) : Ctx :=
  { mayFail := true, ret := .program row.verdictTy, verdictSet := vs }

/-- (Program) and (Handler): the body and every handler from no
facts, every `return` within the verdict set. -/
inductive ProgramOk : Env → Program → Prop
  | mk {env p row} :
      env.prelude.kind? p.kind = some row →
      checkClauses env row p.verdicts p.preserved = .ok () →
      (∀ h ∈ p.handlers, ∃ F,
        BlockOk (handlerEnv env row) (handlerCtx row (verdictNames p))
          h.body F ∧ exits h.body = true) →
      (∃ F, BlockOk (programEnv env row) (programCtx row (verdictNames p))
        p.body F) →
      (row.hasPkt = true → exits p.body = true) →
      ProgramOk env p

/-- A well-typed unit: declarations well-formed, with every predicate
on an array map's value holding of the zero value, functions and
programs well-typed, the call graph acyclic. -/
inductive UnitOk : Prelude → CompUnit → Prop
  | mk {pre u env} :
      env = { prelude := pre, license := u.license.map (·.2), types := u.types,
              consts := u.consts, configs := u.configs, maps := u.maps,
              fns := u.fns, contracts := u.contracts } →
      checkNames u = .ok () →
      (∀ d ∈ u.types, checkTypeDecl env d = .ok ()) →
      (∀ d ∈ u.consts, checkConst env d = .ok ()) →
      (∀ d ∈ u.configs, checkConfig env d = .ok ()) →
      (∀ d ∈ u.maps, checkMap env d = .ok ()) →
      (∀ f ∈ u.fns, FnOk env f) →
      checkCallGraph env u.fns = .ok () →
      (∀ c ∈ u.contracts, checkContract env c = .ok ()) →
      (∀ p ∈ u.programs, ProgramOk env p) →
      UnitOk pre u

/-- Soundness of the checker: a unit `checkUnit` accepts is well-typed.
Stated now, proved after the design settles; the demands rest on
`entails_sound`. -/
theorem check_sound (pre : Prelude) (u : CompUnit) (caps : Caps) :
    checkUnit pre u = .ok caps → UnitOk pre u := by
  sorry

/-- The executable expression typing agrees with the judgment. -/
theorem synth_sound (env : Env) (K : Ctx) (e : Expr) (t : Ty) :
    synth env K e = .ok t → Synth env K e t := by
  sorry

theorem check_expr_sound (env : Env) (K : Ctx) (e : Expr) (t : Ty) :
    check env K e t = .ok () → Check env K e t := by
  sorry

/-- The executable statement checking agrees with the judgment. -/
theorem stmts_sound (env : Env) (K : Ctx) (ss : List Stmt) (F : Facts) :
    checkStmts env K ss = .ok F → BlockOk env K ss F := by
  sorry

end Koit.Check
