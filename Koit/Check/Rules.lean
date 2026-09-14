import Koit.Check.Checker

/-!
The typing judgment of Core as a proposition: the rules of
spec/language.md section 18.3 and the base premises of 18.4, without
the demands `F |= P`, the held set, and the effects, which sessions 3
and 4 add as further premises of the same constructors.

`checkUnit` (Checker.lean) is the decision procedure for this
judgment; `check_sound` states that a unit it accepts is well-typed.
The judgment is declarative where the checker is algorithmic: (Arith)
here takes any integer type both operands check against, and the
checker picks the operand with a type of its own; (Sub) here is
refinement weakening through base-type equality, which is what the
checker decides until entailment arrives. T1, safety, will be stated
on `UnitOk` once the Core semantics of section 19 is defined.

The proofs are deferred, per PLAN.md: definitions, then corpus, then
proofs.
-/

namespace Koit.Check

open Koit (Span)
open Koit.Core

/-- The operations of section 8.1 that (Arith) types. -/
def isCmpBe : CmpOp → Bool
  | .eq | .ne => true
  | _ => false

mutual

/-- `G;K |- e => T` (18.3). -/
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
  /-- An untyped constant takes its type from each use (section 6). -/
  | constUntyped {env K s x d t env'} :
      env.local? x = none → env.const? x = some d → d.ty = none →
      constEnv env x s = .ok env' → Synth env' K d.value t →
      Synth env K (.var s x) t
  /-- The verdict names of the program's kind (section 13). -/
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
  /-- `bool as uN` (section 8.1). -/
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
  /-- `size T` of a sized type, typed as a literal (section 8.4). -/
  | size {env K s t sz} : env.layout t = .ok sz → Synth env K (.size s t) tU64
  /-- The call rule of section 16 for a function of the unit. -/
  | callFn {env K s f args d t} :
      env.fn? f = some d → ArgsOk env K f d.params args →
      (d.fails → K.mayFail) → d.ret = some t →
      (∀ s' t', t ≠ .opt s' t') →
      Synth env K (.call s f args) t
  /-- A prelude call with a signature (sections 6, 13, 16). -/
  | callPrelude {env K s f args row params t} :
      env.fn? f = none → env.prelude.call? f = some row →
      row.acquires = none →
      row.fails = none → row.sig = .fn params (some t) →
      PreludeOk env K s row → ArgsOk env K f params args →
      Synth env K (.call s f args) t
  /-- `errno` in the `else` of a helper call (section 10.5). -/
  | errno {env K s} : K.errnoOk → Synth env K (.errno s) tU32

/-- `G;K |- e <= T` (18.3). -/
inductive Check : Env → Ctx → Expr → Ty → Prop
  /-- (Lit). -/
  | lit {env K s v text t s' signed w} :
      env.norm t = .ok (.int s' signed w) → representable v signed w →
      Check env K (.lit s v text) t
  /-- An untyped constant checked at its use (section 6). -/
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
  /-- (Sub), restricted to refinement weakening: `{v:T | P} <: T`. The
  case `F, P |= Q` is session 3. -/
  | sub {env K e t t'} :
      Synth env K e t' → env.eqv t' t = .ok true → Check env K e t

/-- `G;K |- p : T place [mut]` (18.3), with the origin of the place. -/
inductive PlaceOf : Env → Ctx → Place → PlaceInfo → Prop
  /-- (PVar): a scalar local. -/
  | var {env K s x l} :
      env.local? x = some l → ¬ l.ty.isPlaceTy →
      PlaceOf env K (.var s x)
        { ty := l.ty, mutable := l.mutable, origin := l.origin }
  /-- (PDeref) for a reference named by a binding: `x.f` reads
  through `x` (section 8.2). The guard premise is session 4. -/
  | refVar {env K s x l s' t} :
      env.local? x = some l → l.ty = .ref s' t →
      PlaceOf env K (.var s x) { ty := t, mutable := true, origin := l.origin }
  | viewVar {env K s x l s' t} :
      env.local? x = some l → l.ty = .view s' t →
      PlaceOf env K (.var s x) { ty := t, mutable := true, origin := .pkt }
  | ownVar {env K s x l s' s'' t} :
      env.local? x = some l → l.ty = .own s' (.ref s'' t) →
      PlaceOf env K (.var s x) { ty := t, mutable := true, origin := .kernel }
  /-- A context field, per the kind's table (section 13). -/
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
  /-- (PIndex); the demand `F |= e < n` is session 3. -/
  | index {env K s q i info s' elem n} :
      PlaceOf env K q info → env.norm info.ty = .ok (.array s' elem n) →
      IndexOk env K i →
      PlaceOf env K (.index s q i)
        { ty := elem, mutable := info.mutable, origin := info.origin }
  /-- (PArr) for `array` and `percpu_array`. -/
  | slotArray {env K s m i d n v} :
      env.map? m = some d → d.kind = .array n v → IndexOk env K i →
      PlaceOf env K (.slot s m i) { ty := v, mutable := true, origin := .map m }
  | slotPercpu {env K s m i d n v} :
      env.map? m = some d → d.kind = .percpu n v → IndexOk env K i →
      PlaceOf env K (.slot s m i) { ty := v, mutable := true, origin := .map m }
  /-- (PDeref), explicit, for a scalar pointee (section 8.2). -/
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

/-- An index is an unsigned integer (section 7). -/
inductive IndexOk : Env → Ctx → Expr → Prop
  | poly {env K i} : env.isPoly i → Check env K i tU64 → IndexOk env K i
  | typed {env K i t s w} :
      ¬ env.isPoly i → Synth env K i t →
      env.norm t = .ok (.int s false w) →
      IndexOk env K i

/-- Arguments against parameters (section 16). -/
inductive ArgsOk : Env → Ctx → String → List Param → List Arg → Prop
  | nil {env K f} : ArgsOk env K f [] []
  /-- A scalar parameter takes a value. -/
  | val {env K f p ps e as} :
      (∀ s t, p.ty ≠ .ref s t) → (∀ s t, p.ty ≠ .view s t) →
      (∀ s t, p.ty ≠ .own s t) → Check env K e p.ty →
      ArgsOk env K f ps as →
      ArgsOk env K f (p :: ps) (.val e :: as)
  /-- A scalar parameter takes a scalar place, read. -/
  | scalarPlace {env K f p ps q as info tn pn} :
      (∀ s t, p.ty ≠ .ref s t) → (∀ s t, p.ty ≠ .view s t) →
      (∀ s t, p.ty ≠ .own s t) → PlaceOf env K q info →
      env.norm info.ty = .ok tn → tn.isScalar → env.norm p.ty = .ok pn →
      env.eqv tn pn = .ok true → ArgsOk env K f ps as →
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

/-- A prelude call's availability and license (sections 6, 13). -/
inductive PreludeOk : Env → Ctx → Span → CallRow → Prop
  | mk {env K s row} :
      (row.name.startsWith "pkt." → ∃ r, env.kind = some r ∧ r.hasPkt) →
      (∀ k, env.kind = some k → row.kinds ≠ [] →
        row.kinds.contains k.name) →
      (row.gplOnly → env.gplCompatible) → PreludeOk env K s row

end

/-- What a fallible operation binds (section 8.3), the base premises. -/
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
  /-- A fallible helper (section 8.3). -/
  | call {env K s f args row params ret} :
      env.fn? f = none → env.prelude.call? f = some row →
      row.acquires = none →
      row.fails ≠ none → row.sig = .fn params ret →
      PreludeOk env K s row →
      ArgsOk env K f params args →
      FallibleOk env K (.call s f args) { ty := ret, origin := .stack }
  /-- A function returning `T?` (section 10.8). -/
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
  /-- A spin lock in a map value (section 11.2). -/
  | lock {env K s f t p info s' m} :
      PlaceOf env K p info → env.norm info.ty = .ok (.spinlock s') →
      info.origin = .map m →
      FallibleOk env K (.acquire s .spinlock f t [.place p]) { ty := none }
  | rcu {env K s f t} : FallibleOk env K (.acquire s .rcu f t []) { ty := none }
  | preempt {env K s f t} :
      FallibleOk env K (.acquire s .preempt f t []) { ty := none }
  | irq {env K s f t} : FallibleOk env K (.acquire s .irq f t []) { ty := none }
  /-- A ring-buffer record (section 11.2). -/
  | ringbuf {env K s f s' m t d n sz} :
      env.map? m = some d → d.kind = .ringbuf n →
      env.notRepresentable t false = .ok none → env.layout t = .ok sz →
      FallibleOk env K (.acquire s .ringbuf f (some t) [.map s' m])
        { ty := some (.own s (.ref s t)), origin := .kernel }
  /-- A socket reference, through the acquiring helper's row. -/
  | sockref {env K s f args row params ret} :
      env.prelude.call? f = some row → row.sig = .fn params ret →
      PreludeOk env K s row → ArgsOk env K f params args →
      FallibleOk env K (.acquire s .sockref f none args)
        { ty := ret, origin := .kernel }

/-- A local from what a fallible operation binds. -/
def boundLocal (x : String) (t : Ty) (b : Bound) : Local :=
  { name := x, ty := t, mutable := false, origin := b.origin }

/-- `G;K |- s` (18.4), the base premises, over blocks. -/
inductive StmtsOk : Env → Ctx → List Stmt → Prop
  | nil {env K} : StmtsOk env K []
  /-- A call for its effect (section 9). -/
  | callStmt {env K s s' f args r rest} :
      synthCall env K s' f args false = .ok r → StmtsOk env K rest →
      StmtsOk env K
        (.«let» s false "_" none (.expr (.call s' f args)) :: rest)
  /-- `let x = e` and `var x = e`, a scalar. -/
  | letExpr {env K s m x ty e l rest} :
      x ≠ "_" → bindInit env K s m x ty (.expr e) = .ok l →
      StmtsOk (env.bind l) K rest →
      StmtsOk env K (.«let» s m x ty (.expr e) :: rest)
  /-- `let x = p`: a scalar read, or an aggregate named (section 8.2). -/
  | letPlace {env K s m x ty p l rest} :
      x ≠ "_" → bindInit env K s m x ty (.place p) = .ok l →
      StmtsOk (env.bind l) K rest →
      StmtsOk env K (.«let» s m x ty (.place p) :: rest)
  /-- A struct literal names a stack place (section 8.2). -/
  | letLit {env K s x ty ls fields l rest} :
      x ≠ "_" → bindInit env K s false x ty (.lit ls fields) = .ok l →
      StmtsOk (env.bind l) K rest →
      StmtsOk env K (.«let» s false x ty (.lit ls fields) :: rest)
  /-- (Assign): a mutable scalar place; the store demand is session 3. -/
  | assign {env K s p e info tn rest} :
      PlaceOf env K p info → info.mutable → env.norm info.ty = .ok tn →
      tn.isScalar → Check env K e tn → StmtsOk env K rest →
      StmtsOk env K (.assign s p e :: rest)
  /-- Both branches, also of a constant condition (section 15). -/
  | ite {env K s c t e rest} :
      Check env K c (.bool c.span) → StmtsOk env K t → StmtsOk env K e →
      StmtsOk env K rest → StmtsOk env K (.ite s c t e :: rest)
  /-- (Repeat). -/
  | loop {env K s n body rest} :
      checkCount env K "the count of `repeat`" n = .ok () →
      StmtsOk env { K with inLoop := true } body → StmtsOk env K rest →
      StmtsOk env K (.loop s n body :: rest)
  /-- (For): the index is a `u64`; the cap is session 3. -/
  | «for» {env K s x lo hi body rest} :
      Check env K lo tU64 → Check env K hi tU64 →
      StmtsOk (env.bind { name := x, ty := .int s false 64, mutable := false,
                          origin := .stack }) { K with inLoop := true } body →
      StmtsOk env K rest → StmtsOk env K (.«for» s x lo hi body :: rest)
  | brk {env K s rest} :
      K.inLoop → StmtsOk env K rest → StmtsOk env K (.brk s :: rest)
  | cont {env K s rest} :
      K.inLoop → StmtsOk env K rest → StmtsOk env K (.cont s :: rest)
  /-- (Return). -/
  | ret {env K s v rest} :
      checkRet env K s v = .ok () → StmtsOk env K rest →
      StmtsOk env K (.ret s v :: rest)
  /-- (Mark), (Fail): the context may fail; the reason is a `u32`. -/
  | raise {env K s k r rest} :
      K.mayFail → Check env K r tU32 → StmtsOk env K rest →
      StmtsOk env K (.raise s k r :: rest)
  /-- (Else), (IfLet), (Coerce), (Mark): `try` binds the operation's
  result in the then-branch; a tail's `else` exits. -/
  | «try» {env K s x f thn els ex b t rest} :
      FallibleOk env K f b → b.ty = some t → x ≠ "_" →
      StmtsOk (env.bind (boundLocal x t b)) K thn →
      StmtsOk env { K with errnoOk := fallibleKind env f == .helper } els →
      (ex = true → exits els = true) → StmtsOk env K rest →
      StmtsOk env K (.«try» s x f thn els ex :: rest)
  | tryDiscard {env K s f thn els ex b rest} :
      FallibleOk env K f b → StmtsOk env K thn →
      StmtsOk env { K with errnoOk := fallibleKind env f == .helper } els →
      (ex = true → exits els = true) → StmtsOk env K rest →
      StmtsOk env K (.«try» s "_" f thn els ex :: rest)
  /-- (Hold), scope-only: the held set is session 4. -/
  | holdScope {env K s r acq body row rest} :
      FallibleOk env K acq { ty := none } →
      env.prelude.resource? r = some row →
      row.fails = none → StmtsOk env K body → StmtsOk env K rest →
      StmtsOk env K (.hold s r none acq body none :: rest)
  /-- (Hold), value-yielding, with the tail as `else`. -/
  | holdValue {env K s r x acq body els row b t rest} :
      FallibleOk env K acq b → b.ty = some t →
      env.prelude.resource? r = some row → row.fails ≠ none →
      StmtsOk (env.bind { name := x, ty := t, mutable := false,
                          origin := .kernel }) K body →
      StmtsOk env { K with errnoOk := row.fails == some .helper } els →
      exits els → StmtsOk env K rest →
      StmtsOk env K (.hold s r (some x) acq body (some els) :: rest)
  /-- (Atomic): an integer place in a map value or on the stack. -/
  | atomic {env K s x op p args info tn rest} :
      PlaceOf env K p info → info.mutable → env.norm info.ty = .ok tn →
      tn.isIntTy → (info.origin = .stack ∨ ∃ m, info.origin = .map m) →
      args.length = (if op = .cmpxchg then 2 else 1) →
      (∀ a ∈ args, Check env K a tn) →
      StmtsOk (match x with
               | some n => env.bind { name := n, ty := tn, mutable := false,
                                      origin := .stack }
               | none => env) K rest →
      StmtsOk env K (.atomic s x op p args :: rest)

/-- A function against its signature (section 16): the signature's
well-formedness is `checkFn`'s, the body is `StmtsOk`. -/
inductive FnOk : Env → Fn → Prop
  | mk {env f} :
      checkFn env f = .ok () → FnOk env f

/-- The environment of a program body: the kind in scope. -/
def programEnv (env : Env) (row : KindRow) : Env :=
  { env with kind := some row }

/-- The names of a program's verdict set, if it has one. -/
def verdictNames (p : Program) : Option (List String) :=
  p.verdicts.map (·.map (·.2))

/-- The environment of a handler: the kind, and `reason` (10.6). -/
def handlerEnv (env : Env) (row : KindRow) : Env :=
  (programEnv env row).bind
    { name := "reason", ty := tU32, mutable := false, origin := .stack }

def handlerCtx (row : KindRow) (vs : Option (List String)) : Ctx :=
  { mayFail := false, ret := .handler row.verdictTy, inHandler := true,
    verdictSet := vs }

def programCtx (row : KindRow) (vs : Option (List String)) : Ctx :=
  { mayFail := true, ret := .program row.verdictTy, verdictSet := vs }

/-- (Program) and (Handler), the base premises. -/
inductive ProgramOk : Env → Program → Prop
  | mk {env p row} :
      env.prelude.kind? p.kind = some row →
      checkClauses env row p.verdicts p.preserved = .ok () →
      (∀ h ∈ p.handlers,
        StmtsOk (handlerEnv env row) (handlerCtx row (verdictNames p))
          h.body ∧ exits h.body = true) →
      StmtsOk (programEnv env row) (programCtx row (verdictNames p))
        p.body →
      (row.hasPkt = true → exits p.body = true) →
      ProgramOk env p

/-- A well-typed unit: declarations well-formed, functions and
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
Stated now, proved after the design settles (PLAN.md, "Later"). -/
theorem check_sound (pre : Prelude) (u : CompUnit) :
    checkUnit pre u = .ok () → UnitOk pre u := by
  sorry

/-- The executable expression typing agrees with the judgment. -/
theorem synth_sound (env : Env) (K : Ctx) (e : Expr) (t : Ty) :
    synth env K e = .ok t → Synth env K e t := by
  sorry

theorem check_expr_sound (env : Env) (K : Ctx) (e : Expr) (t : Ty) :
    check env K e t = .ok () → Check env K e t := by
  sorry

end Koit.Check
