import Koit.Core.State

/-!
The dynamic semantics of Core: a big-step relation over the state
of `State.lean`, the subject of the safety theorem. A judgment
relates a state and a phrase to what the phrase produces and the
state after it. A statement produces an outcome: normal completion,
a loop exit, a `return`, a failure on its way to the program's
handler, or an error, the last being what the theorem makes
unreachable. Expressions and fallible operations produce a value or
an abort, since a function they call may fail.

Loops are bounded by their counts and the call graph is acyclic, so
every phrase of a well-typed program has a derivation, and a
big-step relation states the whole run; the continuation frames of
the definition's small-step account are the enclosing rules here: a
`break` is consumed by the `loop` rule, a failure releases each
enclosing `hold` on its way out and is consumed by the program's
handler rule. The relation is parameterized by a kernel, one of the
relations the contracts allow, so a theorem about it holds for every
kernel; the evaluator of `Interp.lean` runs a synthetic one. The
shared state, maps, packet, held stack, and trace, is reached only
through the operations of `Koit.Machine.Ops`, which every level of
the lowering calls, so that a map update or a kernel call is one
definition at every level.
-/

namespace Koit.Core.Sem

open Koit (Span)
open Koit.Core
open Koit.Check (Env UnitOk)
open Koit.Interface (KindDecl CallDecl ResourceDecl AcqArg Sig)
open Koit.Machine (Kernel toNatMod wrap zeros arith compare bswap)

/-- What an expression or a fallible operation produces. -/
abbrev Res (α : Type) := Except Abort α

/-- A primitive of the machine applied in a state. -/
def prim (f : M α) (st : State) : Res (α × State) := f.exec st

/-- The binding a helper's result makes: a place for an owned
reference, a value otherwise. -/
def bindingOf : Val → Binding
  | .loc l => .place l
  | v => .val v

/-- The outcome an abort leaves a statement with. -/
def abortOut : Abort → Outcome
  | .raise k r => .raise k r
  | .err m => .err m
  | .tail p => .tail p

/-- The value an atomic update stores, or none for a `cmpxchg` whose
comparison fails. -/
def atomicResult (op : AtomicOp) (sg : Bool) (w : Nat) (o : Int) (vs : List Val) :
    Option Int :=
  Machine.atomic op sg w o (vs.map fun v => (v.toInt?).getD 0)

mutual

/-- `K ⊢ ⟨e, st⟩ ⇓ r, st'`: the value of an expression, or the abort of
a function it calls. -/
inductive EvalExpr (K : Kernel) : State → Expr → Res Val → State → Prop
  | lit {st s v t} : EvalExpr K st (.lit s v t) (.ok (Val.lit v)) st
  | char {st s c} : EvalExpr K st (.char s c) (.ok (Val.mkInt false 8 c.toNat)) st
  | bool {st s b} : EvalExpr K st (.bool s b) (.ok (.bool b)) st
  | varVal {st s x v} :
      st.local? x = some (.val v) → EvalExpr K st (.var s x) (.ok v) st
  | varPlace {st s x l} :
      st.local? x = some (.place l) → EvalExpr K st (.var s x) (.ok (.loc l)) st
  /-- A constant of the unit, at its declared type or `poly`. -/
  | varConst {st s x d r st'} :
      st.local? x = none → st.env.consts.find? (·.name == x) = some d →
      EvalConst K st d r st' → EvalExpr K st (.var s x) r st'
  /-- A configuration constant: its value for the build. -/
  | varConfig {st s x d e v v' st'} :
      st.local? x = none → st.env.consts.find? (·.name == x) = none →
      st.env.config? x = some d → d.init = some e →
      EvalExpr K st e (.ok v) st' → prim (coerceTo d.ty v) st' = .ok (v', st') →
      EvalExpr K st (.var s x) (.ok v') st'
  /-- A verdict of the program's kind. -/
  | varVerdict {st s x n} :
      st.local? x = none → st.env.consts.find? (·.name == x) = none →
      st.env.config? x = none → st.kind.verdicts.lookup x = some n →
      EvalExpr K st (.var s x) (.ok (Val.u32 n)) st
  | varInterface {st s x d r st'} :
      st.local? x = none → st.env.consts.find? (·.name == x) = none →
      st.env.config? x = none → st.kind.verdicts.lookup x = none →
      st.env.interface.const? x = some d → EvalConst K st d r st' →
      EvalExpr K st (.var s x) r st'
  /-- The total arithmetic of the kernel, the operands meeting at one
  width. -/
  | arith {st s op l r a b st1 st2 sg w x y poly} :
      EvalExpr K st l (.ok a) st1 → EvalExpr K st1 r (.ok b) st2 →
      meetInts a b = some (sg, w, x, y, poly) →
      EvalExpr K st (.arith s op l r) (.ok (.int sg w (arith op sg w x y) poly)) st2
  | arithAbortL {st s op l r e st1} :
      EvalExpr K st l (.error e) st1 → EvalExpr K st (.arith s op l r) (.error e) st1
  | arithAbortR {st s op l r a e st1 st2} :
      EvalExpr K st l (.ok a) st1 → EvalExpr K st1 r (.error e) st2 →
      EvalExpr K st (.arith s op l r) (.error e) st2
  | cmpInt {st s op l r a b st1 st2 sg w x y poly} :
      EvalExpr K st l (.ok a) st1 → EvalExpr K st1 r (.ok b) st2 →
      meetInts a b = some (sg, w, x, y, poly) →
      EvalExpr K st (.cmp s op l r) (.ok (.bool (compare op x y))) st2
  /-- (CmpBe): two patterns at one width, a constant of no width yet
  swapped into the other's. -/
  | cmpBe {st s op l r w w' x y x' y' st1 st2} :
      EvalExpr K st l (.ok (.be w x)) st1 → EvalExpr K st1 r (.ok (.be w' y)) st2 →
      meetBe w x w' y = some (x', y') →
      EvalExpr K st (.cmp s op l r) (.ok (.bool (compare op x' y'))) st2
  | cmpAbortL {st s op l r e st1} :
      EvalExpr K st l (.error e) st1 → EvalExpr K st (.cmp s op l r) (.error e) st1
  | cmpAbortR {st s op l r a e st1 st2} :
      EvalExpr K st l (.ok a) st1 → EvalExpr K st1 r (.error e) st2 →
      EvalExpr K st (.cmp s op l r) (.error e) st2
  | not {st s e v st1} :
      EvalExpr K st e (.ok v) st1 → EvalExpr K st (.not s e) (.ok (.bool (!v.truthy))) st1
  | notAbort {st s e a st1} :
      EvalExpr K st e (.error a) st1 → EvalExpr K st (.not s e) (.error a) st1
  /-- `&&` and `||` evaluate their right operand only when the left
  does not decide them. -/
  | andShort {st s l r v st1} :
      EvalExpr K st l (.ok v) st1 → v.truthy = false →
      EvalExpr K st (.and s l r) (.ok (.bool false)) st1
  | andBoth {st s l r v w st1 st2} :
      EvalExpr K st l (.ok v) st1 → v.truthy = true → EvalExpr K st1 r (.ok w) st2 →
      EvalExpr K st (.and s l r) (.ok (.bool w.truthy)) st2
  | andAbortL {st s l r a st1} :
      EvalExpr K st l (.error a) st1 → EvalExpr K st (.and s l r) (.error a) st1
  | andAbortR {st s l r v a st1 st2} :
      EvalExpr K st l (.ok v) st1 → v.truthy = true → EvalExpr K st1 r (.error a) st2 →
      EvalExpr K st (.and s l r) (.error a) st2
  | orShort {st s l r v st1} :
      EvalExpr K st l (.ok v) st1 → v.truthy = true →
      EvalExpr K st (.or s l r) (.ok (.bool true)) st1
  | orBoth {st s l r v w st1 st2} :
      EvalExpr K st l (.ok v) st1 → v.truthy = false → EvalExpr K st1 r (.ok w) st2 →
      EvalExpr K st (.or s l r) (.ok (.bool w.truthy)) st2
  | orAbortL {st s l r a st1} :
      EvalExpr K st l (.error a) st1 → EvalExpr K st (.or s l r) (.error a) st1
  | orAbortR {st s l r v a st1 st2} :
      EvalExpr K st l (.ok v) st1 → v.truthy = false → EvalExpr K st1 r (.error a) st2 →
      EvalExpr K st (.or s l r) (.error a) st2
  /-- A cast between integer types: truncation, zero extension from
  unsigned, sign extension from signed, as `wrap` does. -/
  | castInt {st s e t x st1 s' sg w p} :
      EvalExpr K st e (.ok (.int s' w x p)) st1 → prim (norm t) st1 = .ok (.int s sg w, st1) →
      EvalExpr K st (.cast s e t) (.ok (Val.mkInt sg w x)) st1
  | castBool {st s e t b st1 sg w} :
      EvalExpr K st e (.ok (.bool b)) st1 → prim (norm t) st1 = .ok (.int s sg w, st1) →
      EvalExpr K st (.cast s e t) (.ok (Val.mkInt sg w (if b then 1 else 0))) st1
  | castAbort {st s e t a st1} :
      EvalExpr K st e (.error a) st1 → EvalExpr K st (.cast s e t) (.error a) st1
  /-- (Hton): the byte swap of a typed operand; a constant of no type
  yet waits for its width. -/
  | hton {st s e sg w x poly st1} :
      EvalExpr K st e (.ok (.int sg w x poly)) st1 →
      EvalExpr K st (.hton s e)
        (.ok (if poly then .be 0 (toNatMod x 64) else .be w (bswap w (toNatMod x w)))) st1
  | htonAbort {st s e a st1} :
      EvalExpr K st e (.error a) st1 → EvalExpr K st (.hton s e) (.error a) st1
  /-- (Ntoh): the byte swap back to a host-order integer. -/
  | ntoh {st s e w x st1} :
      EvalExpr K st e (.ok (.be w x)) st1 →
      EvalExpr K st (.ntoh s e)
        (.ok (if w == 0 then Val.mkInt false 64 x else Val.mkInt false w (bswap w x))) st1
  | ntohAbort {st s e a st1} :
      EvalExpr K st e (.error a) st1 → EvalExpr K st (.ntoh s e) (.error a) st1
  /-- (Read): a scalar place loaded. -/
  | read {st s p r v st1} :
      EvalPlace K st p (.ok r) st1 → prim (loadPlace r) st1 = .ok (v, st1) →
      EvalExpr K st (.read s p) (.ok v) st1
  | readAbort {st s p a st1} :
      EvalPlace K st p (.error a) st1 → EvalExpr K st (.read s p) (.error a) st1
  | size {st s t n} :
      prim (sizeOf t) st = .ok (n, st) → EvalExpr K st (.size s t) (.ok (Val.lit n)) st
  /-- (Move): the reference, with the name dead, so that the scope
  releases nothing; the sink's declaration pops the held entry when it runs. -/
  | move {st s x l} :
      st.local? x = some (.place l) →
      EvalExpr K st (.move s x) (.ok (.loc l)) (st.rebind x .moved)
  | call {st s f args v st1} :
      Call K st s f args (.ok (some v)) st1 →
      EvalExpr K st (.call s f args) (.ok v) st1
  | callAbort {st s f args a st1} :
      Call K st s f args (.error a) st1 → EvalExpr K st (.call s f args) (.error a) st1
  | errno {st s} : EvalExpr K st (.errno s) (.ok (Val.mkInt false 32 st.errno)) st

/-- A constant's value: its expression, fitted to its declared type
when it has one. -/
inductive EvalConst (K : Kernel) : State → ConstDecl → Res Val → State → Prop
  | untyped {st d v st'} :
      d.ty = none → EvalExpr K st d.value (.ok v) st' → EvalConst K st d (.ok v) st'
  | typed {st d t v v' st'} :
      d.ty = some t → EvalExpr K st d.value (.ok v) st' →
      prim (coerceTo t v) st' = .ok (v', st') → EvalConst K st d (.ok v') st'
  | abort {st d a st'} :
      EvalExpr K st d.value (.error a) st' → EvalConst K st d (.error a) st'

/-- The place a place expression denotes. -/
inductive EvalPlace (K : Kernel) : State → Place → Res PlaceRef → State → Prop
  | varLocal {st s x v} :
      st.local? x = some (.val v) → EvalPlace K st (.var s x) (.ok (.local x)) st
  /-- (PDeref) and (PGuard): a name for a place, whose token, for a
  view, is the packet's current one. -/
  | varPlace {st s x l} :
      st.local? x = some (.place l) →
      (l.region.isPkt = true → l.tok = st.layout) →
      EvalPlace K st (.var s x) (.ok (.mem l)) st
  | ctx {st s p f} :
      p = .var s "ctx" → EvalPlace K st (.field s p f) (.ok (.ctx f)) st
  /-- An element of an array context field at a constant index is the
  context field of that element, `user_ip6[2]`, which the kind's
  declaration lists; the index is constant by typing. -/
  | ctxElem {st s s' s'' p f k txt} :
      p = .var s'' "ctx" →
      EvalPlace K st (.index s (.field s' p f) (.lit s k txt)) (.ok (.ctx s!"{f}[{k}]")) st
  | field {st s p f l o ft st1} :
      p ≠ .var s "ctx" → EvalPlace K st p (.ok (.mem l)) st1 →
      prim (fieldOf l.ty f) st1 = .ok ((o, ft), st1) →
      EvalPlace K st (.field s p f) (.ok (.mem { l with off := l.off + o, ty := ft })) st1
  | fieldAbort {st s p f a st1} :
      EvalPlace K st p (.error a) st1 → EvalPlace K st (.field s p f) (.error a) st1
  /-- (PIndex): within the array's bounds. -/
  | index {st s p i l iv idx elem n len esz st1 st2} :
      EvalPlace K st p (.ok (.mem l)) st1 → EvalExpr K st1 i (.ok iv) st2 →
      prim (norm l.ty) st2 = .ok (.array s elem n, st2) →
      prim (constNat n) st2 = .ok (len, st2) → iv.toInt? = some idx →
      0 ≤ idx → idx < len → prim (sizeOf elem) st2 = .ok (esz, st2) →
      EvalPlace K st (.index s p i)
        (.ok (.mem { l with off := l.off + esz * idx.toNat, ty := elem })) st2
  | indexAbort {st s p i a st1} :
      EvalPlace K st p (.error a) st1 → EvalPlace K st (.index s p i) (.error a) st1
  | indexAbortI {st s p i r a st1 st2} :
      EvalPlace K st p (.ok r) st1 → EvalExpr K st1 i (.error a) st2 →
      EvalPlace K st (.index s p i) (.error a) st2
  /-- (PArr): a slot of an array or per-CPU map. -/
  | slot {st s m i iv idx ms st1} :
      EvalExpr K st i (.ok iv) st1 → st1.maps.lookup m = some ms →
      iv.toInt? = some idx → 0 ≤ idx → idx < ms.capacity →
      EvalPlace K st (.slot s m i)
        (.ok (.mem { region := .map m idx.toNat, off := 0, ty := ms.valueTy })) st1
  | slotAbort {st s m i a st1} :
      EvalExpr K st i (.error a) st1 → EvalPlace K st (.slot s m i) (.error a) st1
  | deref {st s x r st1} :
      EvalPlace K st (.var s x) r st1 → EvalPlace K st (.deref s (.var s x)) r st1

/-- The arguments of a call, as the evaluator passes them: a value is
fitted to its parameter's type when the signature is known. -/
inductive EvalArgs (K : Kernel) : State → List Param → List Arg → Res (List Val) → State → Prop
  | nil {st ps} : EvalArgs K st ps [] (.ok []) st
  | val {st ps e v v' rest vs st1 st2} :
      EvalExpr K st e (.ok v) st1 →
      (match ps.head? with
       | some p => prim (coerceTo p.ty v) st1 = .ok (v', st1)
       | none => v' = v) →
      EvalArgs K st1 ps.tail rest (.ok vs) st2 →
      EvalArgs K st ps (.val e :: rest) (.ok (v' :: vs)) st2
  | valAbort {st ps e a rest st1} :
      EvalExpr K st e (.error a) st1 → EvalArgs K st ps (.val e :: rest) (.error a) st1
  | placeMem {st ps p l rest vs st1 st2} :
      EvalPlace K st p (.ok (.mem l)) st1 → scalarRef st1 (.mem l) = false →
      EvalArgs K st1 ps.tail rest (.ok vs) st2 →
      EvalArgs K st ps (.place p :: rest) (.ok (.loc l :: vs)) st2
  | placeScalar {st ps p r v rest vs st1 st2} :
      EvalPlace K st p (.ok r) st1 → scalarRef st1 r = true →
      prim (loadPlace r) st1 = .ok (v, st1) → EvalArgs K st1 ps.tail rest (.ok vs) st2 →
      EvalArgs K st ps (.place p :: rest) (.ok (v :: vs)) st2
  | placeAbort {st ps p a rest st1} :
      EvalPlace K st p (.error a) st1 → EvalArgs K st ps (.place p :: rest) (.error a) st1
  /-- The map of a builtin is no argument; the map pointer of a socket map
  is one, `mapptr m`, where the parameter takes a map pointer. -/
  | map {st ps s m rest r st1} :
      (ps.head?.map fun p => !p.mapPtr.isEmpty) ≠ some true →
      EvalArgs K st ps.tail rest r st1 → EvalArgs K st ps (.map s m :: rest) r st1
  | mapPtrOf {st ps s m rest vs st1} :
      (ps.head?.map fun p => !p.mapPtr.isEmpty) = some true →
      EvalArgs K st ps.tail rest (.ok vs) st1 →
      EvalArgs K st ps (.map s m :: rest) (.ok (.mapPtr m :: vs)) st1
  | mapPtrAbort {st ps s m rest a st1} :
      (ps.head?.map fun p => !p.mapPtr.isEmpty) = some true →
      EvalArgs K st ps.tail rest (.error a) st1 →
      EvalArgs K st ps (.map s m :: rest) (.error a) st1

/-- A call by name: a function of the unit, a builtin, or a kernel
function through the kernel. -/
inductive Call (K : Kernel) : State → Span → String → List Arg → Res (Option Val) → State → Prop
  | fn {st s f args d r st1} :
      st.env.fn? f = some d → ExecFn K st d args r st1 → Call K st s f args r st1
  | builtin {st s f args decl r st1} :
      st.env.fn? f = none → st.env.interface.call? f = some decl → decl.sig = .builtin →
      Builtin K st s f args r st1 → Call K st s f args r st1
  /-- A kernel function: what the kernel does on the arguments,
  through the machine, which appends the trace event and pushes or
  pops the held stack per the declaration. -/
  | helper {st s f args decl params ret vs v st1 st2} :
      st.env.fn? f = none → st.env.interface.call? f = some decl → decl.sig = .fn params ret →
      EvalArgs K st params args (.ok vs) st1 →
      prim (kernelCall K decl params ret vs) st1 = .ok (some v, st2) →
      Call K st s f args (.ok v) st2
  | helperArgsAbort {st s f args decl params ret a st1} :
      st.env.fn? f = none → st.env.interface.call? f = some decl → decl.sig = .fn params ret →
      EvalArgs K st params args (.error a) st1 → Call K st s f args (.error a) st1

/-- The builtins: `copy`, `fill`, `insert`, `delete`, `printk`. -/
inductive Builtin (K : Kernel) : State → Span → String → List Arg → Res (Option Val) → State → Prop
  | copy {st s dst src d sr n st1 st2} :
      EvalPlace K st dst (.ok (.mem d)) st1 → EvalPlace K st1 src (.ok (.mem sr)) st2 →
      prim (sizeOf d.ty) st2 = .ok (n, st2) →
      Builtin K st s "copy" [.place dst, .place src] (.ok none)
        (st2.writeAt d (st2.bytesAt sr n))
  | fill {st s dst b d v n st1 st2} :
      EvalPlace K st dst (.ok (.mem d)) st1 → EvalExpr K st1 b (.ok v) st2 →
      prim (sizeOf d.ty) st2 = .ok (n, st2) →
      Builtin K st s "fill" [.place dst, .val b] (.ok none)
        (st2.writeAt d (List.replicate n (UInt8.ofNat (toNatMod ((v.toInt?).getD 0) 8))))
  /-- `insert`: the machine's update, which replaces a present key,
  adds a new one while the map has room, and answers with the
  kernel's `E2BIG` otherwise, which is the failure of kind `helper`. -/
  | insert {st s sp m k v ms kr vr kb vb st1 st2 st3} :
      st.maps.lookup m = some ms →
      EvalPlace K st k (.ok kr) st1 → prim (bytesOfPlace kr ms.keySize) st1 = .ok (kb, st1) →
      EvalPlace K st1 v (.ok vr) st2 → prim (bytesOfPlace vr ms.valueSize) st2 = .ok (vb, st2) →
      prim (op (Machine.update m kb vb)) st2 = .ok (0, st3) →
      Builtin K st s "insert" [.map sp m, .place k, .place v] (.ok none) st3
  | insertFull {st s sp m k v ms kr vr kb vb rc st1 st2 st3} :
      st.maps.lookup m = some ms →
      EvalPlace K st k (.ok kr) st1 → prim (bytesOfPlace kr ms.keySize) st1 = .ok (kb, st1) →
      EvalPlace K st1 v (.ok vr) st2 → prim (bytesOfPlace vr ms.valueSize) st2 = .ok (vb, st2) →
      prim (op (Machine.update m kb vb)) st2 = .ok (rc, st3) → rc ≠ 0 →
      Builtin K st s "insert" [.map sp m, .place k, .place v]
        (.error (.raise .failed_call (toNatMod rc 32))) st3
  /-- `delete`: the machine's delete, or the kernel's `ENOENT`. -/
  | delete {st s sp m k ms kr kb st1 st2} :
      st.maps.lookup m = some ms →
      EvalPlace K st k (.ok kr) st1 → prim (bytesOfPlace kr ms.keySize) st1 = .ok (kb, st1) →
      prim (op (Machine.delete m kb)) st1 = .ok (0, st2) →
      Builtin K st s "delete" [.map sp m, .place k] (.ok none) st2
  | deleteAbsent {st s sp m k ms kr kb rc st1 st2} :
      st.maps.lookup m = some ms →
      EvalPlace K st k (.ok kr) st1 → prim (bytesOfPlace kr ms.keySize) st1 = .ok (kb, st1) →
      prim (op (Machine.delete m kb)) st1 = .ok (rc, st2) → rc ≠ 0 →
      Builtin K st s "delete" [.map sp m, .place k]
        (.error (.raise .failed_call (toNatMod rc 32))) st2
  /-- `printk`: an event on the trace, its arguments as the kernel
  sees them. -/
  | printk {st s s' fmt rest vs st1} :
      EvalArgs K st [] rest (.ok vs) st1 →
      Builtin K st s "printk" (.val (.str s' fmt) :: rest) (.ok none)
        (st1.record (.print fmt (vs.map fun v => (settle v).observe)))

/-- A function of the unit: the arguments bound in a fresh frame, the
body run, its `return` the result, the caller's frame restored. -/
inductive ExecFn (K : Kernel) : State → Fn → List Arg → Res (Option Val) → State → Prop
  | ret {st d args frame o st1 st2 v} :
      Frame K st d.params args (.ok frame) st1 →
      ExecBlock K { st1 with locals := frame } d.body o st2 →
      (o = .ret v ∨ (o = .normal ∧ v = none)) →
      ExecFn K st d args (.ok v) { st2 with locals := st.locals }
  | raise {st d args frame k r st1 st2} :
      Frame K st d.params args (.ok frame) st1 →
      ExecBlock K { st1 with locals := frame } d.body (.raise k r) st2 →
      ExecFn K st d args (.error (.raise k r)) { st2 with locals := st.locals }
  | argsAbort {st d args a st1} :
      Frame K st d.params args (.error a) st1 → ExecFn K st d args (.error a) st1

/-- The frame of a call from its parameters and arguments. -/
inductive Frame (K : Kernel) :
    State → List Param → List Arg → Res (List (String × Binding)) → State → Prop
  | nil {st ps} : Frame K st ps [] (.ok []) st
  | place {st p ps q l rest frame st1 st2 tn} :
      prim (norm p.ty) st = .ok (tn, st) → (tn matches .ref .. | .view ..) →
      EvalPlace K st q (.ok (.mem l)) st1 → Frame K st1 ps rest (.ok frame) st2 →
      Frame K st (p :: ps) (.place q :: rest) (.ok ((p.name, .place l) :: frame)) st2
  | own {st p ps e l rest frame st1 st2 tn} :
      prim (norm p.ty) st = .ok (tn, st) → (tn matches .own ..) →
      EvalExpr K st e (.ok (.loc l)) st1 → Frame K st1 ps rest (.ok frame) st2 →
      Frame K st (p :: ps) (.val e :: rest) (.ok ((p.name, .place l) :: frame)) st2
  | scalar {st p ps e v v' rest frame st1 st2 tn} :
      prim (norm p.ty) st = .ok (tn, st) → ¬ (tn matches .ref .. | .view .. | .own ..) →
      EvalExpr K st e (.ok v) st1 → prim (coerceTo tn v) st1 = .ok (v', st1) →
      Frame K st1 ps rest (.ok frame) st2 →
      Frame K st (p :: ps) (.val e :: rest) (.ok ((p.name, .val v') :: frame)) st2
  | scalarPlace {st p ps q r v v' rest frame st1 st2 tn} :
      prim (norm p.ty) st = .ok (tn, st) → ¬ (tn matches .ref .. | .view .. | .own ..) →
      EvalPlace K st q (.ok r) st1 → prim (loadPlace r) st1 = .ok (v, st1) →
      prim (coerceTo tn v) st1 = .ok (v', st1) → Frame K st1 ps rest (.ok frame) st2 →
      Frame K st (p :: ps) (.place q :: rest) (.ok ((p.name, .val v') :: frame)) st2
  | abortVal {st p ps e a rest st1} :
      EvalExpr K st e (.error a) st1 → Frame K st (p :: ps) (.val e :: rest) (.error a) st1
  | abortPlace {st p ps q a rest st1} :
      EvalPlace K st q (.error a) st1 → Frame K st (p :: ps) (.place q :: rest) (.error a) st1

/-- A fallible operation: what it binds, `none` for its failure, or
an abort. -/
inductive ExecFall (K : Kernel) :
    State → Fallible → Res (Option (Option Binding)) → State → Prop
  /-- (View): the window lies in the packet; the location carries the
  layout token it was carved under. -/
  | viewOk {st s off t o ov n st1} :
      EvalExpr K st off (.ok o) st1 → o.toInt? = some ov → prim (sizeOf t) st1 = .ok (n, st1) →
      0 ≤ ov → ov.toNat + n ≤ st1.packet.size →
      ExecFall K st (.view s off t)
        (.ok (some (some (.place { region := .pkt, off := ov.toNat, ty := t,
                                   tok := st1.layout })))) st1
  | viewShort {st s off t o ov n st1} :
      EvalExpr K st off (.ok o) st1 → o.toInt? = some ov → prim (sizeOf t) st1 = .ok (n, st1) →
      (ov < 0 ∨ ov.toNat + n > st1.packet.size) →
      ExecFall K st (.view s off t) (.ok none) st1
  | viewAbort {st s off t a st1} :
      EvalExpr K st off (.error a) st1 → ExecFall K st (.view s off t) (.error a) st1
  /-- (Lookup): the machine's lookup with the key's bytes, the entry's
  location or the kernel's null. -/
  | lookupFound {st s m k ms kr kb r st1} :
      st.maps.lookup m = some ms → EvalPlace K st k (.ok kr) st1 →
      prim (bytesOfPlace kr ms.keySize) st1 = .ok (kb, st1) →
      prim (op (Machine.lookup m kb)) st1 = .ok (some r, st1) →
      ExecFall K st (.lookup s m k)
        (.ok (some (some (.place { region := .shared r, off := 0, ty := ms.valueTy })))) st1
  | lookupMissing {st s m k ms kr kb st1} :
      st.maps.lookup m = some ms → EvalPlace K st k (.ok kr) st1 →
      prim (bytesOfPlace kr ms.keySize) st1 = .ok (kb, st1) →
      prim (op (Machine.lookup m kb)) st1 = .ok (none, st1) →
      ExecFall K st (.lookup s m k) (.ok none) st1
  /-- (LoadW): the field's predicate of the value loaded, with the
  siblings read from the place. -/
  | loadw {st s q f fields pred v ok frame fl l st1 st3} :
      EvalPlace K st q (.ok (.mem l)) st1 →
      prim (fieldOf l.ty f) st1 = .ok ((fl.off - l.off, fl.ty), st1) →
      fl.region = l.region → fl.tok = l.tok →
      prim (loadPlace (.mem fl)) st1 = .ok (v, st1) →
      prim (norm l.ty) st1 = .ok (.struct s fields, st1) →
      (fields.find? (·.name == f)).bind (·.pred) = some pred →
      prim (siblingFrame l fields f v) st1 = .ok (frame, st1) →
      EvalExpr K { st1 with locals := frame } pred (.ok ok) st3 →
      ExecFall K st (.loadw s (.field s q f))
        (.ok (if ok.truthy then some (some (.val v)) else none))
        { st3 with locals := st1.locals }
  /-- A fallible helper: the kernel's answer through the machine,
  with `errno` on a failure. -/
  | callOk {st s f args decl params ret vs v st1 st2} :
      st.env.interface.call? f = some decl → decl.sig = .fn params ret →
      EvalArgs K st params args (.ok vs) st1 →
      prim (kernelCall K decl params ret vs) st1 = .ok (some v, st2) →
      ExecFall K st (.call s f args) (.ok (some (v.map bindingOf))) st2
  | callFailed {st s f args decl params ret vs st1 st2} :
      st.env.interface.call? f = some decl → decl.sig = .fn params ret →
      EvalArgs K st params args (.ok vs) st1 →
      prim (kernelCall K decl params ret vs) st1 = .ok (none, st2) →
      ExecFall K st (.call s f args) (.ok none) st2
  | callBuiltinOk {st s f args decl v st1} :
      st.env.interface.call? f = some decl → decl.sig = .builtin →
      Builtin K st s f args (.ok v) st1 →
      ExecFall K st (.call s f args) (.ok (some (v.map .val))) st1
  | callBuiltinFailed {st s f args decl r st1} :
      st.env.interface.call? f = some decl → decl.sig = .builtin →
      Builtin K st s f args (.error (.raise .failed_call r)) st1 →
      ExecFall K st (.call s f args) (.ok none) { st1 with errno := wrap true 32 r }
  | callAbort {st s f args decl params ret a st1} :
      st.env.interface.call? f = some decl → decl.sig = .fn params ret →
      EvalArgs K st params args (.error a) st1 → ExecFall K st (.call s f args) (.error a) st1
  /-- A `T?` function: a value, or absence from a bare `return`. -/
  | callopt {st s f args d v st1} :
      st.env.fn? f = some d → ExecFn K st d args (.ok v) st1 →
      ExecFall K st (.callopt s f args) (.ok (v.map fun v => some (.val v))) st1
  | calloptAbort {st s f args d a st1} :
      st.env.fn? f = some d → ExecFn K st d args (.error a) st1 →
      ExecFall K st (.callopt s f args) (.error a) st1
  /-- (Tail, not taken): the slot empty or the limit reached, the
  operation fails; the taken case is a statement outcome (below). -/
  | tailNotTaken {st s m i v st1} :
      EvalExpr K st i (.ok v) st1 →
      (Machine.tailCall m (toNatMod ((v.toInt?).getD 0) 32)).exec st1.machine = .ok (false, st1.machine) →
      ExecFall K st (.tail s m i) (.ok none) st1
  | tailAbort {st s m i a st1} :
      EvalExpr K st i (.error a) st1 → ExecFall K st (.tail s m i) (.error a) st1
  /-- (Coerce): the predicate of the value, under the refined name. -/
  | coerce {st s e t x base pred v ok st1 st2} :
      t = .refined s x base pred → EvalExpr K st e (.ok v) st1 →
      EvalExpr K (st1.bind x (.val v)) pred (.ok ok) st2 →
      ExecFall K st (.coerce s e t)
        (.ok (if ok.truthy then some (some (.val v)) else none))
        { st2 with locals := st1.locals }
  | coerceAbort {st s e t a st1} :
      EvalExpr K st e (.error a) st1 → ExecFall K st (.coerce s e t) (.error a) st1
  /-- (Hold-in) for a lock: the slot's place, then the lock taken on
  the machine, which refuses one while another is held. -/
  | acquirePlace {st s r f ty p decl slot l obj st1 st2} :
      st.env.interface.resource? r = some decl → decl.arg = .place slot →
      EvalPlace K st p (.ok (.mem l)) st1 → l.heldObj = some obj →
      prim (op (Machine.lock decl obj)) st1 = .ok ((), st2) →
      ExecFall K st (.acquire s r f ty [.place p]) (.ok (some none)) st2
  | acquireScope {st s r f ty decl st1} :
      st.env.interface.resource? r = some decl → decl.arg = .scope →
      prim (op (Machine.enter decl)) st = .ok ((), st1) →
      ExecFall K st (.acquire s r f ty []) (.ok (some none)) st1
  /-- A ring-buffer record: a fresh kernel object of the record's
  size while the ring has room, held. -/
  | reserveOk {st s r sp m t decl n id st1} :
      st.env.interface.resource? r = some decl → decl.arg = .call →
      prim (sizeOf t) st = .ok (n, st) →
      prim (op (Machine.reserve decl m n)) st = .ok (some id, st1) →
      ExecFall K st (.acquire s r "reserve" (some t) [.map sp m])
        (.ok (some (some (.place { region := .kernel id, off := 0, ty := t })))) st1
  | reserveFull {st s r sp m t decl n st1} :
      st.env.interface.resource? r = some decl → decl.arg = .call →
      prim (sizeOf t) st = .ok (n, st) →
      prim (op (Machine.reserve decl m n)) st = .ok (none, st1) →
      ExecFall K st (.acquire s r "reserve" (some t) [.map sp m]) (.ok none)
        { st1 with errno := -12 }
  /-- An acquiring kernel function: its owned result, which the call
  through the machine has already pushed on the held stack. -/
  | acquireCall {st s r f args decl l st1} :
      st.env.interface.resource? r = some decl → decl.arg = .call → f ≠ "reserve" →
      ExecFall K st (.call s f args) (.ok (some (some (.place l)))) st1 →
      ExecFall K st (.acquire s r f none args) (.ok (some (some (.place l)))) st1
  | acquireCallFailed {st s r f args decl st1} :
      st.env.interface.resource? r = some decl → decl.arg = .call → f ≠ "reserve" →
      ExecFall K st (.call s f args) (.ok none) st1 →
      ExecFall K st (.acquire s r f none args) (.ok none) st1

/-- `K ⊢ ⟨s, st⟩ ⇓ o, st'`: one statement. -/
inductive ExecStmt (K : Kernel) : State → Stmt → Outcome → State → Prop
  /-- A call for its effect. -/
  | callStmt {st s s' f args v st1} :
      Call K st s' f args (.ok v) st1 →
      ExecStmt K st (.«let» s false "_" none (.expr (.call s' f args))) .normal st1
  | callStmtAbort {st s s' f args a st1} :
      Call K st s' f args (.error a) st1 →
      ExecStmt K st (.«let» s false "_" none (.expr (.call s' f args))) (abortOut a) st1
  /-- `let x = e`: the value, at the declared type or settled. -/
  | letExpr {st s m x ty e v v' st1} :
      x ≠ "_" → EvalExpr K st e (.ok v) st1 →
      (match ty with
       | some t => prim (coerceTo t v) st1 = .ok (v', st1)
       | none => v' = settle v) →
      ExecStmt K st (.«let» s m x ty (.expr e)) .normal (st1.bind x (.val v'))
  | letExprAbort {st s m x ty e a st1} :
      x ≠ "_" → EvalExpr K st e (.error a) st1 →
      ExecStmt K st (.«let» s m x ty (.expr e)) (abortOut a) st1
  /-- (Read) into a name for a scalar place. -/
  | letScalar {st s m x ty p l tn v v' st1} :
      EvalPlace K st p (.ok (.mem l)) st1 → prim (norm l.ty) st1 = .ok (tn, st1) →
      tn.isScalar = true → prim (loadPlace (.mem l)) st1 = .ok (v, st1) →
      (match ty with
       | some t => prim (coerceTo t v) st1 = .ok (v', st1)
       | none => v' = v) →
      ExecStmt K st (.«let» s m x ty (.place p)) .normal (st1.bind x (.val v'))
  | letLocal {st s m x ty p r v st1} :
      EvalPlace K st p (.ok r) st1 → (∀ l, r ≠ .mem l) →
      prim (loadPlace r) st1 = .ok (v, st1) →
      ExecStmt K st (.«let» s m x ty (.place p)) .normal (st1.bind x (.val v))
  /-- (P3): an aggregate place is named. -/
  | letPlace {st s m x ty p l tn st1} :
      EvalPlace K st p (.ok (.mem l)) st1 → prim (norm l.ty) st1 = .ok (tn, st1) →
      tn.isScalar = false →
      ExecStmt K st (.«let» s m x ty (.place p)) .normal (st1.bind x (.place l))
  | letPlaceAbort {st s m x ty p a st1} :
      EvalPlace K st p (.error a) st1 →
      ExecStmt K st (.«let» s m x ty (.place p)) (abortOut a) st1
  /-- A struct literal: a fresh stack region, its fields stored. -/
  | letLit {st s m x ty ls fields t n id st1 st2} :
      prim (lift (Koit.Check.structForLiteral st.env ls ty fields)) st = .ok (t, st) →
      prim (sizeOf t) st = .ok (n, st) → st.freshStack = (id, st1) →
      StoreFields K (st1.setRegion (.stack id) (zeros n))
        { region := .stack id, off := 0, ty := t } t fields (.ok ()) st2 →
      ExecStmt K st (.«let» s m x ty (.lit ls fields)) .normal
        (st2.bind x (.place { region := .stack id, off := 0, ty := t }))
  /-- (Assign), (Store): the value, then the place. -/
  | assign {st s p e v r st1 st2 st3} :
      EvalExpr K st e (.ok v) st1 → EvalPlace K st1 p (.ok r) st2 →
      prim (storePlace r v) st2 = .ok ((), st3) →
      ExecStmt K st (.assign s p e) .normal st3
  | assignAbortE {st s p e a st1} :
      EvalExpr K st e (.error a) st1 → ExecStmt K st (.assign s p e) (abortOut a) st1
  | assignAbortP {st s p e v a st1 st2} :
      EvalExpr K st e (.ok v) st1 → EvalPlace K st1 p (.error a) st2 →
      ExecStmt K st (.assign s p e) (abortOut a) st2
  | iteT {st s c t e v o st1 st2} :
      EvalExpr K st c (.ok v) st1 → v.truthy = true → ExecBlock K st1 t o st2 →
      ExecStmt K st (.ite s c t e) o st2
  | iteF {st s c t e v o st1 st2} :
      EvalExpr K st c (.ok v) st1 → v.truthy = false → ExecBlock K st1 e o st2 →
      ExecStmt K st (.ite s c t e) o st2
  | iteAbort {st s c t e a st1} :
      EvalExpr K st c (.error a) st1 → ExecStmt K st (.ite s c t e) (abortOut a) st1
  /-- (Loop): the body its count's number of times. -/
  | loop {st s n body v k o st1 st2} :
      EvalExpr K st n (.ok v) st1 → v.toInt? = some k →
      ExecLoop K st1 k.toNat body o st2 → ExecStmt K st (.loop s n body) o st2
  | loopAbort {st s n body a st1} :
      EvalExpr K st n (.error a) st1 → ExecStmt K st (.loop s n body) (abortOut a) st1
  | «for» {st s x lo hi body a b av bv o st1 st2 st3} :
      EvalExpr K st lo (.ok a) st1 → EvalExpr K st1 hi (.ok b) st2 →
      a.toInt? = some av → b.toInt? = some bv →
      ExecFor K st2 x av bv body o st3 → ExecStmt K st (.«for» s x lo hi body) o st3
  | forAbortLo {st s x lo hi body a st1} :
      EvalExpr K st lo (.error a) st1 →
      ExecStmt K st (.«for» s x lo hi body) (abortOut a) st1
  | forAbortHi {st s x lo hi body v a st1 st2} :
      EvalExpr K st lo (.ok v) st1 → EvalExpr K st1 hi (.error a) st2 →
      ExecStmt K st (.«for» s x lo hi body) (abortOut a) st2
  | brk {st s} : ExecStmt K st (.brk s) .brk st
  | cont {st s} : ExecStmt K st (.cont s) .cont st
  | retVal {st s e v st1} :
      EvalExpr K st e (.ok v) st1 → ExecStmt K st (.ret s (some e)) (.ret (some v)) st1
  | retAbort {st s e a st1} :
      EvalExpr K st e (.error a) st1 → ExecStmt K st (.ret s (some e)) (abortOut a) st1
  | retNone {st s} : ExecStmt K st (.ret s none) (.ret none) st
  /-- (Raise): the failure with its reason. -/
  | raise {st s k r v st1} :
      EvalExpr K st r (.ok v) st1 →
      ExecStmt K st (.raise s k r) (.raise k (toNatMod ((v.toInt?).getD 0) 32)) st1
  | raiseAbort {st s k r a st1} :
      EvalExpr K st r (.error a) st1 → ExecStmt K st (.raise s k r) (abortOut a) st1
  /-- (Try-ok): the then-branch with the result bound. -/
  | tryOk {st s x f thn els ex b o st1 st2} :
      ExecFall K st f (.ok (some b)) st1 →
      ExecBlock K (match x, b with
                   | "_", _ => st1
                   | _, none => st1
                   | x, some b => st1.bind x b) thn o st2 →
      ExecStmt K st (.«try» s x f thn els ex) o (st2.dropLocalsTo st1.locals.length)
  /-- (Try-fail): the else-branch. -/
  | tryFail {st s x f thn els ex o st1 st2} :
      ExecFall K st f (.ok none) st1 → ExecBlock K st1 els o st2 →
      ExecStmt K st (.«try» s x f thn els ex) o st2
  | tryAbort {st s x f thn els ex a st1} :
      ExecFall K st f (.error a) st1 → ExecStmt K st (.«try» s x f thn els ex) (abortOut a) st1
  /-- (Tail, taken): the program named by the slot runs in this one's
  place; the statement's outcome is that program, for the driver. -/
  | tailTaken {st s x m i thn els ex v p st1 mach} :
      EvalExpr K st i (.ok v) st1 →
      (Machine.tailCall m (toNatMod ((v.toInt?).getD 0) 32)).exec st1.machine = .ok (true, mach) →
      mach.tailTo = some p →
      ExecStmt K st (.«try» s x (.tail s m i) thn els ex) (.tail p) { st1 with machine := mach }
  /-- (Hold-in), then (Hold-out) or the abnormal release: the body under
  the resource, released on the machine normally when the body
  completes and abnormally on any other exit, unless `move` took it. -/
  | hold {st s r x acq body els b o st1 st2 st3} :
      ExecFall K st acq (.ok (some b)) st1 →
      ExecBlock K (match x, b with
                   | some x, some b => st1.bind x b
                   | _, _ => st1) body o st2 →
      prim (release K (o matches .normal) (st2.moved x)) st2 = .ok ((), st3) →
      ExecStmt K st (.hold s r x acq body els) o (st3.dropLocalsTo st1.locals.length)
  | holdReleaseErr {st s r x acq body els b o m st1 st2} :
      ExecFall K st acq (.ok (some b)) st1 →
      ExecBlock K (match x, b with
                   | some x, some b => st1.bind x b
                   | _, _ => st1) body o st2 →
      prim (release K (o matches .normal) (st2.moved x)) st2 = .error (.err m) →
      ExecStmt K st (.hold s r x acq body els) (.err m) st2
  | holdFail {st s r x acq body els e o st1 st2} :
      ExecFall K st acq (.ok none) st1 → els = some e → ExecBlock K st1 e o st2 →
      ExecStmt K st (.hold s r x acq body els) o st2
  | holdAbort {st s r x acq body els a st1} :
      ExecFall K st acq (.error a) st1 →
      ExecStmt K st (.hold s r x acq body els) (abortOut a) st1
  /-- (Atomic): the read-modify-write, indivisible, the previous value
  bound if asked. -/
  | atomic {st s x op p args r old o sg w vs new st1 st2 st3} :
      EvalPlace K st p (.ok r) st1 → prim (loadPlace r) st1 = .ok (old, st1) →
      old = .int sg w o false → EvalArgs K st1 [] (args.map .val) (.ok vs) st2 →
      new = atomicResult op sg w o vs →
      (match new with
       | some v => prim (storePlace r (Val.mkInt sg w v)) st2 = .ok ((), st3)
       | none => st3 = st2) →
      ExecStmt K st (.atomic s x op p args) .normal
        (match x with
         | some x => st3.bind x (.val old)
         | none => st3)

/-- The fields of a struct literal stored in order. -/
inductive StoreFields (K : Kernel) :
    State → Loc → Ty → List FieldInit → Res Unit → State → Prop
  | nil {st l t} : StoreFields K st l t [] (.ok ()) st
  | cons {st l t fi rest o ft v st1 st2 st3} :
      prim (fieldOf t fi.name) st = .ok ((o, ft), st) →
      EvalExpr K st fi.value (.ok v) st1 →
      prim (storePlace (.mem { l with off := o, ty := ft }) v) st1 = .ok ((), st2) →
      StoreFields K st2 l t rest (.ok ()) st3 →
      StoreFields K st l t (fi :: rest) (.ok ()) st3
  | abort {st l t fi rest a st1} :
      EvalExpr K st fi.value (.error a) st1 →
      StoreFields K st l t (fi :: rest) (.error a) st1

/-- A block: its statements, its locals dropped after. -/
inductive ExecBlock (K : Kernel) : State → List Stmt → Outcome → State → Prop
  | mk {st ss o st1} :
      ExecStmts K st ss o st1 → ExecBlock K st ss o (st1.dropLocalsTo st.locals.length)

inductive ExecStmts (K : Kernel) : State → List Stmt → Outcome → State → Prop
  | nil {st} : ExecStmts K st [] .normal st
  | consNormal {st s rest o st1 st2} :
      ExecStmt K st s .normal st1 → ExecStmts K st1 rest o st2 →
      ExecStmts K st (s :: rest) o st2
  | consExit {st s rest o st1} :
      ExecStmt K st s o st1 → o ≠ .normal → ExecStmts K st (s :: rest) o st1

/-- (Loop), (LoopNext): `n` iterations, `break` ending the loop and
`continue` the iteration. -/
inductive ExecLoop (K : Kernel) : State → Nat → List Stmt → Outcome → State → Prop
  | zero {st body} : ExecLoop K st 0 body .normal st
  | next {st k body o st1 st2} :
      ExecBlock K st body o st1 → (o = .normal ∨ o = .cont) →
      ExecLoop K st1 k body .normal st2 → ExecLoop K st (k + 1) body .normal st2
  | brk {st k body st1} :
      ExecBlock K st body .brk st1 → ExecLoop K st (k + 1) body .normal st1
  | exit {st k body o st1} :
      ExecBlock K st body o st1 → (o matches .ret _ | .raise .. | .err _) →
      ExecLoop K st (k + 1) body o st1

/-- (For): the index a `u64` local of each iteration. -/
inductive ExecFor (K : Kernel) : State → String → Int → Int → List Stmt → Outcome → State → Prop
  | done {st x i b body} : i ≥ b → ExecFor K st x i b body .normal st
  | next {st x i b body o st1 st2} :
      i < b → ExecBlock K (st.bind x (.val (Val.mkInt false 64 i))) body o st1 →
      (o = .normal ∨ o = .cont) →
      ExecFor K (st1.dropLocalsTo st.locals.length) x (i + 1) b body .normal st2 →
      ExecFor K st x i b body .normal st2
  | brk {st x i b body st1} :
      i < b → ExecBlock K (st.bind x (.val (Val.mkInt false 64 i))) body .brk st1 →
      ExecFor K st x i b body .normal (st1.dropLocalsTo st.locals.length)
  | exit {st x i b body o st1} :
      i < b → ExecBlock K (st.bind x (.val (Val.mkInt false 64 i))) body o st1 →
      (o matches .ret _ | .raise .. | .err _) →
      ExecFor K st x i b body o (st1.dropLocalsTo st.locals.length)

end

/-! ### Programs -/

/-- How a program's run ends. -/
inductive ProgOut where
  | halt (v : Val)
  | err (msg : String)
  deriving Repr, Inhabited

/-- (Return) and (Raise): the body's `return` halts; a failure runs
the handler of its kind with `reason` bound and nothing held, whose
`return` halts; a `syscall` body falling off its end returns 0. -/
inductive ExecProgram (K : Kernel) : State → Program → ProgOut → State → Prop
  | ret {st p v v' st1} :
      ExecBlock K st p.body (.ret (some v)) st1 → st1.held = [] →
      prim (coerceTo st.kind.verdictTy v) st1 = .ok (v', st1) →
      ExecProgram K st p (.halt v') st1
  | fallOff {st p st1} :
      ExecBlock K st p.body .normal st1 → st.kind.hasPkt = false → st1.held = [] →
      ExecProgram K st p (.halt (Val.mkInt true 32 0)) st1
  | handled {st p k reason h v v' st1 st2} :
      ExecBlock K st p.body (.raise k reason) st1 → st1.held = [] →
      p.handlers.find? (·.kind == k) = some h →
      ExecBlock K { st1 with locals := [("reason", .val (Val.u32 reason))] }
        h.body (.ret (some v)) st2 →
      prim (coerceTo st.kind.verdictTy v) st2 = .ok (v', st2) →
      ExecProgram K st p (.halt v') st2
  | bodyErr {st p m st1} :
      ExecBlock K st p.body (.err m) st1 → ExecProgram K st p (.err m) st1
  /-- Every `hold` released on the way out, so nothing is held at the
  exit; a state that still holds something is an error. -/
  | heldAtExit {st p o st1} :
      ExecBlock K st p.body o st1 → (o matches .ret _ | .raise .. | .normal) →
      st1.held ≠ [] →
      ExecProgram K st p (.err "the program exits holding a resource") st1
  | bodyStuck {st p o st1} :
      ExecBlock K st p.body o st1 → (o matches .brk | .cont | .ret none) →
      ExecProgram K st p (.err "the body ends outside a loop or without a verdict") st1
  | fallOffPacket {st p st1} :
      ExecBlock K st p.body .normal st1 → st.kind.hasPkt = true →
      ExecProgram K st p (.err "the body fell off its end") st1
  | handlerErr {st p k reason h o st1 st2} :
      ExecBlock K st p.body (.raise k reason) st1 → st1.held = [] →
      p.handlers.find? (·.kind == k) = some h →
      ExecBlock K { st1 with locals := [("reason", .val (Val.u32 reason))] }
        h.body o st2 → (∀ v, o ≠ .ret (some v)) →
      ExecProgram K st p (.err "the handler does not return a verdict") st2

/-! ### The safety theorem -/

/-- A kernel within its contracts, `Koit.Machine.KernelOk`: a helper
never errs, changes the packet only when its declaration has the `resize`
effect, yields a value exactly when its signature has a result, and
fails only when the declaration is fallible. -/
abbrev KernelOk := Machine.KernelOk

/-- The initial state of a program of a unit: any packet, any context
values, the maps as some earlier program of the unit left them or
fresh. -/
def Initial (pre : Interface) (u : CompUnit) (p : Program) (st : State) : Prop :=
  ∃ decl packet ctx maps fuel,
    pre.kind? p.kind = some decl ∧
    st = initState { interface := pre, license := u.license.map (·.2), types := u.types,
                     consts := u.consts, configs := u.configs, maps := u.maps,
                     fns := u.fns, contracts := u.contracts }
          decl packet ctx maps fuel

/-- T1, safety of Core: for every kernel within its contracts, every
program of a well-typed unit halts with a verdict from every initial
state, and no run of it reaches an error. Stated now; the proof, by
induction on the derivation with the typing judgment as the
invariant, comes after the design settles. -/
theorem safety (pre : Interface) (u : CompUnit) (K : Kernel) :
    KernelOk K → UnitOk pre u →
    ∀ p ∈ u.programs, ∀ st, Initial pre u p st →
      (∃ v st', ExecProgram K st p (.halt v) st') ∧
      (∀ m st', ¬ ExecProgram K st p (.err m) st') := by
  sorry

end Koit.Core.Sem
