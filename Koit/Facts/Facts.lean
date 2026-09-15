import Koit.Core.Print
import Koit.Facts.Domain

/-!
The facts `F` on one path: the predicates the program has established
by a branch, a `check`, a coercion, a marked load, a loop bound, or a
refinement in scope, together with the record `p = e` of a store and
the offset of each view. A fact is kept as it entered; the abstract
state is built from the list when a demand is checked (`state`), and
written back only at a join (`meet`), where the hull of two paths is
what survives.

A fact is about the places it mentions, and it is dropped when one of
them may have changed: `kill` after a store, through the aliases a
store may reach, `killShared` after a call, `inv` at a loop head, and
`dropNames` at the end of a block. A branch, a `check`, and a store
give facts about stack places only: a place in a map, the context,
the packet, a `ref` parameter, or a kernel object may change between
the test or store and the use, so neither yields a fact about one.
The one fact about a shared place is a view's offset, which says
where the view is, not what it holds.

The module ends with the semantics the soundness theorem is stated
on: a valuation of places, and what it means for it to satisfy the
facts.
-/

namespace Koit.Facts

open Koit (Span)
open Koit.Core

/-- The span of a fact the checker derives rather than reads. -/
def noSpan : Span := Span.point Koit.Pos.origin

/-- Where a place lives: the stack, a map value, the context, the
packet, a `ref` parameter of unknown origin, or a kernel object bound
by `hold`. Only the stack is this program's alone. -/
inductive Origin where
  | stack | map (name : String) | ctx | pkt | param | kernel
  deriving Repr, BEq, Inhabited

/-- The shape of a place for the domain: an integer of a signedness
and width, a boolean, or something the domain does not compute with,
a byte-order value or an aggregate. -/
inductive Shape where
  | int (signed : Bool) (w : Nat)
  | bool
  | other
  deriving Repr, BEq, Inhabited

/-- What the checker tells the facts about names: the origin and sort
of a place, the value of a constant, a verdict name, or a
configuration constant with a default, the sort a type denotes, and
the size of a type. `smt` turns on the trace of accepted entailments
as solver queries. -/
structure Scope where
  place : Place → Option (Origin × Shape)
  const : String → Option Int
  sort  : Ty → Option Shape
  size  : Ty → Option Nat
  smt   : Bool := false

/-- The scope with nothing in it, for facts over constants alone. -/
def Scope.empty : Scope :=
  { place := fun _ => none, const := fun _ => none, sort := fun _ => none,
    size := fun _ => none }

instance : Inhabited Scope := ⟨Scope.empty⟩

end Koit.Facts

/-! ### Equality up to positions, and what an expression mentions -/

namespace Koit.Core

open Koit.Facts (noSpan)

mutual

/-- Structural equality ignoring spans, over the predicate fragment
and place reads; a read of a scalar local is the local. -/
partial def Expr.same : Expr → Expr → Bool
  | .read _ (.var _ x), e | e, .read _ (.var _ x) => Expr.same (.var noSpan x) e
  | .lit _ v _, .lit _ v' _ => v == v'
  | .char _ c, .char _ c' => c == c'
  | .bool _ b, .bool _ b' => b == b'
  | .var _ x, .var _ y => x == y
  | .arith _ op l r, .arith _ op' l' r' =>
    op == op' && Expr.same l l' && Expr.same r r'
  | .cmp _ op l r, .cmp _ op' l' r' =>
    op == op' && Expr.same l l' && Expr.same r r'
  | .not _ e, .not _ e' => Expr.same e e'
  | .and _ l r, .and _ l' r' => Expr.same l l' && Expr.same r r'
  | .or _ l r, .or _ l' r' => Expr.same l l' && Expr.same r r'
  | .cast _ e t, .cast _ e' t' => Expr.same e e' && t.print == t'.print
  | .size _ t, .size _ t' => t.print == t'.print
  | .read _ p, .read _ q => Place.same p q
  | _, _ => false

partial def Place.same : Place → Place → Bool
  | .var _ x, .var _ y => x == y
  | .field _ p f, .field _ q g => f == g && Place.same p q
  | .index _ p i, .index _ q j => Place.same p q && Expr.same i j
  | .slot _ m i, .slot _ m' j => m == m' && Expr.same i j
  | .deref _ e, .deref _ e' => Expr.same e e'
  | _, _ => false

end

/-! ### What a fact mentions -/

mutual

/-- The places an expression reads: locals as `var` places, and the
places under `rd`, with the places their indexes read. A name that
is not a place, a constant, is listed too and ignored by its
consumers. -/
partial def Expr.atoms : Expr → List Place
  | .var s x => [.var s x]
  | .read _ p => p.atoms
  | .arith _ _ l r | .cmp _ _ l r | .and _ l r | .or _ l r =>
    l.atoms ++ r.atoms
  | .not _ e | .cast _ e _ => e.atoms
  | _ => []

partial def Place.atoms : Place → List Place
  | .var s x => [.var s x]
  | .field s p f => .field s p f :: p.atoms
  | .index s p i => .index s p i :: p.atoms ++ i.atoms
  | .slot s m i => .slot s m i :: i.atoms
  | .deref s e => .deref s e :: e.atoms
  | .invalid .. => []

end

/-- The local a place is rooted at, if any. -/
partial def Place.root : Place → Option String
  | .var _ x => some x
  | .field _ p _ | .index _ p _ => p.root
  | .deref _ (.var _ x) => some x
  | _ => none

/-- `e` with every occurrence of the name `x` replaced by `r`. -/
partial def Expr.subst (e : Expr) (x : String) (r : Expr) : Expr :=
  match e with
  | .var _ y => if y == x then r else e
  | .arith s op l r' => .arith s op (l.subst x r) (r'.subst x r)
  | .cmp s op l r' => .cmp s op (l.subst x r) (r'.subst x r)
  | .not s e' => .not s (e'.subst x r)
  | .and s l r' => .and s (l.subst x r) (r'.subst x r)
  | .or s l r' => .or s (l.subst x r) (r'.subst x r)
  | .cast s e' t => .cast s (e'.subst x r) t
  | e => e

/-- The precedence of a predicate's operator, as the surface printer
has it: `||` lowest, then `&&`, comparisons, `|`, `^`, `&`, shifts,
`+ -`, `* / %`, casts, unary, atoms. -/
def Expr.predPrec : Expr → Nat
  | .or .. => 1
  | .and .. => 2
  | .cmp .. => 3
  | .arith _ op .. =>
    match op with
    | .bor => 4 | .bxor => 5 | .band => 6 | .shl | .shr => 7
    | .add | .sub => 8 | .mul | .div | .mod => 9
  | .cast .. => 10
  | .not .. => 11
  | _ => 12

/-- A predicate printed as the programmer writes it, parenthesized
only where precedence requires: a place read is the place, a cast is
`e as T`. -/
partial def Expr.printPred (e : Expr) (min : Nat := 0) : String :=
  let s := match e with
    | .read _ p => p.print
    | .arith _ op l r =>
      let q := e.predPrec
      l.printPred q ++ " " ++ op.spelling ++ " " ++ r.printPred (q + 1)
    | .cmp _ op l r =>
      l.printPred 4 ++ " " ++ op.spelling ++ " " ++ r.printPred 4
    | .not _ e' => "!" ++ e'.printPred 11
    | .and _ l r => l.printPred 2 ++ " && " ++ r.printPred 3
    | .or _ l r => l.printPred 1 ++ " || " ++ r.printPred 2
    | .cast _ e' t => e'.printPred 11 ++ " as " ++ t.print
    | .size _ t => t.print ++ ".size"
    | .call _ f args =>
      f ++ "(" ++ ", ".intercalate (args.map fun
        | .val a => a.printPred
        | .place p => p.print
        | .map _ m => m) ++ ")"
    | e => e.print
  if e.predPrec < min then "(" ++ s ++ ")" else s

end Koit.Core

namespace Koit.Facts

open Koit (Span)
open Koit.Core

/-- Whether the list holds a place equal to `p`. -/
def hasPlace (ps : List Place) (p : Place) : Bool := ps.any (Place.same · p)

/-! ### Facts -/

/-- One fact: a predicate true on this path, or the offset a view was
carved at. -/
inductive Fact where
  | pred (e : Expr)
  | off (view : String) (e : Expr)
  deriving Repr, Inhabited

/-- The cap of each `for` loop, by the loop's span: an output for the
lowering. -/
abbrev Caps := List (Span × Nat)

/-- The facts on a path, with the places each reference in scope
names, so that a fact about `r.cur` after `let r = m[0]` is a fact
about `m[0].cur`; `bottom` marks a path that has exited, on which
every demand holds; `caps` collects the cap of each `for` loop passed,
an output for the lowering that travels with the facts because it is
gathered along the same walk. -/
structure Facts where
  facts   : List Fact := []
  aliases : List (String × Place) := []
  bottom  : Bool := false
  caps    : Caps := []
  /-- The owned names moved on this path, each with its `move`: path
  state carried with the facts because it joins where they join, and
  the two sides of a join must agree on it. -/
  moved   : List (String × Span) := []
  deriving Inhabited

namespace Facts

def empty : Facts := {}

/-- The facts of a path that has exited. -/
def bot (F : Facts) : Facts := { F with bottom := true }

/-- After `move x`: the name is moved on this path. -/
def addMoved (F : Facts) (x : String) (s : Span) : Facts :=
  { F with moved := F.moved ++ [(x, s)] }

/-- Whether `x` is moved on this path, with the `move`. -/
def moved? (F : Facts) (x : String) : Option Span :=
  (F.moved.find? (·.1 == x)).map (·.2)

/-- A reference bound to a place: `let r = m[0]`. -/
def alias (F : Facts) (x : String) (p : Place) : Facts :=
  { F with aliases := (x, p) :: F.aliases }

mutual

/-- The place with every reference resolved to what it names. -/
partial def resolve (F : Facts) : Place → Place
  | .var s x =>
    match F.aliases.lookup x with
    | some q => F.resolve q
    | none => .var s x
  | .field s p f => .field s (F.resolve p) f
  | .index s p i => .index s (F.resolve p) (F.resolveExpr i)
  | .slot s m i => .slot s m (F.resolveExpr i)
  | .deref s (.var s' x) =>
    match F.aliases.lookup x with
    | some q => F.resolve q
    | none => .deref s (.var s' x)
  | p => p

partial def resolveExpr (F : Facts) : Expr → Expr
  | .read s p => .read s (F.resolve p)
  | .arith s op l r => .arith s op (F.resolveExpr l) (F.resolveExpr r)
  | .cmp s op l r => .cmp s op (F.resolveExpr l) (F.resolveExpr r)
  | .not s e => .not s (F.resolveExpr e)
  | .and s l r => .and s (F.resolveExpr l) (F.resolveExpr r)
  | .or s l r => .or s (F.resolveExpr l) (F.resolveExpr r)
  | .cast s e t => .cast s (F.resolveExpr e) t
  | e => e

end

end Facts

def Fact.atoms : Fact → List Place
  | .pred e => e.atoms
  | .off h e => .var noSpan h :: e.atoms

/-- Whether an expression is in the fragment facts are made of:
literals, names, `size`, arithmetic, comparisons, logic, casts, and
reads of places, with every name a place `sc` knows or a constant.
With `stackOnly`, every place must live on the stack. -/
partial def factForm (sc : Scope) (stackOnly : Bool) : Expr → Bool
  | .lit .. | .char .. | .bool .. | .size .. => true
  | .var _ x =>
    match sc.place (.var noSpan x) with
    | some (o, s) => s != .other && (!stackOnly || o == .stack)
    | none => (sc.const x).isSome
  | .read _ p =>
    match sc.place p with
    | some (o, s) =>
      s != .other && (!stackOnly || o == .stack) &&
        p.atoms.all fun q => match q with
          | .index _ _ i | .slot _ _ i => factForm sc stackOnly i
          | _ => true
    | none => false
  | .arith _ _ l r | .cmp _ _ l r | .and _ l r | .or _ l r =>
    factForm sc stackOnly l && factForm sc stackOnly r
  | .not _ e | .cast _ e _ => factForm sc stackOnly e
  | _ => false

/-! ### Overlap of places -/

/-- Whether two indexes may name the same element: they do unless
both are literals and differ. -/
def indexMayEqual (i j : Expr) : Bool :=
  match i, j with
  | .lit _ v _, .lit _ v' _ => v == v'
  | _, _ => true

/-- Whether `p` is `q` or lies inside it, up to indexes that may be
equal. -/
partial def within (p q : Place) : Bool :=
  if sameRoot p q then true else
  match p with
  | .field _ p' _ | .index _ p' _ => within p' q
  | _ => false
where
  sameRoot (p q : Place) : Bool :=
    match p, q with
    | .var _ x, .var _ y => x == y
    | .deref _ (.var _ x), .var _ y | .var _ x, .deref _ (.var _ y) => x == y
    | .deref _ e, .deref _ e' => Expr.same e e'
    | .field _ p f, .field _ q g => f == g && sameRoot p q
    | .index _ p i, .index _ q j => indexMayEqual i j && sameRoot p q
    | .slot _ m i, .slot _ m' j => m == m' && indexMayEqual i j
    | _, _ => false

/-- Whether a store to `p` may change `q`: one lies inside the other,
or both are reached through `ref` parameters, whose origins are the
callers', or both lie in the packet, where views may overlap. -/
def overlaps (sc : Scope) (p q : Place) : Bool :=
  within p q || within q p ||
  match ((sc.place p).map (·.1) : Option Origin),
        ((sc.place q).map (·.1) : Option Origin) with
  | some .param, some .param => true
  | some .pkt, some .pkt => true
  | _, _ => false

/-- Whether a fact mentions a place satisfying `f`. -/
def Fact.mentions (fact : Fact) (f : Place → Bool) : Bool :=
  fact.atoms.any f

namespace Facts

def add (F : Facts) (f : Fact) : Facts :=
  if F.bottom then F else { F with facts := F.facts ++ [f] }

/-- The facts with those mentioning a place `f` holds of removed. -/
def dropWhere (F : Facts) (f : Place → Bool) : Facts :=
  { F with facts := F.facts.filter fun fact => !fact.mentions f }

/-- As `dropWhere`, keeping a view's offset: a store or a call changes
what the packet holds, never where a view was carved, so an offset
over stack names outlives both. Only the end of the view's scope, and
later the guard it lives under, remove it. -/
def dropWhereKept (F : Facts) (f : Place → Bool) : Facts :=
  { F with facts := F.facts.filter fun fact =>
      match fact with
      | .off _ e => !e.atoms.any f
      | _ => !fact.mentions f }

/-- The offset a view was carved at, if it is a fact. -/
def offsetOf (F : Facts) (h : String) : Option Expr :=
  F.facts.findSome? fun
    | .off h' e => if h' == h then some e else none
    | _ => none

/-- After a store to `p`: every fact about a place the store may
change goes. -/
def kill (sc : Scope) (F : Facts) (p : Place) : Facts :=
  let p := F.resolve p
  F.dropWhereKept fun q => overlaps sc p q

/-- After a call: every fact about a place off the stack goes, since
the callee or the kernel may write it. -/
def killShared (sc : Scope) (F : Facts) : Facts :=
  F.dropWhereKept fun q =>
    match sc.place q with
    | some (.stack, _) => false
    | some _ => true
    | none => false

/-- At the end of a block: the facts about its locals go, and so do
their aliases. -/
def dropNames (F : Facts) (names : List String) : Facts :=
  let F := F.dropWhere fun q => match q.root with
    | some x => names.contains x
    | none => false
  { F with aliases := F.aliases.filter fun (x, _) => !names.contains x,
           moved := F.moved.filter fun (x, _) => !names.contains x }

/-- At a loop head: the facts about what the body assigns and about
shared places go; the body's own facts are added by the loop rule. -/
def inv (sc : Scope) (F : Facts) (assigned : List Place) : Facts :=
  assigned.foldl (kill sc) (F.killShared sc)

/-- The negation of a condition, pushed to the comparisons. -/
partial def negate : Expr → Expr
  | .cmp s op l r =>
    let op' := match op with
      | .eq => CmpOp.ne | .ne => .eq | .lt => .ge | .ge => .lt
      | .le => .gt | .gt => .le
    .cmp s op' l r
  | .not _ e => e
  | .and s l r => .or s (negate l) (negate r)
  | .or s l r => .and s (negate l) (negate r)
  | .bool s b => .bool s (!b)
  | e => .not e.span e

/-- A condition established on this path, by a branch or a `check`:
its conjuncts enter as separate facts, and a conjunct that reads a
place off the stack yields nothing. -/
partial def assume (sc : Scope) (F : Facts) (e : Expr) : Facts :=
  match e with
  | .and _ l r => (F.assume sc l).assume sc r
  | .not _ (.or _ l r) => (F.assume sc (negate l)).assume sc (negate r)
  | .not _ (.not _ e) => F.assume sc e
  | e =>
    let e := F.resolveExpr e
    if factForm sc true e then F.add (.pred e) else F

/-- The atom of a place: the local itself, or a read. -/
def atomOf (sc : Scope) (p : Place) : Expr :=
  match p with
  | .var s x =>
    match sc.place p with
    | some (_, .int ..) | some (_, .bool) => .var s x
    | _ => .read s p
  | p => .read p.span p

/-- After `p = e`: the facts about `p` go, then `p = e` is recorded
when `p` lies on the stack, `e` does not read what the store changed,
and `e` is in the fragment over stack places. A store to a shared
place leaves no fact: another party may write the place before it is
read again, and the lowering reloads it. -/
def record (sc : Scope) (F : Facts) (p : Place) (e : Expr) : Facts :=
  let p := F.resolve p
  let e := F.resolveExpr e
  let F := F.kill sc p
  match sc.place p with
  | some (.stack, _) =>
    if e.atoms.any (fun q => overlaps sc p q) then F
    else if factForm sc true e then
      F.add (.pred (.cmp e.span .eq (atomOf sc p) e))
    else F
  | _ => F

end Facts

/-! ### The abstract state -/

/-- What is known about each place at one point: built from the facts
and discarded. -/
abbrev State := List (Place × AV)

namespace State

def get? (st : State) (p : Place) : Option AV :=
  (st.find? fun (q, _) => Place.same p q).map (·.2)

def set (st : State) (p : Place) (v : AV) : State :=
  (p, v) :: st.filter fun (q, _) => !Place.same p q

/-- The join at a join of two paths: a place missing on one side is
unknown there. -/
def join (a b : State) : State :=
  a.filterMap fun (p, v) => (b.get? p).map fun v' => (p, v.join v')

end State

/-- The unknown value of a sort. -/
def unknown : Shape → AV
  | .int s w => .int (Abs.top s w)
  | .bool => .bool .maybe
  | .other => .none

/-- Exact integer arithmetic for two constants of no type yet, which
is the arithmetic of `u64` on the values that occur. -/
def arithInt (op : ArithOp) (x y : Int) : Int :=
  match op with
  | .add => x + y
  | .sub => x - y
  | .mul => x * y
  | .div => Abs.divInt x y
  | .mod => Abs.modInt x y
  | .band => Int.ofNat (x.toNat &&& y.toNat)
  | .bor => Int.ofNat (x.toNat ||| y.toNat)
  | .bxor => Int.ofNat (x.toNat ^^^ y.toNat)
  | .shl => Int.ofNat (x.toNat <<< y.toNat)
  | .shr => Int.ofNat (x.toNat >>> y.toNat)

def cmpInt (op : CmpOp) (x y : Int) : Bool :=
  match op with
  | .eq => x == y | .ne => x != y | .lt => x < y | .le => x ≤ y
  | .gt => x > y | .ge => x ≥ y

def Abs.apply (op : ArithOp) (a b : Abs) : Abs :=
  match op with
  | .add => a.add b | .sub => a.sub b | .mul => a.mul b | .div => a.div b
  | .mod => a.mod b | .band => a.band b | .bor => a.bor b
  | .bxor => a.bxor b | .shl => a.shl b | .shr => a.shr b

/-- The value of a place in the state: what is recorded, or the
unknown value of its sort. -/
def lookup (sc : Scope) (st : State) (p : Place) : AV :=
  match st.get? p with
  | some v => v
  | none =>
    match sc.place p with
    | some (_, s) => unknown s
    | none => .none

/-- Forward interpretation of an expression in the state. -/
partial def eval (sc : Scope) (st : State) : Expr → AV
  | .lit _ v _ => .poly v
  | .char _ c => .int (Abs.const false 8 c.toNat)
  | .bool _ b => .bool (.ofBool b)
  | .size _ t => match sc.size t with
    | some n => .poly n
    | none => .none
  | .var s x =>
    match sc.place (.var s x) with
    | some _ => lookup sc st (.var s x)
    | none => match sc.const x with
      | some v => .poly v
      | none => .none
  | .read _ p => lookup sc st p
  | .arith _ op l r =>
    let a := eval sc st l
    let b := eval sc st r
    match a.align b with
    | some (a, b) => .int (a.apply op b)
    | none => match a, b with
      | .poly x, .poly y => .poly (arithInt op x y)
      | _, _ => .none
  | .cmp _ op l r =>
    let a := eval sc st l
    let b := eval sc st r
    match a.align b with
    | some (a, b) => .bool (Abs.cmp op a b)
    | none => match a, b with
      | .poly x, .poly y => .bool (.ofBool (cmpInt op x y))
      | _, _ => .none
  | .not _ e => match eval sc st e with
    | .bool t => .bool t.not
    | _ => .none
  | .and _ l r => match eval sc st l, eval sc st r with
    | .bool a, .bool b => .bool (a.and b)
    | _, _ => .none
  | .or _ l r => match eval sc st l, eval sc st r with
    | .bool a, .bool b => .bool (a.or b)
    | _, _ => .none
  | .cast _ e t =>
    match sc.sort t, eval sc st e with
    | some (.int s w), .int a => .int (a.cast s w)
    | some (.int s w), .poly v => .int (Abs.const s w v)
    | some (.int s w), .bool .yes => .int (Abs.const s w 1)
    | some (.int s w), .bool .no => .int (Abs.const s w 0)
    | some (.int s w), .bool .maybe =>
      .int (Abs.reduce { Abs.top s w with lo := 0, hi := 1 })
    | _, _ => .none
  | _ => .none

/-- The state with `e` known to be `a`: a place is set; a place under
a constant mask learns the masked bits; a place under a widening cast
from unsigned learns the value when it fits. -/
partial def assignAbs (sc : Scope) (st : State) (e : Expr) (a : Abs) : State :=
  match e with
  | .var s x =>
    if (sc.place (.var s x)).isSome then st.set (.var s x) (.int a) else st
  | .read _ p => st.set p (.int a)
  | .arith _ .band x m =>
    match eval sc st m, eval sc st x with
    | .poly mv, .int xa | .int ⟨_, _, mv, _, _, _⟩, .int xa =>
      let mask := toBits xa.w mv
      let bits := (Abs.top xa.signed xa.w).withBits (a.kv &&& mask)
        (a.km &&& mask)
      assignAbs sc st x (xa.meet bits)
    | _, _ => st
  | .cast _ x _ =>
    match eval sc st x with
    | .int xa =>
      if !xa.signed && xa.w < a.w && a.lo ≥ 0 &&
          a.hi ≤ typeHi false xa.w then
        assignAbs sc st x (xa.meet (a.cast false xa.w))
      else st
    | _ => st
  | _ => st

mutual

/-- The state narrowed by assuming `e`. -/
partial def narrow (sc : Scope) (st : State) : Expr → State
  | .and _ l r => narrow sc (narrow sc st l) r
  | .or _ l r => (narrow sc st l).join (narrow sc st r)
  | .not _ e => narrowNot sc st e
  | .cmp _ op l r =>
    let a := eval sc st l
    let b := eval sc st r
    match a.align b with
    | some (a, b) =>
      let (a', b') := Abs.narrow op a b
      assignAbs sc (assignAbs sc st l a') r b'
    | none => st
  | .var s x =>
    match sc.place (.var s x) with
    | some (_, .bool) => st.set (.var s x) (.bool .yes)
    | _ => st
  | _ => st

partial def narrowNot (sc : Scope) (st : State) : Expr → State
  | .cmp s op l r => narrow sc st (Facts.negate (.cmp s op l r))
  | .and _ l r => (narrowNot sc st l).join (narrowNot sc st r)
  | .or _ l r => narrowNot sc (narrowNot sc st l) r
  | .not _ e => narrow sc st e
  | .var s x =>
    match sc.place (.var s x) with
    | some (_, .bool) => st.set (.var s x) (.bool .no)
    | _ => st
  | _ => st

end

namespace Facts

/-- The state at this point: the facts applied in the order they
entered, each narrowing with what was known when it arrived. -/
def state (sc : Scope) (F : Facts) : State :=
  F.facts.foldl (fun st f => match f with
    | .pred e => narrow sc st e
    | .off .. => st) []

/-- The facts a joined state yields for one place: its bounds where
narrower than the type, its known bits, its truth. -/
def factsOf (sc : Scope) (p : Place) : AV → List Fact
  | .int a =>
    if a.isEmpty then [] else
    let k := atomOf sc p
    let s := noSpan
    let lit (n : Int) : Expr := .lit s n.toNat (toString n)
    (if a.lo > typeLo a.signed a.w && a.lo ≥ 0 then
      [.pred (.cmp s .ge k (lit a.lo))] else []) ++
    (if a.hi < typeHi a.signed a.w && a.hi ≥ 0 then
      [.pred (.cmp s .le k (lit a.hi))] else []) ++
    (if a.km != 0 then
      [.pred (.cmp s .eq (.arith s .band k (lit a.km)) (lit (a.kv &&& a.km)))]
     else [])
  | .bool .yes => [.pred (atomOf sc p)]
  | .bool .no => [.pred (.not noSpan (atomOf sc p))]
  | _ => []

/-- The facts after two paths join: what both paths established,
and, for each place, the hull of what each knew. A path that has
exited contributes nothing. -/
def meet (sc : Scope) (F1 F2 : Facts) : Facts :=
  let caps := F1.caps ++ F2.caps.filter fun (s, _) =>
    !F1.caps.any fun (s', _) => s' == s
  if F1.bottom then { F2 with caps }
  else if F2.bottom then { F1 with caps }
  else
    let common := F1.facts.filter fun f => F2.facts.any fun g =>
      match f, g with
      | .pred e, .pred e' => Expr.same e e'
      | .off h e, .off h' e' => h == h' && Expr.same e e'
      | _, _ => false
    let joined := (F1.state sc).join (F2.state sc)
    let hull := joined.flatMap fun (p, v) => factsOf sc p v
    -- the two sides agree on what is moved, or the join is an error
    -- the checker reports before it meets them
    { facts := common ++ hull, aliases := F1.aliases, bottom := false, caps,
      moved := F1.moved }

/-- The facts printed one per line, for messages and tests. -/
def print (F : Facts) : List String :=
  F.facts.map fun
    | .pred e => e.print
    | .off h e => s!"off({h}) = {e.print}"

end Facts

/-! ### Semantics -/

/-- A runtime value: an integer of a type, as its bit pattern, or a
boolean; a constant of no type yet, as an expression's value before
it meets a typed operand. -/
inductive Val where
  | int (signed : Bool) (w : Nat) (bits : Nat)
  | poly (v : Int)
  | bool (b : Bool)
  deriving Repr, BEq, Inhabited

/-- A valuation: the values of places at one moment, and what the
scope fixes, the constants, the sorts of types, and the sizes. -/
structure Valuation where
  place : Place → Option Val
  const : String → Option Int
  sort  : Ty → Option Shape
  size  : Ty → Option Nat

/-- The value of `v` in the type. -/
def Val.toInt : Val → Option Int
  | .int s w n => some (fromBits s w n)
  | .poly v => some v
  | .bool _ => none

/-- Two integer operands at one type. -/
def Val.align : Val → Val → Option (Bool × Nat × Int × Int)
  | .int s w n, .int s' w' n' =>
    if s == s' && w == w' then some (s, w, fromBits s w n, fromBits s w n')
    else none
  | .int s w n, .poly v =>
    some (s, w, fromBits s w n, fromBits s w (toBits w v))
  | .poly v, .int s w n =>
    some (s, w, fromBits s w (toBits w v), fromBits s w n)
  | _, _ => none

/-- Arithmetic of the type: wrapping, with the kernel's division and
shifts. -/
def arithVal (op : ArithOp) (s : Bool) (w : Nat) (x y : Int) : Val :=
  let bits (v : Int) : Val := .int s w (toBits w v)
  let xb := toBits w x
  let yb := toBits w y
  match op with
  | .add => bits (x + y)
  | .sub => bits (x - y)
  | .mul => bits (x * y)
  | .div => bits (Abs.divInt x y)
  | .mod => bits (Abs.modInt x y)
  | .band => .int s w (xb &&& yb)
  | .bor => .int s w (xb ||| yb)
  | .bxor => .int s w (xb ^^^ yb)
  | .shl => bits (Int.ofNat (xb <<< (yb % w)))
  | .shr =>
    if s then bits (x >>> (yb % w)) else .int s w (xb >>> (yb % w))

/-- The value of an expression under a valuation, in the fragment. -/
partial def evalVal (σ : Valuation) : Expr → Option Val
  | .lit _ v _ => some (.poly v)
  | .char _ c => some (.int false 8 c.toNat)
  | .bool _ b => some (.bool b)
  | .size _ t => (σ.size t).map fun n => .poly n
  | .var s x =>
    match σ.place (.var s x) with
    | some v => some v
    | none => (σ.const x).map .poly
  | .read _ p => σ.place p
  | .arith _ op l r => do
    let a ← evalVal σ l
    let b ← evalVal σ r
    match a.align b with
    | some (s, w, x, y) => some (arithVal op s w x y)
    | none => match a, b with
      | .poly x, .poly y => some (.poly (arithInt op x y))
      | _, _ => none
  | .cmp _ op l r => do
    let a ← evalVal σ l
    let b ← evalVal σ r
    match a.align b with
    | some (_, _, x, y) => some (.bool (cmpInt op x y))
    | none => match a, b with
      | .poly x, .poly y => some (.bool (cmpInt op x y))
      | _, _ => none
  | .not _ e => do
    let .bool b ← evalVal σ e | none
    some (.bool !b)
  | .and _ l r => do
    let .bool a ← evalVal σ l | none
    let .bool b ← evalVal σ r | none
    some (.bool (a && b))
  | .or _ l r => do
    let .bool a ← evalVal σ l | none
    let .bool b ← evalVal σ r | none
    some (.bool (a || b))
  | .cast _ e t => do
    let some (.int s w) := σ.sort t | none
    match ← evalVal σ e with
    | .int _ _ n => some (.int s w (toBits w (fromBits s w (n &&& ones w))))
    | .poly v => some (.int s w (toBits w v))
    | .bool b => some (.int s w (if b then 1 else 0))
  | _ => none

/-- Whether a predicate holds under a valuation. -/
def holds (σ : Valuation) (e : Expr) : Prop := evalVal σ e = some (.bool true)

def Fact.holds (σ : Valuation) : Fact → Prop
  | .pred e => Facts.holds σ e
  | .off h e => Facts.holds σ (.cmp noSpan .eq (.var noSpan h) e)

/-- `sigma` satisfies `F`: every fact holds. -/
def Sat (σ : Valuation) (F : Facts) : Prop := ∀ f ∈ F.facts, f.holds σ

/-- A valuation that agrees with the scope: places carry values of
the sort the scope gives them, and the constants, sorts, and sizes
are the scope's. -/
def WellTyped (sc : Scope) (σ : Valuation) : Prop :=
  (∀ p v, σ.place p = some v →
    match v, sc.place p with
    | .int s w _, some (_, .int s' w') => s = s' ∧ w = w'
    | .bool _, some (_, .bool) => True
    | _, _ => False) ∧
  σ.const = sc.const ∧ σ.sort = sc.sort ∧ σ.size = sc.size

/-- Semantic entailment: `P` holds under every valuation that
satisfies `F`. The judgment is stated with this; the procedure of
`Entail.lean` decides a subset of it. -/
def Entails (sc : Scope) (F : Facts) (P : Expr) : Prop :=
  F.bottom = true ∨
  ∀ σ, WellTyped sc σ → Sat σ F → holds σ P

end Koit.Facts
