import Koit.Check.Env

/-!
Operations on types the rules need: resolution of named types,
base-type equality (refinements ignored, since their comparison is
entailment), the padded size and alignment at natural alignment,
packet representability, scalars against aggregates, constant
expressions and their evaluation for sizes and counts, and the form a
predicate may take.
-/

namespace Koit.Check

open Koit (Span)
open Koit.Core


/-- `{v: T | P}` weakened to `T`, at the head. -/
def _root_.Koit.Core.Ty.strip : Ty → Ty
  | .refined _ _ t _ => t.strip
  | t => t

/-- The head-normal form of a type: refinements stripped and a named
type replaced by its declaration, repeatedly. -/
partial def Env.norm (env : Env) (t : Ty) (fuel : Nat := 64) : M Ty := do
  match t.strip with
  | .named s n =>
    if fuel == 0 then
      err s s!"type `{n}` is defined in terms of itself"
    match env.type? n with
    | some d => env.norm d.ty (fuel - 1)
    | none => err s s!"unknown type `{n}`"
  | t' => return t'

def _root_.Koit.Core.Ty.isIntTy : Ty → Bool
  | .int .. => true
  | _ => false

/-- The scalars: integers, byte-order integers, booleans.
`t` is head-normal. -/
def _root_.Koit.Core.Ty.isScalar : Ty → Bool
  | .int .. | .be .. | .bool .. => true
  | _ => false

/-- The place types: a name of a place, not a value. -/
def _root_.Koit.Core.Ty.isPlaceTy : Ty → Bool
  | .ref .. | .view .. | .own .. => true
  | _ => false

mutual

/-- Evaluates a constant expression to an integer, for array lengths,
map capacities, loop counts, and `size`; `none` when the expression
is not constant or has no integer value (a configuration constant
without a default, a byte-order value). Arithmetic is over `Int`,
which is exact for the sizes and counts this serves. -/
partial def Env.evalConst (env : Env) (e : Expr) (fuel : Nat := 64) :
    Option Int := do
  if fuel == 0 then none else
  match e with
  | .lit _ v _ => some v
  | .char _ c => some c.toNat
  | .var _ n =>
    if (env.local? n).isSome then none
    else if let some d := env.const? n then env.evalConst d.value (fuel - 1)
    else if let some d := env.config? n then
      d.init.bind fun i => env.evalConst i (fuel - 1)
    else none
  | .arith _ op l r => do
    let a ← env.evalConst l (fuel - 1)
    let b ← env.evalConst r (fuel - 1)
    match op with
    | .add => some (a + b)
    | .sub => some (a - b)
    | .mul => some (a * b)
    | .div => some (if b == 0 then 0 else a / b)
    | .mod => some (if b == 0 then a else a % b)
    | .band => some (Int.ofNat (a.toNat &&& b.toNat))
    | .bor => some (Int.ofNat (a.toNat ||| b.toNat))
    | .bxor => some (Int.ofNat (a.toNat ^^^ b.toNat))
    | .shl => some (Int.ofNat (a.toNat <<< b.toNat))
    | .shr => some (Int.ofNat (a.toNat >>> b.toNat))
  | .cast _ e _ => env.evalConst e (fuel - 1)
  | .size _ t => (env.layout t).toOption.map fun (sz, _) => Int.ofNat sz
  | _ => none

/-- The padded size and alignment of a data type, with fields at
natural alignment in declaration order. -/
partial def Env.layout (env : Env) (t : Ty) (fuel : Nat := 64) :
    M (Nat × Nat) := do
  if fuel == 0 then err t.span "type nesting too deep"
  match ← env.norm t with
  | .int _ _ w => return (w / 8, w / 8)
  | .be _ w => return (w / 8, w / 8)
  | .bool _ => return (1, 1)
  | .spinlock _ => return (4, 4)
  | .struct _ fields =>
    let mut off := 0
    let mut align := 1
    for f in fields do
      let (sz, al) ← env.layout f.ty (fuel - 1)
      off := (off + al - 1) / al * al + sz
      align := max align al
    return ((off + align - 1) / align * align, align)
  | .array s elem n =>
    let (sz, al) ← env.layout elem (fuel - 1)
    match env.evalConst n with
    | some k => return (sz * k.toNat, al)
    | none => err s s!"the array length `{n.print}` must be a constant \
        expression"
  | t' => err t'.span s!"`{t.print}` has no size: it names a place, not data"

end

/-- Why a type is not packet-representable, if it is not:
a `spinlock`, a `ref`, a `view`, an `own`, or an optional inside it.
With `allowLock`, one `spinlock` is admitted, as in a map value. -/
partial def Env.notRepresentable (env : Env) (t : Ty) (allowLock : Bool)
    (fuel : Nat := 64) : M (Option String) := do
  if fuel == 0 then return some "a type nested too deep"
  match ← env.norm t with
  | .int .. | .be .. | .bool .. => return none
  | .spinlock _ => return if allowLock then none else some "`spinlock`"
  | .struct _ fields =>
    for f in fields do
      if let some why ← env.notRepresentable f.ty allowLock (fuel - 1) then
        return some why
    return none
  | .array _ elem _ => env.notRepresentable elem allowLock (fuel - 1)
  | .ref .. => return some "`ref`"
  | .view .. => return some "`view`"
  | .own .. => return some "`own`"
  | .opt .. => return some "an optional"
  | _ => return some "an unknown type"

/-- The number of `spinlock` fields in a data type, through nesting. -/
partial def Env.spinlocks (env : Env) (t : Ty) (fuel : Nat := 64) : M Nat := do
  if fuel == 0 then return 0
  match ← env.norm t with
  | .spinlock _ => return 1
  | .struct _ fields =>
    let mut n := 0
    for f in fields do
      n := n + (← env.spinlocks f.ty (fuel - 1))
    return n
  | .array _ elem n =>
    let k := (env.evalConst n).map (·.toNat) |>.getD 1
    return k * (← env.spinlocks elem (fuel - 1))
  | _ => return 0

/-- Base-type equality: structural, through named types, with
refinements ignored and array lengths compared by value when both
evaluate and by text otherwise. Field predicates are ignored as well:
two struct types with the same fields and base types are one type. -/
partial def Env.eqv (env : Env) (a b : Ty) (fuel : Nat := 64) : M Bool := do
  if fuel == 0 then return false
  let a' ← env.norm a
  let b' ← env.norm b
  match a', b' with
  | .int _ s w, .int _ s' w' => return s == s' && w == w'
  | .be _ w, .be _ w' => return w == w'
  | .bool _, .bool _ => return true
  | .spinlock _, .spinlock _ => return true
  | .struct _ fs, .struct _ gs =>
    if fs.length != gs.length then return false
    for (f, g) in fs.zip gs do
      if f.name != g.name then return false
      unless ← env.eqv f.ty g.ty (fuel - 1) do return false
    return true
  | .array _ t n, .array _ t' n' =>
    unless ← env.eqv t t' (fuel - 1) do return false
    match env.evalConst n, env.evalConst n' with
    | some k, some k' => return k == k'
    | _, _ => return n.print == n'.print
  | .ref _ t, .ref _ t' => env.eqv t t' (fuel - 1)
  | .view _ t, .view _ t' => env.eqv t t' (fuel - 1)
  | .own _ t, .own _ t' => env.eqv t t' (fuel - 1)
  | .opt _ t, .opt _ t' => env.eqv t t' (fuel - 1)
  | _, _ => return false

/-- Whether `e` is a constant expression: literals,
constants, configuration constants, `size`, `hton` of a constant, and
arithmetic, comparison, and logic over these. -/
partial def Env.isConstExpr (env : Env) : Expr → Bool
  | .lit .. | .char .. | .bool .. | .size .. => true
  | .var _ n =>
    (env.local? n).isNone && ((env.const? n).isSome || (env.config? n).isSome)
  | .arith _ _ l r | .cmp _ _ l r | .and _ l r | .or _ l r =>
    env.isConstExpr l && env.isConstExpr r
  | .not _ e | .cast _ e _ | .hton _ e => env.isConstExpr e
  | _ => false

/-- The form a predicate may take: literals, names, arithmetic,
comparisons, and logic; no calls, no map or packet access, no
byte-order casts. -/
partial def isPredicateForm : Expr → Bool
  | .lit .. | .char .. | .bool .. | .var .. | .size .. => true
  | .arith _ _ l r | .cmp _ _ l r | .and _ l r | .or _ l r =>
    isPredicateForm l && isPredicateForm r
  | .not _ e | .cast _ e _ => isPredicateForm e
  | _ => false

end Koit.Check
