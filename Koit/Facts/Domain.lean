import Koit.Core.Syntax

/-!
The abstract values entailment computes with: for an integer, an
interval read in the signedness of its type together with the bits
known exactly, the two kept consistent with each other; for a boolean,
three-valued truth. Every operator of the predicate fragment has a
transfer function here, exact for `%` and `/` by a constant, for `&`
with a constant mask, and for a cast between widths, since those are
the cases a verifier re-derives from the emitted code and the ones
programs lean on: a modulo into an array, a masked header field, a
byte widened to an index.

A value here is what the checker knows about a name at one point on
one path. It is built from the facts on that path when a demand is
checked, and discarded after.
-/

namespace Koit.Facts

/-- Three-valued truth: a comparison over intervals may be decided or
not. -/
inductive Tri where
  | yes | no | maybe
  deriving Repr, BEq, DecidableEq, Inhabited

namespace Tri

def not : Tri → Tri
  | .yes => .no | .no => .yes | .maybe => .maybe

def and : Tri → Tri → Tri
  | .no, _ | _, .no => .no
  | .yes, .yes => .yes
  | _, _ => .maybe

def or : Tri → Tri → Tri
  | .yes, _ | _, .yes => .yes
  | .no, .no => .no
  | _, _ => .maybe

def ofBool (b : Bool) : Tri := if b then .yes else .no

/-- The join of two truths at a join of two paths. -/
def join (a b : Tri) : Tri := if a == b then a else .maybe

end Tri

/-! ### Widths -/

/-- `2^w`. -/
def modulus (w : Nat) : Nat := 2 ^ w

/-- The all-ones mask of `w` bits. -/
def ones (w : Nat) : Nat := modulus w - 1

/-- The smallest and largest values of the type. -/
def typeLo (signed : Bool) (w : Nat) : Int :=
  if signed then -(Int.ofNat (2 ^ (w - 1))) else 0

def typeHi (signed : Bool) (w : Nat) : Int :=
  if signed then Int.ofNat (2 ^ (w - 1)) - 1 else Int.ofNat (ones w)

/-- The bit pattern of a value of the type, wrapping. -/
def toBits (w : Nat) (v : Int) : Nat := (v % Int.ofNat (modulus w)).toNat

/-- The value a bit pattern denotes in the type. -/
def fromBits (signed : Bool) (w : Nat) (n : Nat) : Int :=
  if signed && n ≥ 2 ^ (w - 1) then Int.ofNat n - Int.ofNat (modulus w)
  else Int.ofNat n

/-- The number of bits needed for `n`: 0 for 0. -/
def bitLen (n : Nat) : Nat := if n == 0 then 0 else Nat.log2 n + 1

/-! ### Abstract integers -/

/-- What is known about an integer of one type: the interval `[lo, hi]`
of its value, inclusive, read in the type's signedness, and the bits
known exactly, `kv` holding their values and `km` marking which bits
those are. An interval with `lo > hi` is the empty value: the path
cannot be taken. -/
structure Abs where
  signed : Bool
  w  : Nat
  lo : Int
  hi : Int
  kv : Nat
  km : Nat
  deriving Repr, BEq, Inhabited

namespace Abs

/-- Nothing known: the whole type. -/
def top (signed : Bool) (w : Nat) : Abs :=
  { signed, w, lo := typeLo signed w, hi := typeHi signed w, kv := 0, km := 0 }

/-- Exactly one value, wrapped into the type. -/
def const (signed : Bool) (w : Nat) (v : Int) : Abs :=
  let n := toBits w v
  { signed, w, lo := fromBits signed w n, hi := fromBits signed w n,
    kv := n, km := ones w }

def isEmpty (a : Abs) : Bool := a.lo > a.hi

def const? (a : Abs) : Option Int := if a.lo == a.hi then some a.lo else none

/-- The unknown-bit mask, the complement of `km` within the width. -/
def um (a : Abs) : Nat := ones a.w ^^^ (a.km &&& ones a.w)

/-- The bit patterns of the interval's ends. -/
def loBits (a : Abs) : Nat := toBits a.w a.lo
def hiBits (a : Abs) : Nat := toBits a.w a.hi

/-- The interval narrowed to what the known bits allow. -/
def bitsToInterval (a : Abs) : Abs :=
  if a.km == 0 then a else
  let minBits := a.kv &&& a.km
  let maxBits := (a.kv &&& a.km) ||| a.um
  let sign := 2 ^ (a.w - 1)
  if !a.signed then
    { a with lo := max a.lo (Int.ofNat minBits), hi := min a.hi maxBits }
  else if a.km &&& sign != 0 then
    -- the sign is known: one contiguous range in the signed reading
    { a with lo := max a.lo (fromBits true a.w minBits),
             hi := min a.hi (fromBits true a.w maxBits) }
  else
    -- the sign is unknown: the smallest value has the sign bit set,
    -- the largest has it clear
    { a with lo := max a.lo (fromBits true a.w (minBits ||| sign)),
             hi := min a.hi
               (fromBits true a.w (maxBits &&& (ones a.w ^^^ sign))) }

/-- The bits the interval fixes: when both ends have the same sign,
the leading bits their patterns share. -/
def intervalToBits (a : Abs) : Abs :=
  if a.isEmpty then a else
  let l := a.loBits
  let h := a.hiBits
  if (a.lo < 0) != (a.hi < 0) then a else
  let differ := bitLen (l ^^^ h)
  let high := ones a.w ^^^ ones differ
  let conflict := (a.kv ^^^ l) &&& a.km &&& high
  if conflict != 0 then { a with lo := 1, hi := 0 } else
  { a with kv := (a.kv &&& a.km) ||| (l &&& high), km := a.km ||| high }

/-- Interval and bits made consistent with each other. -/
def reduce (a : Abs) : Abs :=
  if a.isEmpty then a else
  let a := a.bitsToInterval
  let a := a.intervalToBits
  a.bitsToInterval

/-- The join at a join of two paths: the hull of the intervals and the
bits both know with the same value. -/
def join (a b : Abs) : Abs :=
  if a.isEmpty then b else if b.isEmpty then a else
  let km := a.km &&& b.km &&& (ones a.w ^^^ (a.kv ^^^ b.kv))
  { a with lo := min a.lo b.lo, hi := max a.hi b.hi, kv := a.kv &&& km, km }

/-- The meet: both known at once, empty on a conflict. -/
def meet (a b : Abs) : Abs :=
  let conflict := (a.kv ^^^ b.kv) &&& a.km &&& b.km
  if conflict != 0 then { a with lo := 1, hi := 0 } else
  reduce { a with
           lo := max a.lo b.lo, hi := min a.hi b.hi,
           kv := (a.kv &&& a.km) ||| (b.kv &&& b.km), km := a.km ||| b.km }

/-- Whether the interval lies within the type. -/
def fits (a : Abs) (lo hi : Int) : Bool :=
  typeLo a.signed a.w ≤ lo && hi ≤ typeHi a.signed a.w

/-- The value with the interval replaced, kept within the type. -/
def withInterval (a : Abs) (lo hi : Int) : Abs :=
  if a.fits lo hi then reduce { a with lo, hi }
  else reduce { a with lo := typeLo a.signed a.w, hi := typeHi a.signed a.w }

/-- The value with the known bits replaced, the interval widened to
the type first. -/
def withBits (a : Abs) (kv km : Nat) : Abs :=
  reduce { a with
           lo := typeLo a.signed a.w, hi := typeHi a.signed a.w,
           kv := kv &&& km &&& ones a.w, km := km &&& ones a.w }

/-- Known bits of a sum, as the verifier computes them: a carry can
reach every bit above an unknown one. -/
def addBits (a b : Abs) : Nat × Nat :=
  let sm := a.um + b.um
  let sv := a.kv + b.kv
  let sigma := sm + sv
  let chi := sigma ^^^ sv
  let mu := (chi ||| a.um ||| b.um) &&& ones a.w
  ((sv &&& (ones a.w ^^^ mu)) &&& ones a.w, ones a.w ^^^ mu)

/-- Known bits of a difference, likewise with borrows. -/
def subBits (a b : Abs) : Nat × Nat :=
  let m := modulus a.w
  let dv := (a.kv + m - b.kv) % m
  let alpha := dv + a.um
  let beta := (dv + m - b.um) % m
  let chi := alpha ^^^ beta
  let mu := (chi ||| a.um ||| b.um) &&& ones a.w
  ((dv &&& (ones a.w ^^^ mu)) &&& ones a.w, ones a.w ^^^ mu)

def add (a b : Abs) : Abs :=
  let (kv, km) := addBits a b
  let r := { a with kv, km }
  if a.fits (a.lo + b.lo) (a.hi + b.hi) then
    reduce { r with lo := a.lo + b.lo, hi := a.hi + b.hi }
  else r.withBits kv km

def sub (a b : Abs) : Abs :=
  let (kv, km) := subBits a b
  let r := { a with kv, km }
  if a.fits (a.lo - b.hi) (a.hi - b.lo) then
    reduce { r with lo := a.lo - b.hi, hi := a.hi - b.lo }
  else r.withBits kv km

/-- The number of low bits known zero. -/
def lowZeros (a : Abs) : Nat := Id.run do
  let mut k := 0
  for i in [0:a.w] do
    if a.km.testBit i && !a.kv.testBit i then k := k + 1 else return k
  return k

def mul (a b : Abs) : Abs :=
  match a.const?, b.const? with
  | some x, some y => const a.signed a.w (x * y)
  | _, _ =>
    let z := a.lowZeros + b.lowZeros
    let km := if z ≥ a.w then ones a.w else ones z
    let r := (top a.signed a.w).withBits 0 km
    if a.lo ≥ 0 && b.lo ≥ 0 && a.fits (a.lo * b.lo) (a.hi * b.hi) then
      reduce { r with lo := a.lo * b.lo, hi := a.hi * b.hi }
    else r

/-- `x / y` with `x / 0 = 0`, the kernel's semantics; truncating for
signed operands. -/
def divInt (x y : Int) : Int := if y == 0 then 0 else Int.tdiv x y

/-- `x % y` with `x % 0 = x`. -/
def modInt (x y : Int) : Int := if y == 0 then x else Int.tmod x y

def div (a b : Abs) : Abs :=
  match a.const?, b.const? with
  | some x, some y => const a.signed a.w (divInt x y)
  | _, some y =>
    if y > 0 && a.lo ≥ 0 then
      reduce { top a.signed a.w with
               lo := Int.tdiv a.lo y, hi := Int.tdiv a.hi y }
    else if y == 0 then const a.signed a.w 0
    else top a.signed a.w
  | _, _ =>
    -- an unsigned quotient never exceeds the dividend, and is 0 for a
    -- zero divisor
    if a.lo ≥ 0 && b.lo ≥ 0 then
      reduce { top a.signed a.w with lo := 0, hi := a.hi }
    else top a.signed a.w

def mod (a b : Abs) : Abs :=
  match a.const?, b.const? with
  | some x, some y => const a.signed a.w (modInt x y)
  | _, some y =>
    if y == 0 then a
    else if y > 0 && a.lo ≥ 0 then
      if a.hi < y then a
      else
        let r := reduce { top a.signed a.w with lo := 0, hi := y - 1 }
        -- a power of two keeps the low bits exactly
        if y.toNat &&& (y.toNat - 1) == 0 then
          let low := y.toNat - 1
          r.meet ((top a.signed a.w).withBits (a.kv &&& low)
            ((a.km &&& low) ||| (ones a.w ^^^ low)))
        else r
    else top a.signed a.w
  | _, _ =>
    if a.lo ≥ 0 && b.lo ≥ 0 then
      let hi := if b.lo ≥ 1 then min a.hi (b.hi - 1) else a.hi
      reduce { top a.signed a.w with lo := 0, hi }
    else top a.signed a.w

def band (a b : Abs) : Abs :=
  let alpha := a.kv ||| a.um
  let beta := b.kv ||| b.um
  let kv := a.kv &&& b.kv
  let um := alpha &&& beta &&& (ones a.w ^^^ kv)
  let r := (top a.signed a.w).withBits kv (ones a.w ^^^ um)
  if a.lo ≥ 0 && b.lo ≥ 0 then
    reduce { r with lo := 0, hi := min a.hi b.hi }
  else r

def bor (a b : Abs) : Abs :=
  let kv := a.kv ||| b.kv
  let um := (a.um ||| b.um) &&& (ones a.w ^^^ kv)
  let r := (top a.signed a.w).withBits kv (ones a.w ^^^ um)
  if a.lo ≥ 0 && b.lo ≥ 0 then
    reduce { r with lo := max a.lo b.lo }
  else r

def bxor (a b : Abs) : Abs :=
  let kv := a.kv ^^^ b.kv
  let um := a.um ||| b.um
  (top a.signed a.w).withBits kv (ones a.w ^^^ um)

/-- The shift amount, masked to the width as the kernel masks it. -/
def shiftAmount (a : Abs) (b : Abs) : Option Nat :=
  b.const?.map fun c => (toBits a.w c) % a.w

def shl (a b : Abs) : Abs :=
  match shiftAmount a b with
  | some c =>
    let kv := (a.kv <<< c) &&& ones a.w
    let km := ((a.km <<< c) ||| ones c) &&& ones a.w
    let r := (top a.signed a.w).withBits kv km
    if a.lo ≥ 0 && a.fits (a.lo <<< c) (a.hi <<< c) then
      reduce { r with lo := a.lo <<< c, hi := a.hi <<< c }
    else r
  | none => top a.signed a.w

def shr (a b : Abs) : Abs :=
  match shiftAmount a b with
  | some c =>
    if a.signed && a.lo < 0 then top a.signed a.w
    else
      let kv := a.kv >>> c
      let km := (a.km >>> c) ||| (ones a.w ^^^ ones (a.w - c))
      let r := (top a.signed a.w).withBits kv km
      reduce { r with lo := a.lo >>> c, hi := a.hi >>> c }
  | none =>
    if a.lo ≥ 0 then reduce { top a.signed a.w with lo := 0, hi := a.hi }
    else top a.signed a.w

/-- `e as T`: truncation keeps the low bits; a widening extends by
zero or by sign; the same width reread in the other signedness keeps
the values that both readings share. -/
def cast (a : Abs) (signed : Bool) (w : Nat) : Abs :=
  if a.isEmpty then { top signed w with lo := 1, hi := 0 } else
  if w < a.w then
    let kv := a.kv &&& ones w
    let km := a.km &&& ones w
    let r := (top signed w).withBits kv km
    -- the whole interval lies in one window of the narrower width
    if a.hi - a.lo < Int.ofNat (modulus w) &&
        a.loBits >>> w == a.hiBits >>> w then
      let lo := fromBits signed w (a.loBits &&& ones w)
      let hi := fromBits signed w (a.hiBits &&& ones w)
      if lo ≤ hi then reduce { r with lo, hi } else r
    else r
  else if w > a.w then
    if !a.signed then
      -- zero extension: the same values, high bits known zero
      reduce { top signed w with
               lo := a.lo, hi := a.hi, kv := a.kv,
               km := a.km ||| (ones w ^^^ ones a.w) }
    else
      let sign := 2 ^ (a.w - 1)
      let high := ones w ^^^ ones a.w
      let signKnown := a.km &&& sign != 0
      let kv := if signKnown && a.kv &&& sign != 0 then a.kv ||| high else a.kv
      let km := if signKnown then a.km ||| high else a.km
      let r := (top signed w).withBits kv km
      if r.fits a.lo a.hi then reduce { r with lo := a.lo, hi := a.hi } else r
  else if signed == a.signed then a
  else
    let r := (top signed w).withBits a.kv a.km
    -- values below the sign bit read the same either way
    if a.lo ≥ 0 && a.hi < Int.ofNat (2 ^ (w - 1)) then
      reduce { r with lo := a.lo, hi := a.hi }
    else r

/-- A comparison decided from the intervals and the known bits. -/
def cmp (op : Core.CmpOp) (a b : Abs) : Tri :=
  if a.isEmpty || b.isEmpty then .yes else
  match op with
  | .lt => if a.hi < b.lo then .yes else if a.lo ≥ b.hi then .no else .maybe
  | .le => if a.hi ≤ b.lo then .yes else if a.lo > b.hi then .no else .maybe
  | .gt => if a.lo > b.hi then .yes else if a.hi ≤ b.lo then .no else .maybe
  | .ge => if a.lo ≥ b.hi then .yes else if a.hi < b.lo then .no else .maybe
  | .eq =>
    if a.hi < b.lo || b.hi < a.lo then .no
    else if (a.kv ^^^ b.kv) &&& a.km &&& b.km != 0 then .no
    else match a.const?, b.const? with
      | some x, some y => .ofBool (x == y)
      | _, _ => .maybe
  | .ne =>
    if a.hi < b.lo || b.hi < a.lo then .yes
    else if (a.kv ^^^ b.kv) &&& a.km &&& b.km != 0 then .yes
    else match a.const?, b.const? with
      | some x, some y => .ofBool (x != y)
      | _, _ => .maybe

/-- Both sides narrowed on the assumption that `a op b` holds. -/
def narrow (op : Core.CmpOp) (a b : Abs) : Abs × Abs :=
  match op with
  | .lt => (a.withInterval a.lo (min a.hi (b.hi - 1)),
            b.withInterval (max b.lo (a.lo + 1)) b.hi)
  | .le => (a.withInterval a.lo (min a.hi b.hi),
            b.withInterval (max b.lo a.lo) b.hi)
  | .gt => (a.withInterval (max a.lo (b.lo + 1)) a.hi,
            b.withInterval b.lo (min b.hi (a.hi - 1)))
  | .ge => (a.withInterval (max a.lo b.lo) a.hi,
            b.withInterval b.lo (min b.hi a.hi))
  | .eq => let m := a.meet b; (m, m)
  | .ne =>
    let a' := match b.const? with
      | some y =>
        if a.lo == y then a.withInterval (a.lo + 1) a.hi
        else if a.hi == y then a.withInterval a.lo (a.hi - 1)
        else a
      | none => a
    let b' := match a.const? with
      | some x =>
        if b.lo == x then b.withInterval (b.lo + 1) b.hi
        else if b.hi == x then b.withInterval b.lo (b.hi - 1)
        else b
      | none => b
    (a', b')

/-- `[lo, hi] & bits`, for messages. -/
def describe (a : Abs) : String :=
  if a.isEmpty then "empty"
  else if let some v := a.const? then toString v
  else s!"[{a.lo}, {a.hi}]" ++
    (if a.km != 0 then s!" with bits {a.kv} known under mask {a.km}" else "")

end Abs

/-- What the forward interpretation yields for an expression: an
integer of a known type, a constant of no type yet, which takes the
type of the operand it meets, as a literal does, a boolean, or nothing
when the expression is outside the fragment. -/
inductive AV where
  | int (a : Abs)
  | poly (v : Int)
  | bool (t : Tri)
  | none
  deriving Repr, Inhabited

namespace AV

/-- Two integer operands at one type, a constant taking the type of
the other. -/
def align : AV → AV → Option (Abs × Abs)
  | .int a, .int b =>
    if a.signed == b.signed && a.w == b.w then some (a, b) else Option.none
  | .int a, .poly v => some (a, Abs.const a.signed a.w v)
  | .poly v, .int b => some (Abs.const b.signed b.w v, b)
  | _, _ => Option.none

def join : AV → AV → AV
  | .int a, .int b => .int (a.join b)
  | .int a, .poly v | .poly v, .int a =>
    .int (a.join (Abs.const a.signed a.w v))
  | .poly v, .poly u => if v == u then .poly v else .none
  | .bool a, .bool b => .bool (a.join b)
  | _, _ => .none

def const? : AV → Option Int
  | .int a => a.const?
  | .poly v => some v
  | _ => Option.none

end AV

end Koit.Facts
