import Koit.Core.Syntax

/-!
Bytes and the kernel's arithmetic, the pure functions every level of
the semantics computes with: two's-complement patterns and their
reduction to a width, the total arithmetic of the instruction set,
comparison, byte order, and the read-modify-write of the atomic
updates. Memory is little-endian. Nothing here knows a language or a
state.
-/

namespace Koit.Machine

open Koit.Core (ArithOp CmpOp AtomicOp)

/-! ### Patterns -/

/-- `v` modulo `2^w`, as a natural number: the `w`-bit pattern of the
integer. -/
def toNatMod (v : Int) (w : Nat) : Nat :=
  let m := 2 ^ w
  if v ≥ 0 then v.toNat % m else (m - (v.natAbs % m)) % m

/-- `v` reduced to the range of `int(s,w)`. -/
def wrap (signed : Bool) (w : Nat) (v : Int) : Int :=
  let r : Int := toNatMod v w
  if signed && r ≥ 2 ^ (w - 1) then r - 2 ^ w else r

/-- The bytes of the pattern `x` of width `w` reversed: `hton` and
`ntoh` on this little-endian machine. -/
def bswap (w : Nat) (x : Nat) : Nat :=
  (List.range (w / 8)).foldl (fun acc i => acc * 256 + (x >>> (8 * i)) % 256) 0

/-! ### The kernel's arithmetic -/

/-- Division rounding toward zero, the kernel's for signed operands. -/
def tdiv (a b : Int) : Int :=
  let q : Int := a.natAbs / b.natAbs
  if (a < 0) != (b < 0) then -q else q

/-- The arithmetic and bitwise operators on `int(s,w)`, total: `x / 0`
is `0`, `x % 0` is `x`, shifts mask their amount to the width, and
everything wraps. -/
def arith (op : ArithOp) (signed : Bool) (w : Nat) (a b : Int) : Int :=
  let bits (x : Int) : Nat := toNatMod x w
  wrap signed w <| match op with
    | .add => a + b
    | .sub => a - b
    | .mul => a * b
    | .div => if b == 0 then 0 else if signed then tdiv a b else a / b
    | .mod => if b == 0 then a else if signed then a - b * tdiv a b else a % b
    | .band => bits a &&& bits b
    | .bor => bits a ||| bits b
    | .bxor => bits a ^^^ bits b
    | .shl => bits a <<< (bits b % w)
    | .shr =>
      let s := bits b % w
      if signed then
        -- arithmetic: floor division by 2^s
        if a ≥ 0 then a.toNat >>> s
        else -(((a.natAbs + 2 ^ s - 1) / 2 ^ s : Nat) : Int)
      else bits a >>> s

def compare (op : CmpOp) (a b : Int) : Bool :=
  match op with
  | .eq => a == b | .ne => a != b | .lt => a < b | .le => a ≤ b
  | .gt => a > b | .ge => a ≥ b

/-- The value an atomic update stores over the previous value `old`,
or none for a `cmpxchg` whose comparison fails. -/
def atomic (op : AtomicOp) (signed : Bool) (w : Nat) (old : Int) (args : List Int) :
    Option Int :=
  let arg (i : Nat) : Int := (args[i]?).getD 0
  match op with
  | .add => some (arith .add signed w old (arg 0))
  | .band => some (arith .band signed w old (arg 0))
  | .bor => some (arith .bor signed w old (arg 0))
  | .bxor => some (arith .bxor signed w old (arg 0))
  | .xchg => some (wrap signed w (arg 0))
  | .cmpxchg => if old == arg 0 then some (wrap signed w (arg 1)) else none

/-! ### Bytes -/

/-- The little-endian bytes of `v` in `n` bytes. -/
def leBytes (v : Nat) (n : Nat) : List UInt8 :=
  (List.range n).map fun i => UInt8.ofNat ((v >>> (8 * i)) % 256)

def beBytes (v : Nat) (n : Nat) : List UInt8 := (leBytes v n).reverse

def ofLe (bs : List UInt8) : Nat :=
  bs.foldr (fun b acc => acc * 256 + b.toNat) 0

def ofBe (bs : List UInt8) : Nat := ofLe bs.reverse

/-- The bytes `[off, off + n)` of `b`, zero past its end. -/
def slice (b : ByteArray) (off n : Nat) : List UInt8 :=
  (List.range n).map fun i => if off + i < b.size then b.get! (off + i) else 0

/-- `b` with `bs` written at `off`; a write past the end is dropped. -/
def blit (b : ByteArray) (off : Nat) (bs : List UInt8) : ByteArray :=
  bs.foldl (fun (acc, i) x => (if i < acc.size then acc.set! i x else acc, i + 1))
    (b, off) |>.1

def zeros (n : Nat) : ByteArray := ByteArray.mk (Array.replicate n 0)

def hexOf (bs : List UInt8) : String :=
  String.join (bs.map fun b =>
    let ds := Nat.toDigits 16 b.toNat
    (if ds.length < 2 then "0" else "") ++ String.ofList ds)

end Koit.Machine
