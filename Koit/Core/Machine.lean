import Koit.Check.Rules

/-!
The machine the dynamic semantics runs on: values, the total
arithmetic of the kernel's instruction set, byte memory for the
regions, the state of a run, what a helper may do, and the outcomes
a statement can have. The big-step relation of `Semantics.lean` and
the evaluator of `Interp.lean` are both written over these, so that
the evaluator is the relation's executable form.

Values are scalars: fixed-width integers normalized to their type's
range, byte-order values, booleans, and the location of a place for
the names a `let` binds to one. A literal or an untyped constant is
`poly`: it takes the width of the operand or the place it meets, as
it takes its type from the context in the static rules. Regions are
byte arrays: a map slot, the packet, a struct literal on the stack,
or a kernel object bound by `hold`; scalars local to a block live in
the frame's store.
-/

namespace Koit.Sem

open Koit (Span)
open Koit.Core
open Koit.Check (Env)
open Koit.Prelude (KindRow CallRow ResourceRow AcqArg Sig)

/-! ### Locations and values -/

/-- A region of bytes. -/
inductive Region where
  /-- A struct literal's bytes, numbered per run. -/
  | stack (id : Nat)
  /-- A slot of an array or per-CPU map, or an entry of a hash map by
  its number. -/
  | map (name : String) (slot : Nat)
  | pkt
  /-- An object the kernel handed out: a ring-buffer record, a
  socket. -/
  | kernel (id : Nat)
  deriving BEq, Repr, Inhabited

/-- A place: a region, an offset in it, the type of what is there,
and, for the packet, the layout token the location was made under,
so that a location into the packet is usable only while its token is
the current one. -/
structure Loc where
  region : Region
  off    : Nat
  ty     : Ty
  tok    : Nat := 0
  deriving Repr, Inhabited

/-- Values. A byte-order value is its stored bit pattern, the number
read little-endian from the bytes as they lie in memory, so that
`hton` and `ntoh` are byte swaps and equality compares patterns; the
width `0` marks `hton` of a constant of no type yet, whose pattern
is fixed when it meets a place or an operand. -/
inductive Val where
  | int (signed : Bool) (w : Nat) (v : Int) (poly : Bool := false)
  | be (w : Nat) (v : Nat)
  | bool (b : Bool)
  | loc (l : Loc)
  deriving Repr, Inhabited

/-- `v` modulo `2^w`, as a natural number. -/
def toNatMod (v : Int) (w : Nat) : Nat :=
  let m := 2 ^ w
  if v ≥ 0 then v.toNat % m else (m - (v.natAbs % m)) % m

/-- `v` reduced to the range of `int(s,w)`. -/
def wrap (signed : Bool) (w : Nat) (v : Int) : Int :=
  let r : Int := toNatMod v w
  if signed && r ≥ 2 ^ (w - 1) then r - 2 ^ w else r

namespace Val

def mkInt (signed : Bool) (w : Nat) (v : Int) (poly : Bool := false) : Val :=
  .int signed w (wrap signed w v) poly

def u64 (v : Nat) : Val := mkInt false 64 v
def u32 (v : Nat) : Val := mkInt false 32 v
def lit (v : Nat) : Val := mkInt false 64 v true

/-- The bytes of the pattern `x` of width `w` reversed: `hton` and
`ntoh` on this little-endian machine. -/
def bswap (w : Nat) (x : Nat) : Nat :=
  (List.range (w / 8)).foldl (fun acc i => acc * 256 + (x >>> (8 * i)) % 256) 0

/-- A byte-order value printed as the number it holds in network
order, swapping the stored pattern back. -/
def print : Val → String
  | .int _ _ v _ => toString v
  | .be w v =>
    let n := if w == 0 then v else bswap w v
    s!"be{w}(0x{String.ofList ((Nat.toDigits 16 n).map Char.toUpper)})"
  | .bool b => toString b
  | .loc l => s!"place at {repr l.region} + {l.off}"

/-- The integer a value denotes, for comparisons and indexes. -/
def toInt? : Val → Option Int
  | .int _ _ v _ => some v
  | .be _ v => some v
  | .bool b => some (if b then 1 else 0)
  | .loc _ => none

/-- Whether the value is true, for conditions. -/
def truthy : Val → Bool
  | .bool b => b
  | .int _ _ v _ => v != 0
  | .be _ v => v != 0
  | .loc _ => true

end Val

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

/-- The width two operands meet at: a `poly` operand takes the other's
type, and two `poly` operands are `u64`. -/
def meetInts : Val → Val → Option (Bool × Nat × Int × Int × Bool)
  | .int s w a pa, .int s' w' b pb =>
    if pa && !pb then some (s', w', wrap s' w' a, b, false)
    else if pb && !pa then some (s, w, a, wrap s w b, false)
    else if pa && pb then some (false, 64, wrap false 64 a, wrap false 64 b, true)
    else if s == s' && w == w' then some (s, w, a, b, false)
    else none
  | _, _ => none

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

/-- A scalar value decoded from bytes by its normalized type; a
byte-order value is the pattern as stored. -/
def decode (t : Ty) (bs : List UInt8) : Option Val :=
  match t with
  | .int _ s w => some (Val.mkInt s w (ofLe bs))
  | .be _ w => some (.be w (ofLe bs))
  | .bool _ => some (.bool (bs.any (· != 0)))
  | _ => none

/-- A byte-order value fitted to a place of width `w`: a pattern
keeps its low bytes, a constant of no width yet is swapped into
place, and an untyped integer is `hton` of itself. -/
def fitBe (w : Nat) : Val → Val
  | .be 0 x => .be w (Val.bswap w (toNatMod x w))
  | .be _ x => .be w (toNatMod x w)
  | .int _ _ x _ => .be w (Val.bswap w (toNatMod x w))
  | v => v

/-- Two byte-order operands at one pattern width: a constant of no
width yet takes the other's. -/
def meetBe (w : Nat) (x : Nat) (w' : Nat) (y : Nat) : Option (Nat × Nat) :=
  if w == 0 && w' == 0 then some (x, y)
  else if w == 0 then some (Val.bswap w' (toNatMod x w'), y)
  else if w' == 0 then some (x, Val.bswap w (toNatMod y w))
  else if w == w' then some (x, y)
  else none

/-- A scalar value encoded for a place of normalized type `t`, a
`poly` value taking the place's width. -/
def encode (t : Ty) (v : Val) : Option (List UInt8) :=
  match t, v with
  | .int _ s w, .int _ _ x _ => some (leBytes (toNatMod (wrap s w x) w) (w / 8))
  | .be _ w, .be _ _ | .be _ w, .int _ _ _ true =>
    match fitBe w v with
    | .be _ x => some (leBytes x (w / 8))
    | _ => none
  | .bool _, .bool b => some [if b then 1 else 0]
  | _, _ => none

/-! ### The state of a run -/

/-- A map's contents: slots by number for the array kinds, entries by
number for a hash map, submitted records for a ring buffer. A slot
not yet written is all zero. -/
structure MapState where
  decl      : MapDecl
  valueTy   : Ty
  valueSize : Nat
  keyTy     : Option Ty := none
  keySize   : Nat := 0
  capacity  : Nat
  slots     : List (Nat × ByteArray) := []
  entries   : List (Nat × List UInt8 × ByteArray) := []
  ring      : List ByteArray := []
  nextEntry : Nat := 0
  deriving Inhabited

/-- What a name in the frame denotes. -/
inductive Binding where
  | val (v : Val)
  | place (l : Loc)
  /-- An owned name after `move`. -/
  | moved
  deriving Repr, Inhabited

/-- What the kernel answered a call with, as the trace records it. -/
inductive CallOut where
  | ok (v : Option Val)
  | failed (errno : Int)
  deriving Repr, Inhabited

/-- One event of the trace: a kernel call with its row, its arguments,
and its answer, or a `printk` with its format and arguments. What a
run does outside the model is this list, in order. -/
inductive Event where
  | call (row : String) (args : List Val) (out : CallOut)
  | print (fmt : String) (args : List Val)
  deriving Repr, Inhabited

/-- A held resource, innermost first in the state. -/
structure HeldRes where
  row  : ResourceRow
  name : Option String
  /-- The record's map, for a ring-buffer record. -/
  map  : Option String := none
  obj  : Option Loc := none
  deriving Inhabited

structure State where
  env        : Env
  kind       : KindRow
  packet     : ByteArray := ByteArray.empty
  /-- The layout token: dropped by a resize, so that a view carved
  before it is dead. -/
  layout     : Nat := 0
  ctx        : List (String × Val) := []
  maps       : List (String × MapState) := []
  stackBufs  : List (Nat × ByteArray) := []
  kernelObjs : List (Nat × ByteArray) := []
  nextId     : Nat := 0
  /-- The frame's store: the names in scope, innermost first. -/
  locals     : List (String × Binding) := []
  held       : List HeldRes := []
  /-- The negative return of the last helper that failed. -/
  errno      : Int := 0
  fuel       : Nat := 100000
  clock      : Nat := 0
  /-- The kernel calls made so far and the `printk` events, in
  order. -/
  trace      : List Event := []
  deriving Inhabited

namespace State

def region (st : State) : Region → ByteArray
  | .stack id => (st.stackBufs.lookup id).getD ByteArray.empty
  | .map m slot =>
    match st.maps.lookup m with
    | some ms =>
      match ms.decl.kind with
      | .hash .. => ((ms.entries.find? (·.1 == slot)).map (·.2.2)).getD
          (zeros ms.valueSize)
      | _ => (ms.slots.lookup slot).getD (zeros ms.valueSize)
    | none => ByteArray.empty
  | .pkt => st.packet
  | .kernel id => (st.kernelObjs.lookup id).getD ByteArray.empty

def setRegion (st : State) : Region → ByteArray → State
  | .stack id, b =>
    { st with stackBufs := (id, b) :: st.stackBufs.filter (·.1 != id) }
  | .map m slot, b =>
    { st with maps := st.maps.map fun (n, ms) =>
        if n != m then (n, ms) else
        match ms.decl.kind with
        | .hash .. =>
          (n, { ms with entries := ms.entries.map fun (i, k, v) =>
                  if i == slot then (i, k, b) else (i, k, v) })
        | _ => (n, { ms with slots := (slot, b) :: ms.slots.filter (·.1 != slot) }) }
  | .pkt, b => { st with packet := b }
  | .kernel id, b =>
    { st with kernelObjs := (id, b) :: st.kernelObjs.filter (·.1 != id) }

def bytesAt (st : State) (l : Loc) (n : Nat) : List UInt8 :=
  slice (st.region l.region) l.off n

def writeAt (st : State) (l : Loc) (bs : List UInt8) : State :=
  st.setRegion l.region (blit (st.region l.region) l.off bs)

def local? (st : State) (x : String) : Option Binding :=
  (st.locals.find? (·.1 == x)).map (·.2)

def bind (st : State) (x : String) (b : Binding) : State :=
  { st with locals := (x, b) :: st.locals }

def rebind (st : State) (x : String) (b : Binding) : State :=
  { st with locals := st.locals.map fun (y, b') =>
      if y == x then (y, b) else (y, b') }

def fresh (st : State) : Nat × State :=
  (st.nextId, { st with nextId := st.nextId + 1 })

/-- The trace with an event appended. -/
def record (st : State) (ev : Event) : State :=
  { st with trace := st.trace ++ [ev] }

end State

/-! ### Outcomes -/

/-- How a statement ends: normally, leaving a loop, returning a value,
raising a failure with its reason, or, for the cases the theorems
make unreachable, an error. -/
inductive Outcome where
  | normal
  | brk
  | cont
  | ret (v : Option Val)
  | raise (k : Kind) (reason : Nat)
  | err (msg : String)
  deriving Repr, Inhabited

/-- What a fallible operation yields: a value, a place, nothing, or a
failure. -/
inductive FallOut where
  | ok (b : Option Binding)
  | failed
  | err (msg : String)
  deriving Repr, Inhabited

/-! ### The kernel -/

/-- What a kernel function does when called: a result and a new
state, a failure with the negative return the `helper` reason
defaults to, or an error the kernel's contract excludes. -/
inductive HelperOut where
  | ok (v : Option Val) (st : State)
  | failed (errno : Int) (st : State)
  | err (msg : String)
  deriving Inhabited

/-- A kernel: what each helper of the call table does on the
evaluated arguments, one of the relations the contracts allow. The
semantics is stated for every kernel; the evaluator runs a synthetic
one. -/
structure Kernel where
  helper : CallRow → List Val → State → HelperOut

/-- The initial state of a program: the packet, the context fields at
their given values or zero, and the maps as they are. -/
def initState (env : Env) (row : KindRow) (packet : ByteArray)
    (ctx : List (String × Nat)) (maps : List (String × MapState)) (fuel : Nat) :
    State :=
  { env, kind := row, packet, maps, fuel,
    ctx := row.ctx.map fun f =>
      (f.name, Val.mkInt false 32 ((ctx.lookup f.name).getD 0)) }

/-! ### The evaluation monad and its primitives -/

/-- The release of the innermost held resource, normally or
abnormally: a ring-buffer record is submitted or discarded; the
others leave no trace here. A resource `move` handed away is no
longer held and is not released. -/
def releaseRes (st : State) (normal : Bool) (x : Option String) : State :=
  match st.held with
  | h :: rest =>
    if x.isSome && h.name != x then st else
    let st := { st with held := rest }
    match h.map, h.obj with
    | some m, some l =>
      if normal then
        let rec_ := st.region l.region
        { st with maps := st.maps.map fun (p : String × MapState) =>
          if p.1 == m then (p.1, { p.2 with ring := p.2.ring ++ [rec_] }) else p }
      else st
    | _, _ => st
  | [] => st

/-- The frame's locals restored to `n` entries after a block, keeping
the stores to the outer names, which are updated in place. -/
def State.dropLocalsTo (st : State) (n : Nat) : State :=
  { st with locals := st.locals.drop (st.locals.length - n) }

/-- What leaves a statement without returning to it: a failure on its
way to the program's handler, or an error. -/
inductive Abort where
  | raise (k : Kind) (reason : Nat)
  | err (msg : String)
  deriving Repr, Inhabited

/-- The evaluation monad: exceptions over state, so that a failure on
its way to the program's handler carries the state it left, maps
written and resources released, as the relation's rules do. -/
abbrev M := ExceptT Abort (StateM State)

/-- A primitive applied in a state: its result and the state after,
or the abort. -/
def M.exec (f : M α) (st : State) : Except Abort (α × State) :=
  match (f.run).run st with
  | (.ok v, st') => .ok (v, st')
  | (.error e, _) => .error e

def fail (msg : String) : M α := throw (.err msg)

/-- A checker operation, whose failure here is an error. -/
def lift (x : Koit.Check.M α) : M α :=
  match x with
  | .ok v => pure v
  | .error d => fail s!"{d}"

def getEnv : M Env := do return (← get).env

def norm (t : Ty) : M Ty := do lift ((← getEnv).norm t)

def sizeOf (t : Ty) : M Nat := do return (← lift ((← getEnv).layout t)).1

/-- A field's offset and type in a struct type. -/
def fieldOf (t : Ty) (f : String) : M (Nat × Ty) := do
  let env ← getEnv
  match ← norm t with
  | .struct _ fields =>
    match ← lift (Koit.Check.fieldOffset env t f), fields.find? (·.name == f) with
    | some o, some fd => return (o, fd.ty)
    | _, _ => fail s!"no field `{f}`"
  | _ => fail s!"`{f}` of a type without fields"

def constNat (e : Expr) : M Nat := do
  match (← getEnv).evalConst e with
  | some v => return v.toNat
  | none => fail s!"`{e.print}` is not a constant"

/-- A value fitted to a place or declaration of type `t`: a `poly`
value takes its width. -/
partial def coerceTo (t : Ty) (v : Val) : M Val := do
  match ← norm t, v with
  | .int _ s w, .int _ _ x _ => return Val.mkInt s w x
  | .int _ s w, .bool b => return Val.mkInt s w (if b then 1 else 0)
  | .be _ w, .be _ _ | .be _ w, .int _ _ _ true => return fitBe w v
  | .refined _ _ base _, v => coerceTo base v
  | _, v => return v

/-- A `poly` value settled, as a binding with no declared type does:
`u64`. -/
def settle : Val → Val
  | .int _ _ x true => Val.mkInt false 64 x
  | .be 0 x => fitBe 64 (.be 0 x)
  | v => v

/-- A place as the evaluator addresses it. -/
inductive PlaceRef where
  | local (x : String)
  | ctx (f : String)
  | mem (l : Loc)
  deriving Repr, Inhabited

def useFuel : M Unit := do
  let st ← get
  if st.fuel == 0 then fail "out of fuel"
  set { st with fuel := st.fuel - 1 }

def dropTo (n : Nat) : M Unit := modify (·.dropLocalsTo n)

/-- Whether a place holds a scalar, which an argument reads, as
opposed to an aggregate, which is passed by its location. -/
def scalarRef (st : State) : PlaceRef → Bool
  | .mem l =>
    match (norm l.ty).exec st with
    | .ok (tn, _) => tn.isScalar
    | .error _ => false
  | _ => true

/-- A hash map's key and value bytes at a place. -/
def bytesOfPlace (r : PlaceRef) (n : Nat) : M (List UInt8) := do
  match r with
  | .mem l => return (← get).bytesAt l n
  | _ => fail "an aggregate is expected"

def loadPlace (r : PlaceRef) : M Val := do
  let st ← get
  match r with
  | .local x =>
    match st.local? x with
    | some (.val v) => return v
    | some (.place l) => return .loc l
    | _ => fail s!"`{x}` has no value"
  | .ctx f =>
    match st.ctx.lookup f with
    | some v => return v
    | none => fail s!"the context has no field `{f}`"
  | .mem l =>
    let t ← norm l.ty
    let n ← sizeOf t
    match decode t (st.bytesAt l n) with
    | some v => return v
    | none => fail s!"a load of an aggregate `{l.ty.print}`"

def storePlace (r : PlaceRef) (v : Val) : M Unit := do
  let st ← get
  match r with
  | .local x =>
    match st.local? x with
    | some (.val old) =>
      let v := match old with
        | .int s w _ _ => Val.mkInt s w ((v.toInt?).getD 0)
        | .be w _ => fitBe w v
        | _ => v
      set (st.rebind x (.val v))
    | _ => fail s!"a store to `{x}`, which is not a scalar local"
  | .ctx f =>
    set { st with ctx := st.ctx.map fun (g, w) => if g == f then (g, v) else (g, w) }
  | .mem l =>
    let t ← norm l.ty
    match encode t v with
    | some bs => set (st.writeAt l bs)
    | none => fail s!"a store of {v.print} into a `{l.ty.print}`"

/-- A helper's failure, with its negative return as `errno`. -/
def helperFailed (errno : Int) : M Unit :=
  modify fun st => { st with errno }

/-- The frame a field predicate is evaluated in, at a marked load:
the field bound to the value loaded and every scalar sibling to its
value at the place, built from the fields in order. -/
def siblingFrame (l : Loc) (fields : List Field) (f : String) (v : Val) :
    M (List (String × Binding)) := do
  let mut frame : List (String × Binding) := [(f, .val v)]
  for g in fields do
    if g.name != f && (← norm g.ty).isScalar then
      let (o, _) ← fieldOf l.ty g.name
      let gv ← loadPlace (.mem { l with off := l.off + o, ty := g.ty })
      frame := (g.name, .val gv) :: frame
  return frame

/-- Bytes formatted for `printk`'s `{}`. -/
def fmtArgs (fmt : String) (args : List Val) : String :=
  let parts := fmt.splitOn "{}"
  let rec go : List String → List Val → String
    | [], _ => ""
    | [p], _ => p
    | p :: ps, a :: as => p ++ a.print ++ go ps as
    | p :: ps, [] => p ++ "{}" ++ go ps []
  go parts args

/-- The lines `printk` wrote, read off the trace. -/
def State.log (st : State) : List String :=
  st.trace.filterMap fun
    | .print fmt args => some (fmtArgs fmt args)
    | _ => none

end Koit.Sem
