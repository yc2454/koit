import Koit.Machine.Ops
import Koit.Check.Rules

/-!
The state of a Core run and the values it holds. The observable
half, the maps, the packet, the kernel objects, the held stack, and
the trace, is the shared state of `Koit.Machine`, embedded as one
field; the rest is Core's own: the frame of names bound to values,
places, or marked moved, the struct literals' bytes, the context by
field name, `errno`, and the evaluator's fuel. The big-step relation
of `Semantics.lean` and the evaluator of `Interp.lean` are both
written over these, so that the evaluator is the relation's
executable form, and both reach the shared state only through the
operations of `Koit.Machine.Ops`.

Values are scalars: fixed-width integers normalized to their type's
range, byte-order values, booleans, and the location of a place for
the names a `let` binds to one. A literal or an untyped constant is
`poly`: it takes the width of the operand or the place it meets, as
it takes its type from the context in the static rules. A location's
region is one of the machine's, or a struct literal's frame, which
is Core's alone.
-/

namespace Koit.Core.Sem

open Koit (Span)
open Koit.Core
open Koit.Check (Env)
open Koit.Interface (KindRow CallRow ResourceRow AcqArg Sig)
open Koit.Machine (toNatMod wrap leBytes ofLe slice blit zeros bswap Kernel HeldObj)

/-! ### Locations and values -/

/-- A region of bytes: one of the machine's, or a struct literal's
frame, numbered per run. -/
inductive Region where
  | shared (r : Machine.Region)
  | stack (id : Nat)
  deriving BEq, Repr, Inhabited

namespace Region

def map (m : String) (slot : Nat) : Region := .shared (.map m slot)
def pkt : Region := .shared .pkt
def kernel (id : Nat) : Region := .shared (.kernel id)

def isPkt : Region → Bool
  | .shared .pkt => true
  | _ => false

/-- The machine's region, for a location the shared state can
describe. -/
def shared? : Region → Option Machine.Region
  | .shared r => some r
  | .stack _ => none

end Region

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

/-- The object a location names on the held stack: the field of a map
value for a lock, the kernel object for a record or a socket. -/
def Loc.heldObj (l : Loc) : Option HeldObj :=
  match l.region with
  | .shared (.map m i) => some (.slot m i l.off)
  | .shared (.kernel id) => some (.object id)
  | _ => none

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

namespace Val

def mkInt (signed : Bool) (w : Nat) (v : Int) (poly : Bool := false) : Val :=
  .int signed w (wrap signed w v) poly

def u64 (v : Nat) : Val := mkInt false 64 v
def u32 (v : Nat) : Val := mkInt false 32 v
def lit (v : Nat) : Val := mkInt false 64 v true

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

/-- The value as the kernel and the trace see it: an integer, a
byte-order value as its pattern, a boolean as 0 or 1, and an object
the kernel handed out by its number. -/
def observe : Val → Machine.Val
  | .int _ _ v _ => .scalar v
  | .be _ v => .scalar v
  | .bool b => .scalar (if b then 1 else 0)
  | .loc l =>
    match l.region with
    | .shared (.kernel id) => .object id
    | _ => .scalar 0

end Val

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
  | .be 0 x => .be w (bswap w (toNatMod x w))
  | .be _ x => .be w (toNatMod x w)
  | .int _ _ x _ => .be w (bswap w (toNatMod x w))
  | v => v

/-- Two byte-order operands at one pattern width: a constant of no
width yet takes the other's. -/
def meetBe (w : Nat) (x : Nat) (w' : Nat) (y : Nat) : Option (Nat × Nat) :=
  if w == 0 && w' == 0 then some (x, y)
  else if w == 0 then some (bswap w' (toNatMod x w'), y)
  else if w' == 0 then some (x, bswap w (toNatMod y w))
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

/-- What a name in the frame denotes. -/
inductive Binding where
  | val (v : Val)
  | place (l : Loc)
  /-- An owned name after `move`. -/
  | moved
  deriving Repr, Inhabited

structure State where
  env        : Env
  kind       : KindRow
  /-- The shared state: what every level of the lowering acts on. -/
  machine    : Machine.State := {}
  ctx        : List (String × Val) := []
  /-- The struct literals' bytes, by number. -/
  stackBufs  : List (Nat × ByteArray) := []
  nextStack  : Nat := 0
  /-- The frame's store: the names in scope, innermost first. -/
  locals     : List (String × Binding) := []
  /-- The negative return of the last helper that failed. -/
  errno      : Int := 0
  fuel       : Nat := 100000
  deriving Inhabited

namespace State

def region (st : State) : Region → ByteArray
  | .shared r => st.machine.region r
  | .stack id => (st.stackBufs.lookup id).getD ByteArray.empty

def setRegion (st : State) : Region → ByteArray → State
  | .shared r, b => { st with machine := st.machine.setRegion r b }
  | .stack id, b =>
    { st with stackBufs := (id, b) :: st.stackBufs.filter (·.1 != id) }

def bytesAt (st : State) (l : Loc) (n : Nat) : List UInt8 :=
  slice (st.region l.region) l.off n

def writeAt (st : State) (l : Loc) (bs : List UInt8) : State :=
  st.setRegion l.region (blit (st.region l.region) l.off bs)

/-- Whether an access of `n` bytes at `l` is admitted: the token is
current for the packet and the bytes lie in the region. -/
def admits (st : State) (l : Loc) (n : Nat) : Bool :=
  match l.region with
  | .shared r => st.machine.admits r l.off n l.tok
  | .stack _ => l.off + n ≤ (st.region l.region).size

def local? (st : State) (x : String) : Option Binding :=
  (st.locals.find? (·.1 == x)).map (·.2)

def bind (st : State) (x : String) (b : Binding) : State :=
  { st with locals := (x, b) :: st.locals }

def rebind (st : State) (x : String) (b : Binding) : State :=
  { st with locals := st.locals.map fun (y, b') =>
      if y == x then (y, b) else (y, b') }

/-- Whether an owned name has been moved on this path. -/
def moved (st : State) (x : Option String) : Bool :=
  match x with
  | some x => (st.local? x matches some .moved)
  | none => false

/-- A fresh struct literal's number. -/
def freshStack (st : State) : Nat × State :=
  (st.nextStack, { st with nextStack := st.nextStack + 1 })

/-- The shared parts, read through the state. -/
def maps (st : State) := st.machine.maps
def packet (st : State) := st.machine.packet
def layout (st : State) := st.machine.layout
def held (st : State) := st.machine.held
def trace (st : State) := st.machine.trace

def record (st : State) (ev : Machine.Event) : State :=
  { st with machine := st.machine.record ev }

/-- The lines `printk` wrote. -/
def log (st : State) : List String := st.machine.log

/-- The frame's locals restored to `n` entries after a block, keeping
the stores to the outer names, which are updated in place. -/
def dropLocalsTo (st : State) (n : Nat) : State :=
  { st with locals := st.locals.drop (st.locals.length - n) }

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

/-- The initial state of a program: the packet, the context fields at
their given values or zero, and the maps as they are. -/
def initState (env : Env) (row : KindRow) (packet : ByteArray)
    (ctx : List (String × Nat)) (maps : List (String × Machine.MapState)) (fuel : Nat) :
    State :=
  { env, kind := row, fuel,
    machine := { maps, packet },
    ctx := row.ctx.map fun f =>
      (f.name, Val.mkInt false 32 ((ctx.lookup f.name).getD 0)) }

/-! ### The evaluation monad and its primitives -/

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
  match (ExceptT.run f).run st with
  | (.ok v, st') => .ok (v, st')
  | (.error e, _) => .error e

def fail (msg : String) : M α := throw (.err msg)

/-- An operation of the shared machine, applied to the shared half of
the state; its error is an error here. -/
def op (f : Machine.Op α) : M α := do
  let st ← get
  match f.exec st.machine with
  | .ok (a, m) => set { st with machine := m }; return a
  | .error msg => fail msg

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

/-! ### Kernel functions and releases through the machine -/

/-- An argument as the kernel sees it, fitted to its parameter: a
scalar reduced to the parameter's type, a `ref` or `view` place as
its bytes, an owned reference as its object. -/
def kernelArg (p : Param) (v : Val) : M Machine.Val := do
  match ← norm p.ty, v with
  | .own .., .loc l =>
    match l.region with
    | .shared (.kernel id) => return .object id
    | _ => fail s!"`{p.name}` takes an owned reference"
  | .ref _ t, .loc l | .view _ t, .loc l =>
    let n ← sizeOf t
    unless (← get).admits l n do fail s!"`{p.name}` reads outside its region"
    return .bytes ((← get).bytesAt l n)
  | .ref .., _ | .view .., _ | .own .., _ => fail s!"`{p.name}` takes a place"
  | t, v =>
    match ← coerceTo t v with
    | .loc _ => fail s!"`{p.name}` takes a scalar"
    | v' => return v'.observe

/-- The kernel's answer at the row's result type: an integer at the
type, or the location of the object handed out. -/
def kernelResult (ret : Option Ty) (v : Machine.Val) : M Val := do
  match ret, v with
  | some t, .object id =>
    let pointee := match t with
      | .own _ u | .ref _ u => u
      | u => u
    return .loc { region := .kernel id, off := 0, ty := pointee }
  | some t, .scalar x =>
    match ← norm t with
    | .int _ s w => return Val.mkInt s w x
    | .bool _ => return .bool (x != 0)
    | .refined _ _ base _ =>
      match ← norm base with
      | .int _ s w => return Val.mkInt s w x
      | _ => return Val.mkInt true 64 x
    | _ => return Val.mkInt true 64 x
  | _, v => return Val.mkInt true 64 v.toInt

/-- A kernel function through the shared machine: the arguments as
the kernel sees them, the call with its trace event and its effect
on the held stack, and the result at the row's type; `none` on a
failure, with `errno` set to its negative return. -/
def kernelCall (K : Kernel) (row : CallRow) (params : List Param) (ret : Option Ty)
    (args : List Val) : M (Option (Option Val)) := do
  let st ← get
  let vs ← (params.zip args).mapM fun (p, v) => kernelArg p v
  match ← op (Machine.call st.env.interface K st.kind row vs) with
  | .ok v =>
    match v with
    | some v => return some (some (← kernelResult ret v))
    | none => return some none
  | .failed n =>
    helperFailed n
    return none

/-- The release at the exit of a `hold`, normally or abnormally, as
the innermost entry's row says; nothing when `move` handed the
resource away. -/
def release (K : Kernel) (normal : Bool) (moved : Bool) : M Unit := do
  if moved then return
  let st ← get
  op (Machine.release st.env.interface K st.kind normal)

end Koit.Core.Sem
