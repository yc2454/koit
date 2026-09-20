import Koit.Machine.Bytes
import Koit.Interface.Rows

/-!
The world every level of the semantics acts on: the part of a run's
state that the kernel and userspace can observe, and that is one
definition shared verbatim by Core, LIR, and the target machine. It
holds the maps, the packet with its layout token, the objects the
kernel handed out, the held stack of resources, and the trace of
kernel calls and `printk` events. Each level's own state embeds it as
a field beside that level's private half, its locals or registers,
and the correctness theorems of the lowering ask that two runs end
with this structure equal.

Nothing in it refers to a location of any level. The memory it
addresses is three regions, a map slot, the packet, and a kernel
object, which every level reaches the same way; a level's own memory,
Core's struct literals or the target's frame, is that level's. A held
object is a map slot's field or a kernel object; a traced memory
argument is the bytes the kernel received.
-/

namespace Koit.Machine

open Koit.Core (Ty MapDecl Resource)
open Koit.Interface (ResourceRow)

/-! ### Regions and what the kernel sees -/

/-- A region of the shared memory. -/
inductive Region where
  /-- A slot of an array or per-CPU map, or an entry of a hash map by
  its number. -/
  | map (name : String) (slot : Nat)
  | pkt
  /-- An object the kernel handed out: a ring-buffer record, a
  socket. -/
  | kernel (id : Nat)
  deriving BEq, DecidableEq, Repr, Inhabited

/-- What the kernel sees of an argument or hands back: a scalar, the
bytes a memory argument pointed at, or an object it owns. This is
what the trace records and what the kernel parameter receives, so a
kernel call reads the same at every level. -/
inductive Val where
  | scalar (v : Int)
  | bytes (bs : List UInt8)
  | object (id : Nat)
  deriving BEq, DecidableEq, Repr, Inhabited

def Val.toInt : Val → Int
  | .scalar v => v
  | .bytes bs => ofLe bs
  | .object id => id

def Val.print : Val → String
  | .scalar v => toString v
  | .bytes bs => "0x" ++ hexOf bs
  | .object id => s!"object {id}"

/-! ### Maps -/

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

/-! ### The protocol state and the trace -/

/-- The object a held entry releases, described without a location:
a lock by the field of the map value it lies in, a record or a
socket by its kernel object. -/
inductive HeldObj where
  | slot (m : String) (i : Nat) (off : Nat)
  | object (id : Nat)
  deriving BEq, DecidableEq, Repr, Inhabited

/-- A held resource, innermost first in the state. -/
structure HeldRes where
  row  : ResourceRow
  /-- The ring a record belongs to, for its submission. -/
  ring : Option String := none
  obj  : Option HeldObj := none
  deriving Inhabited

/-- Two held entries are the same resource on the same object. -/
def HeldRes.same (a b : HeldRes) : Bool :=
  a.row.res == b.row.res && a.obj == b.obj

/-- What the kernel answered a call with, as the trace records it. -/
inductive CallOut where
  | ok (v : Option Val)
  | failed (errno : Int)
  deriving BEq, DecidableEq, Repr, Inhabited

/-- One event of the trace: a kernel call with its row, its arguments,
and its answer, or a `printk` with its format and arguments. What a
run does outside the model is this list, in order. -/
inductive Event where
  | call (row : String) (args : List Val) (out : CallOut)
  | print (fmt : String) (args : List Val)
  deriving BEq, DecidableEq, Repr, Inhabited

/-! ### The state -/

structure State where
  maps       : List (String × MapState) := []
  packet     : ByteArray := ByteArray.empty
  /-- The layout token: changed by a resize, so that a location into
  the packet made before it is dead. -/
  layout     : Nat := 0
  kernelObjs : List (Nat × ByteArray) := []
  /-- The next kernel object's number. -/
  nextId     : Nat := 0
  held       : List HeldRes := []
  /-- The kernel calls made so far and the `printk` events, in
  order. -/
  trace      : List Event := []
  /-- The kernel's own clock, for the synthetic kernel's `ktime`. -/
  clock      : Nat := 0
  deriving Inhabited

namespace State

def region (st : State) : Region → ByteArray
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

def bytesAt (st : State) (r : Region) (off n : Nat) : List UInt8 :=
  slice (st.region r) off n

def writeAt (st : State) (r : Region) (off : Nat) (bs : List UInt8) : State :=
  st.setRegion r (blit (st.region r) off bs)

/-- Whether an access of `n` bytes at `off` in `r`, made under the
token `tok`, is admitted: the token is current for the packet and
the bytes lie in the region. -/
def admits (st : State) (r : Region) (off n tok : Nat) : Bool :=
  (r != .pkt || tok == st.layout) && off + n ≤ (st.region r).size

def map? (st : State) (m : String) : Option MapState := st.maps.lookup m

def setMap (st : State) (m : String) (ms : MapState) : State :=
  { st with maps := st.maps.map fun (n, x) => if n == m then (n, ms) else (n, x) }

/-- A fresh kernel object number. -/
def fresh (st : State) : Nat × State :=
  (st.nextId, { st with nextId := st.nextId + 1 })

/-- The trace with an event appended. -/
def record (st : State) (ev : Event) : State :=
  { st with trace := st.trace ++ [ev] }

def push (st : State) (h : HeldRes) : State := { st with held := h :: st.held }

end State

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

end Koit.Machine
