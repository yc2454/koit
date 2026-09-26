import Koit.Machine.State

/-!
The operation monad on the shared state and the map operations on
it, one implementation that every level's semantics calls, with the
kernel's answers: a lookup by index or key, an update, a delete. They
are split from `Ops.lean` so that the kernel parameter's synthetic
instance can use them for the socket maps, whose entries the kernel
alone writes.
-/

namespace Koit.Machine

/-- An operation on the shared state: a result and the new state, or
an error. -/
abbrev Op := ExceptT String (StateM State)

def Op.exec (f : Op α) (st : State) : Except String (α × State) :=
  match (ExceptT.run f).run st with
  | (.ok v, st') => .ok (v, st')
  | (.error e, _) => .error e

def fail (msg : String) : Op α := throw msg

def mapState (m : String) : Op MapState := do
  match (← get).map? m with
  | some ms => pure ms
  | none => fail s!"unknown map `{m}`"

/-! ### Maps and rings -/

/-- `lookup`: the slot of an array kind below its capacity, or the
entry of a hash kind with the key's bytes; none for the kernel's
null. The key of an array kind is its 4-byte index. -/
def lookup (m : String) (key : List UInt8) : Op (Option Region) := do
  let ms ← mapState m
  match ms.decl.kind with
  | .hash .. =>
    return (ms.entries.find? (·.2.1 == key)).map fun (i, _, _) => .map m i
  | .ringbuf _ => fail "a ring buffer has no slots"
  | _ =>
    let idx := ofLe key
    return if idx < ms.capacity then some (.map m idx) else none

/-- `update`: insert or replace; a full hash map answers with the
kernel's `E2BIG`. -/
def update (m : String) (key value : List UInt8) : Op Int := do
  let ms ← mapState m
  match ms.entries.find? (·.2.1 == key) with
  | some (i, _, _) =>
    modify (·.setRegion (.map m i) (ByteArray.mk value.toArray))
    return 0
  | none =>
    if ms.entries.length ≥ ms.capacity then return -7
    modify (·.setMap m { ms with
      entries := ms.entries ++ [(ms.nextEntry, key, ByteArray.mk value.toArray)],
      nextEntry := ms.nextEntry + 1 })
    return 0

/-- `delete`: remove the entry, or the kernel's `ENOENT`. -/
def delete (m : String) (key : List UInt8) : Op Int := do
  let ms ← mapState m
  if ms.entries.any (·.2.1 == key) then
    modify (·.setMap m { ms with entries := ms.entries.filter (·.2.1 != key) })
    return 0
  else return -2

end Koit.Machine
