import Koit.Machine.Kernel

/-!
The operations on the shared state, one implementation that every
level's semantics calls: the map builtins with the kernel's answers,
the protocol of the held stack, the kernel call with its argument
check, its trace event, and the acquisition or release it performs,
and how each resource row releases. A level converts its own
locations to the shared regions and the kernel's values before it
calls in, and converts the answers back, so nothing here sees a
level's location.

The held stack is protocol state: `lock`, `enter`, `reserve`, and an
acquiring row push; `unlock`, `leave`, `submit`, `discard`, and a
releasing row pop and check. A release that does not match the
innermost entry, a lock taken while one is held, and a call a held
row forbids are errors, the machine's refusals, which the theorems
of the lowering make unreachable.
-/

namespace Koit.Machine

open Koit.Core (Resource Effect)
open Koit.Interface (KindRow CallRow ResourceRow AcqArg)

/-- An operation on the shared state: a result and the new state, or
an error. -/
abbrev Op := ExceptT String (StateM State)

def Op.exec (f : Op α) (st : State) : Except String (α × State) :=
  match (ExceptT.run f).run st with
  | (.ok v, st') => .ok (v, st')
  | (.error e, _) => .error e

def fail (msg : String) : Op α := throw msg

/-- The row of a resource in the interface. -/
def resourceRow (pre : Interface) (r : Resource) : Op ResourceRow :=
  match pre.resource? r with
  | some row => pure row
  | none => fail s!"no row for `{r}`"

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

/-! ### The held stack -/

/-- The innermost held entry popped, when it is the resource's and
the object's. -/
def popHeld (res : Resource) (obj : Option HeldObj) : Op HeldRes := do
  let st ← get
  match st.held with
  | h :: rest =>
    unless h.row.res == res && h.obj == obj do
      fail s!"a release of {h.row.describe} that is not the innermost held"
    set { st with held := rest }
    return h
  | [] => fail "a release with nothing held"

/-- An entry pushed, subject to the row's nesting rule. -/
def push (row : ResourceRow) (obj : Option HeldObj) (ring : Option String := none) :
    Op Unit := do
  let st ← get
  if row.nesting == .no && st.held.any (·.row.res == row.res) then
    fail s!"{row.describe} acquired while one is held"
  set (st.push { row, ring, obj })

/-- `reserve`: a fresh record of `n` bytes while the ring has room,
held until it is submitted or discarded; none when the ring is
full. -/
def reserve (row : ResourceRow) (m : String) (n : Nat) : Op (Option Nat) := do
  let ms ← mapState m
  if (ms.ring.foldl (fun a b => a + b.size) 0) + n > ms.capacity then return none
  let st ← get
  let (id, st) := st.fresh
  set (st.setRegion (.kernel id) (zeros n))
  push row (some (.object id)) (some m)
  return some id

/-- `submit`: the record popped and appended to its ring. -/
def submit (obj : HeldObj) : Op Unit := do
  let h ← popHeld ⟨"ringbuf"⟩ (some obj)
  let st ← get
  match h.ring, obj with
  | some m, .object id =>
    let ms ← mapState m
    set (st.setMap m { ms with ring := ms.ring ++ [st.region (.kernel id)] })
  | _, _ => fail "a record without a ring"

/-- `discard`: the record popped. -/
def discard (obj : HeldObj) : Op Unit := do
  let _ ← popHeld ⟨"ringbuf"⟩ (some obj)

def lock (row : ResourceRow) (obj : HeldObj) : Op Unit := push row (some obj)

def unlock (obj : HeldObj) : Op Unit := do
  let _ ← popHeld ⟨"spinlock"⟩ (some obj)

def enter (row : ResourceRow) : Op Unit := push row none

def leave (res : Resource) : Op Unit := do
  let _ ← popHeld res none

def print (fmt : String) (args : List Val) : Op Unit :=
  modify (·.record (.print fmt args))

/-! ### Kernel functions -/

/-- The resource rows a kernel function releases: those whose exit
column names its kernel function. -/
def releasesOf (pre : Interface) (row : CallRow) : List ResourceRow :=
  pre.resources.filter fun r =>
    r.normalExit == row.kernel || r.abnormalExit == row.kernel

/-- The held row that forbids a call, unless the call is that row's
own release. -/
def forbidsCall (st : State) (releases : List ResourceRow) : Option ResourceRow :=
  (st.held.find? fun h =>
    hasFlag h.row.forbidden .call && !releases.any (·.res == h.row.res)).map (·.row)

/-- A kernel function through `K`: the held rows consulted, the
kernel's answer, the trace appended, and the held stack pushed with
the object an acquiring row hands out or popped for the object a
releasing row takes. The arguments arrive as the kernel sees them,
fitted by the caller to the row's parameter kinds. An inline row is
computed here instead, with no call and no event. -/
def call (pre : Interface) (K : Kernel) (kind : KindRow) (row : CallRow) (vs : List Val) :
    Op CallOut := do
  let st ← get
  -- an inline row is arithmetic, not a call: no held row forbids it
  -- and the trace does not list it
  if row.isInline then
    match inlineRow row.name vs st with
    | some v => return .ok (some v)
    | none => fail s!"`{row.name}` has no inline computation"
  let releases := releasesOf pre row
  if let some h := forbidsCall st releases then
    fail s!"a call while {h.describe} is held"
  match K.helper kind row vs st with
  | .ok v st' =>
    set (st'.record (.call row.name vs (.ok v)))
    if let some r := row.acquires then
      if let some (.object id) := v then
        push (← resourceRow pre r) (some (.object id))
    if let some rrow := releases.head? then
      let obj := vs.findSome? fun
        | .object id => some (HeldObj.object id)
        | _ => none
      let _ ← popHeld rrow.res obj
    return .ok v
  | .failed n st' =>
    set (st'.record (.call row.name vs (.failed n)))
    return .failed n
  | .err m => fail m

/-! ### Releases -/

/-- How a resource row releases: a builtin of the protocol, or the
kernel function its exit column names. -/
inductive Release where
  | leave
  | unlock
  | submit
  | discard
  | kernel (row : CallRow)
  deriving Inhabited

/-- The release of a row, normally or abnormally. -/
def releaseOf (pre : Interface) (row : ResourceRow) (normal : Bool) : Except String Release :=
  if row.arg == .scope then .ok .leave
  else if row.res == ⟨"spinlock"⟩ then .ok .unlock
  else if row.res == ⟨"ringbuf"⟩ then .ok (if normal then .submit else .discard)
  else
    let exit := if normal then row.normalExit else row.abnormalExit
    match pre.calls.find? (·.kernel == exit) with
    | some crow => .ok (.kernel crow)
    | none => .error s!"no kernel function `{exit}` releases {row.describe}"

/-- The innermost held entry released, normally or abnormally, as its
row says. -/
def release (pre : Interface) (K : Kernel) (kind : KindRow) (normal : Bool) : Op Unit := do
  let st ← get
  let h :: _ := st.held | fail "a release with nothing held"
  match releaseOf pre h.row normal with
  | .error m => fail m
  | .ok .leave => leave h.row.res
  | .ok r =>
    let some obj := h.obj | fail s!"{h.row.describe} held without its object"
    match r with
    | .unlock => unlock obj
    | .submit => submit obj
    | .discard => discard obj
    | .kernel crow =>
      match obj with
      | .object id =>
        match ← call pre K kind crow [.object id] with
        | .ok _ => pure ()
        | .failed n => fail s!"`{crow.name}` failed with {n} releasing {h.row.describe}"
      | .slot .. => fail s!"`{crow.name}` releases an object, not a field"
    | .leave => pure ()

end Koit.Machine
