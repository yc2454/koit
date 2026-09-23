import Koit.Machine.Kernel

/-!
The operations on the shared state, one implementation that every
level's semantics calls: the map builtins with the kernel's answers,
the protocol of the held stack, the kernel call with its argument
check, its trace event, and the acquisition or release it performs,
and how each resource declaration releases. A level converts its own
locations to the shared regions and the kernel's values before it
calls in, and converts the answers back, so nothing here sees a
level's location.

The held stack is protocol state: `lock`, `enter`, `reserve`, and an
acquiring declaration push; `unlock`, `leave`, `submit`, `discard`, and a
releasing declaration pop and check. A release that does not match the
innermost entry, a lock taken while one is held, and a call a held
declaration forbids are errors, the machine's refusals, which the theorems
of the lowering make unreachable.
-/

namespace Koit.Machine

open Koit.Core (Resource Effect)
open Koit.Interface (KindDecl CallDecl ResourceDecl AcqArg)

/-- An operation on the shared state: a result and the new state, or
an error. -/
abbrev Op := ExceptT String (StateM State)

def Op.exec (f : Op α) (st : State) : Except String (α × State) :=
  match (ExceptT.run f).run st with
  | (.ok v, st') => .ok (v, st')
  | (.error e, _) => .error e

def fail (msg : String) : Op α := throw msg

/-- The declaration of a resource in the interface. -/
def resourceDecl (pre : Interface) (r : Resource) : Op ResourceDecl :=
  match pre.resource? r with
  | some decl => pure decl
  | none => fail s!"no declaration for `{r}`"

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
    unless h.decl.res == res && h.obj == obj do
      fail s!"a release of {h.decl.describe} that is not the innermost held"
    set { st with held := rest }
    return h
  | [] => fail "a release with nothing held"

/-- An entry pushed, subject to the declaration's nesting rule. -/
def push (decl : ResourceDecl) (obj : Option HeldObj) (ring : Option String := none) :
    Op Unit := do
  let st ← get
  if decl.nesting == .no && st.held.any (·.decl.res == decl.res) then
    fail s!"{decl.describe} acquired while one is held"
  set (st.push { decl, ring, obj })

/-- `reserve`: a fresh record of `n` bytes while the ring has room,
held until it is submitted or discarded; none when the ring is
full. -/
def reserve (decl : ResourceDecl) (m : String) (n : Nat) : Op (Option Nat) := do
  let ms ← mapState m
  if (ms.ring.foldl (fun a b => a + b.size) 0) + n > ms.capacity then return none
  let st ← get
  let (id, st) := st.fresh
  set (st.setRegion (.kernel id) (zeros n))
  push decl (some (.object id)) (some m)
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

def lock (decl : ResourceDecl) (obj : HeldObj) : Op Unit := push decl (some obj)

def unlock (obj : HeldObj) : Op Unit := do
  let _ ← popHeld ⟨"spinlock"⟩ (some obj)

def enter (decl : ResourceDecl) : Op Unit := push decl none

def leave (res : Resource) : Op Unit := do
  let _ ← popHeld res none

def print (fmt : String) (args : List Val) : Op Unit :=
  modify (·.record (.print fmt args))

/-- The kernel's limit of tail calls in one invocation. -/
def maxTailCalls : Nat := 33

/-- `bpf_tail_call`: taken when the slot holds a program and the
limit is not reached, which the run driver honors by running that
program on this state; otherwise nothing happens. -/
def tailCall (m : String) (i : Nat) : Op Bool := do
  let st ← get
  let some ms := st.maps.lookup m | throw s!"unknown map `{m}`"
  match ms.progs.lookup i with
  | some p =>
    if st.tailCount < maxTailCalls then
      set { st with tailTo := some p, tailCount := st.tailCount + 1 }
      return true
    else return false
  | none => return false

/-! ### Kernel functions -/

/-- The resource declarations a kernel function releases: those whose exit
clause names its kernel function. -/
def releasesOf (pre : Interface) (decl : CallDecl) : List ResourceDecl :=
  pre.resources.filter fun r =>
    r.normalExit == decl.kernel || r.abnormalExit == decl.kernel

/-- The held declaration that forbids a call, unless the call is that declaration's
own release. -/
def forbidsCall (st : State) (releases : List ResourceDecl) : Option ResourceDecl :=
  (st.held.find? fun h =>
    hasFlag h.decl.forbidden .call && !releases.any (·.res == h.decl.res)).map (·.decl)

/-- A kernel function through `K`: the held declarations consulted, the
kernel's answer, the trace appended, and the held stack pushed with
the object an acquiring declaration hands out or popped for the object a
releasing declaration takes. The arguments arrive as the kernel sees them,
fitted by the caller to the declaration's parameter kinds. An inline declaration is
computed here instead, with no call and no event. -/
def call (pre : Interface) (K : Kernel) (kind : KindDecl) (decl : CallDecl) (vs : List Val) :
    Op CallOut := do
  let st ← get
  -- an inline declaration is arithmetic, not a call: no held declaration forbids it
  -- and the trace does not list it
  if decl.isInline then
    match inlineDecl decl.name vs st with
    | some v => return .ok (some v)
    | none => fail s!"`{decl.name}` has no inline computation"
  let releases := releasesOf pre decl
  if let some h := forbidsCall st releases then
    fail s!"a call while {h.describe} is held"
  match K.helper kind decl vs st with
  | .ok v st' =>
    set (st'.record (.call decl.name vs (.ok v)))
    if let some r := decl.acquires then
      if let some (.object id) := v then
        push (← resourceDecl pre r) (some (.object id))
    if let some rrow := releases.head? then
      let obj := vs.findSome? fun
        | .object id => some (HeldObj.object id)
        | _ => none
      let _ ← popHeld rrow.res obj
    return .ok v
  | .failed n st' =>
    set (st'.record (.call decl.name vs (.failed n)))
    return .failed n
  | .err m => fail m

/-! ### Releases -/

/-- How a resource declaration releases: a builtin of the protocol, or the
kernel function its exit clause names. -/
inductive Release where
  | leave
  | unlock
  | submit
  | discard
  | kernel (decl : CallDecl)
  deriving Inhabited

/-- The release of a declaration, normally or abnormally. -/
def releaseOf (pre : Interface) (decl : ResourceDecl) (normal : Bool) : Except String Release :=
  if decl.arg == .scope then .ok .leave
  else if decl.res == ⟨"spinlock"⟩ then .ok .unlock
  else if decl.res == ⟨"ringbuf"⟩ then .ok (if normal then .submit else .discard)
  else
    let exit := if normal then decl.normalExit else decl.abnormalExit
    match pre.calls.find? (·.kernel == exit) with
    | some crow => .ok (.kernel crow)
    | none => .error s!"no kernel function `{exit}` releases {decl.describe}"

/-- The innermost held entry released, normally or abnormally, as its
declaration says. -/
def release (pre : Interface) (K : Kernel) (kind : KindDecl) (normal : Bool) : Op Unit := do
  let st ← get
  let h :: _ := st.held | fail "a release with nothing held"
  match releaseOf pre h.decl normal with
  | .error m => fail m
  | .ok .leave => leave h.decl.res
  | .ok r =>
    let some obj := h.obj | fail s!"{h.decl.describe} held without its object"
    match r with
    | .unlock => unlock obj
    | .submit => submit obj
    | .discard => discard obj
    | .kernel crow =>
      match obj with
      | .object id =>
        match ← call pre K kind crow [.object id] with
        | .ok _ => pure ()
        | .failed n => fail s!"`{crow.name}` failed with {n} releasing {h.decl.describe}"
      | .slot .. => fail s!"`{crow.name}` releases an object, not a field"
    | .leave => pure ()

end Koit.Machine
