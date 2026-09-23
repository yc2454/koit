import Koit.LIR.Wf
import Koit.Core.State

/-!
The state of an LIR run: the shared state of `Koit.Machine`, the
same field Core's state holds, beside LIR's private half, a frame of
locals bound to values, the stack objects `frame` allocates, and the
context by field name. LIR's values are Core's, restricted to
fixed-width integers and locations; its regions and locations are
Core's, since its stack objects are Core's struct literals with the
key frames the lowering adds. The pass-B relation maps Core's frame
to this one and leaves the shared field equal.
-/

namespace Koit.LIR.Sem

open Koit.Core.Sem (Val Loc Region Abort)
open Koit.Check (Env)
open Koit.Interface (KindDecl)
open Koit.Machine (slice blit)

structure State where
  env       : Env
  kind      : KindDecl
  /-- The shared state: what every level of the lowering acts on. -/
  machine   : Machine.State := {}
  ctx       : List (String × Val) := []
  /-- The stack objects, by number. -/
  stackBufs : List (Nat × ByteArray) := []
  nextStack : Nat := 0
  /-- The frame: each local bound to a value, innermost first. -/
  locals    : List (String × Val) := []
  fuel      : Nat := 100000
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

/-- A load or store of `n` bytes at `l` is admitted: the location's
token is current for the packet, and the bytes lie in the region. -/
def admits (st : State) (l : Loc) (n : Nat) : Bool :=
  match l.region with
  | .shared r => st.machine.admits r l.off n l.tok
  | .stack _ => l.off + n ≤ (st.region l.region).size

def local? (st : State) (x : String) : Option Val :=
  (st.locals.find? (·.1 == x)).map (·.2)

def bind (st : State) (x : String) (v : Val) : State :=
  { st with locals := (x, v) :: st.locals }

def rebind (st : State) (x : String) (v : Val) : State :=
  { st with locals := st.locals.map fun (y, v') =>
      if y == x then (y, v) else (y, v') }

def freshStack (st : State) : Nat × State :=
  (st.nextStack, { st with nextStack := st.nextStack + 1 })

def maps (st : State) := st.machine.maps
def packet (st : State) := st.machine.packet
def layout (st : State) := st.machine.layout
def held (st : State) := st.machine.held
def trace (st : State) := st.machine.trace
def log (st : State) : List String := st.machine.log

end State

/-- The initial state of a program: the packet, the context fields at
their given values or zero, and the maps as they are. -/
def initState (env : Env) (decl : KindDecl) (packet : ByteArray)
    (ctx : List (String × Nat)) (maps : List (String × Machine.MapState)) (fuel : Nat) :
    State :=
  { env, kind := decl, fuel,
    machine := { maps, packet },
    ctx := decl.ctx.map fun f =>
      (f.name, Val.mkInt false 32 ((ctx.lookup f.name).getD 0)) }

/-- The LIR state a Core state lowers to: the same shared state,
context, and fuel, and an empty frame. -/
def ofCore (st : Core.Sem.State) : State :=
  { env := st.env, kind := st.kind, machine := st.machine, ctx := st.ctx, fuel := st.fuel }

/-- The evaluation monad: exceptions over state, as Core's. -/
abbrev M := ExceptT Abort (StateM State)

def M.exec (f : M α) (st : State) : Except Abort (α × State) :=
  match (ExceptT.run f).run st with
  | (.ok v, st') => .ok (v, st')
  | (.error e, _) => .error e

def fail (msg : String) : M α := throw (.err msg)

/-- An operation of the shared machine, applied to the shared half of
the state. -/
def op (f : Machine.Op α) : M α := do
  let st ← get
  match f.exec st.machine with
  | .ok (a, m) => set { st with machine := m }; return a
  | .error msg => fail msg

def useFuel : M Unit := do
  let st ← get
  if st.fuel == 0 then fail "out of fuel"
  set { st with fuel := st.fuel - 1 }

end Koit.LIR.Sem
