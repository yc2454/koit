import Koit.BPF.Syntax
import Koit.Machine.Ops

/-!
The state of the target machine, for BIR and bytecode alike: the
program counter, a register file over the level's register type, the
frame of 64 slots with the verifier's spill rules, the context's
fields, and the shared state of `Koit.Machine`, the same field
Core's and LIR's states hold. Values are scalars, locations, or map
handles, never integers standing for addresses: a location's region
is one of the machine's, the frame, or the context, and its offset
may leave the region between the arithmetic that moves it and the
access that uses it, since only the access is checked.

The causes a step can refuse for are the verifier's checks, one
constructor per item of `bir.md` 5.3, each carrying what identifies
the instance, so that the runner prints why a program would not
load and a rejection from the kernel can be matched against the list.
-/

namespace Koit.BPF

open Koit.Machine (toNatMod wrap leBytes ofLe HeldObj)
open Koit.Interface (KindDecl)

/-! ### Regions and values -/

/-- A region: one of the shared memory's, the frame, or the context. -/
inductive Region where
  | shared (r : Machine.Region)
  | frame
  | ctx
  deriving BEq, DecidableEq, Repr, Inhabited

def Region.pkt : Region := .shared .pkt
def Region.map (m : String) (i : Nat) : Region := .shared (.map m i)
def Region.kernel (id : Nat) : Region := .shared (.kernel id)

def Region.print : Region → String
  | .shared (.map m i) => s!"map {m}[{i}]"
  | .shared .pkt => "pkt"
  | .shared (.kernel id) => s!"object {id}"
  | .frame => "frame"
  | .ctx => "ctx"

/-- A value in a register or a frame slot: a 64-bit pattern, a
location with the token it was made under, or a map's handle. Null
is the scalar zero. -/
inductive Val where
  | scalar (n : Nat)
  | loc (r : Region) (off : Int) (tok : Nat)
  | handle (m : String)
  deriving BEq, DecidableEq, Repr, Inhabited

def Val.print : Val → String
  | .scalar n => toString n
  | .loc r off _ => s!"{r.print} + {off}"
  | .handle m => s!"map {m}"

/-- The object a location names on the held stack. -/
def Val.heldObj : Val → Option HeldObj
  | .loc (.shared (.map m i)) off _ => if off ≥ 0 then some (.slot m i off.toNat) else none
  | .loc (.shared (.kernel id)) _ _ => some (.object id)
  | _ => none

/-! ### The causes of a refusal -/

/-- Why a step is refused: the verifier's checks, one constructor per
item of the list in `bir.md` 5.3, plus `halted` for a step on a
halted state and `malformed` for what well-formedness excludes and no
verifier check names. -/
inductive Cause where
  /-- 1: an access outside its region, or of a width that crosses
  its end, or through a value that is not a location. -/
  | outOfRegion (r : Region) (off : Int) (n : Nat)
  | noRegion (v : Val)
  /-- 2: an access through a packet location whose token is stale. -/
  | staleToken (off : Int)
  /-- 3: a read of an uninitialized register or frame byte, or a byte
  read of a spilled slot. -/
  | uninitRegister (r : String)
  | uninitFrame (off : Int)
  | byteReadOfSpill (off : Int)
  /-- 4: a store of a location anywhere but an aligned frame slot. -/
  | pointerLeak (r : Region) (off : Int)
  /-- 5: an ALU operation on a location other than the two allowed. -/
  | aluOnLocation (what : String)
  /-- 6: a comparison the machine does not define. -/
  | badComparison (what : String)
  /-- 7: a context access that is not a declared field, or a write to a
  read-only field. -/
  | ctxAccess (off : Int) (n : Nat) (write : Bool)
  /-- 8: an argument that does not fit its parameter kind, or a call
  while a held resource forbids it. -/
  | badArgument (callee : String) (what : String)
  | forbiddenCall (callee : String) (held : String)
  /-- 9: a release that is not the innermost held object, or a lock
  taken while one is held. -/
  | badRelease (what : String)
  | lockHeld (what : String)
  /-- 10: an exit while something is held, or with the result not a
  scalar. -/
  | exitHeld
  | exitNotScalar
  /-- 11: a `pc` outside the code, or a jump to one. -/
  | pcOutOfCode (pc : Nat)
  /-- 12: a store into a map the program may only read, a load from
  one it may only write, or a builtin that writes such a map. -/
  | readOnlyRegion (r : Region) (off : Int) (n : Nat)
  | writeOnlyRegion (r : Region) (off : Int) (n : Nat)
  | readOnlyMap (m : String) (op : String)
  /-- 13: a store through the packet in a kind whose packet is
  read-only. -/
  | readOnlyPacket (off : Int) (n : Nat)
  /-- 14: an access through a location into a frame that has been
  popped. -/
  | staleFrame (off : Int) (n : Nat)
  /-- 15: a load or store whose bytes overlap a slot field of a map
  value, which the kernel reaches only through the slot's operations. -/
  | slotAccess (r : Region) (off : Int) (n : Nat) (write : Bool)
  /-- A step on a halted state. -/
  | halted
  /-- What well-formedness excludes: an unknown map, declaration, label, or
  object, a wrong arity, and the kernel's own error, which its
  contract excludes. -/
  | malformed (what : String)
  deriving Repr, Inhabited

def Cause.describe : Cause → String
  | .outOfRegion r off n => s!"an access of {n} bytes at {r.print} + {off} is outside the region"
  | .noRegion v => s!"a memory access through {v.print}, which is not a location"
  | .staleToken off => s!"an access at pkt + {off} through a location made before a resize"
  | .uninitRegister r => s!"a read of {r}, which is uninitialized"
  | .uninitFrame off => s!"a read of the frame at {off}, which is uninitialized"
  | .byteReadOfSpill off => s!"a byte read of the frame at {off}, which holds a spilled value"
  | .pointerLeak r off => s!"a store of a location into {r.print} + {off}"
  | .aluOnLocation what => s!"arithmetic on a location: {what}"
  | .badComparison what => s!"a comparison the machine does not define: {what}"
  | .ctxAccess off n true => s!"a store of {n} bytes to the context at {off}, which is not a writable field of the context"
  | .ctxAccess off n false => s!"a load of {n} bytes from the context at {off}, which is not a field of the context"
  | .badArgument callee what => s!"`{callee}`: {what}"
  | .forbiddenCall callee held => s!"a call to `{callee}` while {held} is held"
  | .badRelease what => s!"a release out of order: {what}"
  | .lockHeld what => s!"{what} acquired while one is held"
  | .exitHeld => "an exit while a resource is held"
  | .exitNotScalar => "an exit with a result that is not a scalar"
  | .pcOutOfCode pc => s!"the program counter {pc} is outside the code"
  | .readOnlyRegion r off n => s!"a store of {n} bytes into {r.print} + {off}, which the program may only read"
  | .writeOnlyRegion r off n => s!"a load of {n} bytes from {r.print} + {off}, which the program may only write"
  | .readOnlyMap m op => s!"`{op}` on map {m}, which the program may only read"
  | .readOnlyPacket off n => s!"a store of {n} bytes at pkt + {off}, and this kind may only read the packet"
  | .staleFrame off n => s!"an access of {n} bytes at frame + {off} of a frame that has returned"
  | .slotAccess r off n true => s!"a store of {n} bytes into {r.print} + {off} overlaps a slot field"
  | .slotAccess r off n false => s!"a load of {n} bytes from {r.print} + {off} overlaps a slot field"
  | .halted => "the program has halted"
  | .malformed what => s!"a malformed program: {what}"

/-! ### The frame -/

/-- A slot of the frame: one spilled value, or eight bytes, each
initialized or not. -/
inductive Slot where
  | spilled (v : Val)
  | bytes (bs : Array (Option UInt8))
  deriving Repr, Inhabited

/-- The frame: 64 slots of 8 bytes at offsets `-512` to `-1` from its
top. -/
structure Frame where
  slots : Array Slot
  deriving Inhabited

namespace Frame

def size : Nat := 512

def emptySlot : Slot := .bytes (Array.replicate 8 none)

/-- The frame at entry: every byte uninitialized. -/
def init : Frame := ⟨Array.replicate 64 emptySlot⟩

/-- The byte index of an offset from the top, when it lies in the
frame. -/
def index (off : Int) : Option Nat :=
  if -512 ≤ off && off < 0 then some (off + 512).toNat else none

def slot (fr : Frame) (i : Nat) : Slot := fr.slots.getD i emptySlot

def setSlot (fr : Frame) (i : Nat) (s : Slot) : Frame := ⟨fr.slots.set! i s⟩

/-- A load of `n` bytes at `off`: 8 bytes at a spilled slot yield the
value; otherwise every byte must be initialized and none may belong
to a spilled slot, and the bytes read little-endian are a scalar. -/
def load (fr : Frame) (off : Int) (n : Nat) : Except Cause Val := do
  let some i := index off | throw (.outOfRegion .frame off n)
  unless i + n ≤ size do throw (.outOfRegion .frame off n)
  if n == 8 && i % 8 == 0 then
    if let .spilled v := fr.slot (i / 8) then return v
  let mut bs : List UInt8 := []
  for k in [0:n] do
    match fr.slot ((i + k) / 8) with
    | .spilled _ => throw (.byteReadOfSpill (off + k))
    | .bytes b =>
      match b.getD ((i + k) % 8) none with
      | some x => bs := bs ++ [x]
      | none => throw (.uninitFrame (off + k))
  return .scalar (ofLe bs)

/-- The initialized bytes at `off`, for a key or a memory argument. -/
def readBytes (fr : Frame) (off : Int) (n : Nat) : Except Cause (List UInt8) := do
  let some i := index off | throw (.outOfRegion .frame off n)
  unless i + n ≤ size do throw (.outOfRegion .frame off n)
  let mut bs : List UInt8 := []
  for k in [0:n] do
    match fr.slot ((i + k) / 8) with
    | .spilled _ => throw (.byteReadOfSpill (off + k))
    | .bytes b =>
      match b.getD ((i + k) % 8) none with
      | some x => bs := bs ++ [x]
      | none => throw (.uninitFrame (off + k))
  return bs

/-- A store of `v` as `n` bytes at `off`: a location or a handle only
as 8 bytes at a slot boundary, which spills it; a scalar as bytes,
which unspills the slot it touches, its other bytes becoming
uninitialized. -/
def store (fr : Frame) (off : Int) (n : Nat) (v : Val) : Except Cause Frame := do
  let some i := index off | throw (.outOfRegion .frame off n)
  unless i + n ≤ size do throw (.outOfRegion .frame off n)
  match v with
  | .scalar x =>
    let mut fr := fr
    let bytes := leBytes (toNatMod x (8 * n)) n
    for k in [0:n] do
      let s := (i + k) / 8
      let b := match fr.slot s with
        | .bytes b => b
        | .spilled _ => Array.replicate 8 none
      fr := fr.setSlot s (.bytes (b.set! ((i + k) % 8) (bytes.getD k 0)))
    return fr
  | _ =>
    unless n == 8 && i % 8 == 0 do throw (.pointerLeak .frame off)
    return fr.setSlot (i / 8) (.spilled v)

end Frame

/-! ### The state -/

/-- What a subprogram call saves: where to return, the caller's
registers and frame with its identity, and the register its result
goes to. -/
structure Saved (ρ : Type) where
  retPc : Nat
  regs  : ρ → Option Val
  frame : Frame
  /-- The identity of the saved frame, which its locations carry. -/
  id    : Nat
  dst   : Option ρ

/-- The state of a run: the program counter, the registers, each
holding a value or uninitialized, the frame, the context's fields by
name, the shared state, and the subprogram calls in progress. -/
structure State (ρ : Type) where
  pc      : Nat := 0
  regs    : ρ → Option Val
  frame   : Frame := Frame.init
  /-- The identity of the running frame, and the next one to hand
  out: a frame location carries the identity of the frame it was
  made in, as a packet location carries the layout token, so that an
  access through one whose frame has returned is refused. -/
  frameId   : Nat := 0
  nextFrame : Nat := 1
  ctx     : List (String × Nat) := []
  machine : Machine.State := {}
  /-- The subprogram calls in progress, innermost first. -/
  frames  : List (Saved ρ) := []
  /-- The arguments of the subprogram running, for BIR's `arg`. -/
  args    : List Val := []

instance : Inhabited (State ρ) := ⟨{ regs := fun _ => none }⟩

namespace State

variable [DecidableEq ρ]

def set (m : State ρ) (r : ρ) (v : Val) : State ρ :=
  { m with regs := fun r' => if r' = r then some v else m.regs r' }

def clear (m : State ρ) (rs : List ρ) : State ρ :=
  { m with regs := fun r' => if rs.contains r' then none else m.regs r' }

def held (m : State ρ) := m.machine.held

/-- The live frame with identity `id`: the running one, or one saved
by a call in progress, which a callee reaches through a location its
caller passed; none when that frame has returned. -/
def frameAt (m : State ρ) (id : Nat) : Option Frame :=
  if id == m.frameId then some m.frame
  else (m.frames.find? (·.id == id)).map (·.frame)

/-- The live frame `id` replaced. -/
def setFrameAt (m : State ρ) (id : Nat) (fr : Frame) : State ρ :=
  if id == m.frameId then { m with frame := fr }
  else { m with frames := m.frames.map fun s => if s.id == id then { s with frame := fr } else s }

end State

/-! ### The convention and the environment -/

/-- What distinguishes the two register files: the designated
registers, how a call takes its operands, whether `lea` is admitted,
and how a jump target selects the next instruction. -/
structure Conv (ρ τ : Type) where
  /-- The result register: `r0`, or `v_ret`. -/
  ret : ρ
  /-- The register holding the context at entry: `r1`, or `v_ctx`. -/
  ctx : ρ
  /-- The frame pointer: `r10`, or `v_fp`. -/
  fp : ρ
  /-- The registers no instruction may write: the frame pointer, and
  in BIR the context register, which bytecode's `r1` is only at
  entry. -/
  pinned : List ρ
  /-- For the fixed convention, the registers a call reads its
  arguments from, in order, and the ones it leaves uninitialized;
  none when the operands are on the instruction and nothing is
  clobbered. -/
  fixedCall : Option (List ρ × List ρ)
  lea : Bool
  /-- The next instruction a jump target selects, given the program's
  label table and the current `pc`. -/
  resolve : List (Nat × Nat) → Nat → τ → Option Nat
  /-- A register's name, for the causes. -/
  name : ρ → String

/-- BIR's convention: explicit call operands, `lea`, labels. -/
def birConv : Conv VReg Label :=
  { ret := .ret, ctx := .ctx, fp := .fp, pinned := [.ctx, .fp], fixedCall := none, lea := true,
    resolve := fun labels _ l => labels.lookup l.id,
    name := VReg.print }

/-- Bytecode's convention: arguments in `r1` to `r5`, dead after the
call, the result in `r0`, `r10` the frame pointer, no `lea`, and
jump targets as offsets from the next instruction. -/
def bytecodeConv : Conv Reg Int :=
  { ret := .r0, ctx := .r1, fp := .r10, pinned := [.r10],
    fixedCall := some ([.r1, .r2, .r3, .r4, .r5], [.r1, .r2, .r3, .r4, .r5]),
    lea := false,
    resolve := fun _ pc off => if (pc : Int) + 1 + off ≥ 0 then some ((pc : Int) + 1 + off).toNat else none,
    name := Reg.print }

/-- What a step reads besides the state: the interface, the kind's
declaration, the convention, the program, and the sizes of the types the
kernel functions' memory parameters name, which the caller supplies
from the checker's layout so that the machine reads no type. -/
structure Env (ρ τ : Type) where
  pre    : Interface
  kind   : KindDecl
  conv   : Conv ρ τ
  prog   : Program ρ τ
  sizeOf : Core.Ty → Option Nat

/-- The loaded state of a program from a shared state: the context in
its register, the frame pointer in its, every other register and the
whole frame uninitialized. -/
def load [DecidableEq ρ] (X : Env ρ τ) (st : Machine.State) (ctx : List (String × Nat)) :
    State ρ :=
  { pc := 0,
    regs := fun r =>
      if r = X.conv.ctx then some (.loc .ctx 0 st.layout)
      else if r = X.conv.fp then some (.loc .frame 0 0)
      else none,
    frame := Frame.init,
    ctx := X.kind.ctx.map fun f => (f.name, (ctx.lookup f.name).getD 0),
    machine := st }

end Koit.BPF
