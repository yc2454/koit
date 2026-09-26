import Koit.BPF.Interp
import Koit.BPF.Wf
import Koit.Core.Interp
import Koit.Interface.Interface

/-!
Checks on the target machine over hand-written programs: the ALU's
normal form, the frame's spill rules, the context rows, the map
builtins through a key frame, the held stack at exit, and the same
program under both conventions, BIR's explicit operands and
bytecode's `r1` to `r5`.
-/

open Koit Koit.BPF Koit.Machine

namespace KoitTests.BPF

private instance : BEq (Except String Nat) where
  beq a b := match a, b with
    | .ok x, .ok y => x == y
    | .error x, .error y => x == y
    | _, _ => false

private def xdp : Interface.KindDecl := (Interface.v6_8.kind? "xdp").get!

/-- The same kind with a packet the program may only read. -/
private def roPkt : Interface.KindDecl := { xdp with pktWritable := false }

/-- A one-slot array map of a 16-byte value, as the runs need one. -/
private def counters : Machine.MapState :=
  let decl : Core.MapDecl :=
    { span := Interface.noSpan, name := "counters",
      kind := .array (.lit Interface.noSpan 1 "1") (.int Interface.noSpan false 64) }
  { decl, valueTy := .int Interface.noSpan false 64, valueSize := 16, capacity := 1 }

/-- A hash map from a 4-byte key to an 8-byte value. -/
private def table : Machine.MapState :=
  let decl : Core.MapDecl :=
    { span := Interface.noSpan, name := "table",
      kind := .hash (.lit Interface.noSpan 4 "4") (.int Interface.noSpan false 32)
        (.int Interface.noSpan false 64) }
  { decl, valueTy := .int Interface.noSpan false 64, valueSize := 8,
    keyTy := some (.int Interface.noSpan false 32), keySize := 4, capacity := 4 }

/-- One-slot arrays of an 8-byte value the program may only read, and
only write. -/
private def rodata : Machine.MapState :=
  let decl : Core.MapDecl :=
    { span := Interface.noSpan, name := "rodata", access := .ro,
      kind := .array (.lit Interface.noSpan 1 "1") (.int Interface.noSpan false 64) }
  { decl, valueTy := .int Interface.noSpan false 64, valueSize := 8, capacity := 1 }

private def wonly : Machine.MapState :=
  let decl : Core.MapDecl :=
    { span := Interface.noSpan, name := "wonly", access := .wo,
      kind := .array (.lit Interface.noSpan 1 "1") (.int Interface.noSpan false 64) }
  { decl, valueTy := .int Interface.noSpan false 64, valueSize := 8, capacity := 1 }

/-- A one-slot array whose 16-byte value holds a 4-byte spin lock at
offset 0 and a counter at 8. -/
private def locked : Machine.MapState :=
  let decl : Core.MapDecl :=
    { span := Interface.noSpan, name := "locked",
      kind := .array (.lit Interface.noSpan 1 "1") (.int Interface.noSpan false 64) }
  { decl, valueTy := .int Interface.noSpan false 64, valueSize := 16, capacity := 1,
    slotFields := [(0, 4)] }

private def shared (packet : List UInt8 := []) : Machine.State :=
  { maps := [("counters", counters), ("table", table), ("rodata", rodata),
             ("wonly", wonly), ("locked", locked)],
    packet := ByteArray.mk packet.toArray }

private def sizeOf : Core.Ty → Option Nat
  | .int _ _ w => some (w / 8)
  | _ => none

private def birEnv (code : List (Instr VReg Label)) (labels : List (Nat × Nat) := [])
    (objects : List FrameObj := []) (kind : Interface.KindDecl := xdp) : Env VReg Label :=
  { pre := Interface.v6_8, kind, conv := birConv, sizeOf,
    prog := { name := "t", kind := "xdp", code := code.toArray, labels, objects } }

private def bcEnv (code : List (Instr Reg Int)) : Env Reg Int :=
  { pre := Interface.v6_8, kind := xdp, conv := bytecodeConv, sizeOf,
    prog := { name := "t", kind := "xdp", code := code.toArray } }

/-- The verdict of a BIR program, or the refusal. -/
private def runB (X : Env VReg Label) (st : Machine.State := shared)
    (ctx : List (String × Nat) := []) : Except String (Nat × Machine.State) :=
  match run X Machine.synthetic (load X st ctx) 10000 with
  | .ok h => .ok (h.verdict, h.state.machine)
  | .error r => .error r.describe

private def verdictB (X : Env VReg Label) (st : Machine.State := shared) : Except String Nat :=
  (runB X st).map (·.1)

private def runC (X : Env Reg Int) (st : Machine.State := shared) : Except String Nat :=
  match run X Machine.synthetic (load X st []) 10000 with
  | .ok h => .ok h.verdict
  | .error r => .error r.describe

private def v (n : Nat) : VReg := .v n

/-! ### The ALU and the normal form -/

-- 32-bit results are zero-extended into the register
#guard verdictB (birEnv
  [.lddw (v 0) 0xFFFFFFFF, .alu .add .w32 (v 0) (.imm 1),
   .mov .w64 .ret (.reg (v 0)), .exit]) == .ok 0
-- the verdict is fitted to the kind's 32-bit width
#guard verdictB (birEnv [.lddw .ret 0x100000002, .exit]) == .ok 2
-- division by zero yields zero, modulo by zero the dividend
#guard verdictB (birEnv
  [.lddw (v 0) 7, .mov .w64 (v 1) (.imm 0), .alu .div .w64 (v 0) (.reg (v 1)),
   .mov .w64 .ret (.reg (v 0)), .exit]) == .ok 0
#guard verdictB (birEnv
  [.lddw (v 0) 7, .alu .mod .w64 (v 0) (.imm 0), .mov .w64 .ret (.reg (v 0)), .exit]) == .ok 7
-- an arithmetic shift of a negative 32-bit pattern
#guard verdictB (birEnv
  [.lddw (v 0) 0xFFFFFFF0, .alu .arsh .w32 (v 0) (.imm 4),
   .mov .w64 .ret (.reg (v 0)), .exit]) == .ok 0xFFFFFFFF
-- movsx from 8 bits, then a 32-bit unsigned compare
#guard verdictB (birEnv
  [.lddw (v 0) 0x80, .movsx .w32 8 (v 1) (v 0),
   .jcond .lt .w32 (v 1) (.imm 0x100) ⟨1⟩,
   .mov .w64 .ret (.imm 1), .exit,
   .mov .w64 .ret (.imm 2), .exit] [(1, 5)]) == .ok 1
-- `end be 16` swaps the low bytes
#guard verdictB (birEnv
  [.lddw (v 0) 0x0800, .«end» .be 16 (v 0), .mov .w64 .ret (.reg (v 0)), .exit]) == .ok 8

/-! ### Registers and the frame -/

-- a read of an uninitialized register is refused
#guard (verdictB (birEnv [.mov .w64 .ret (.reg (v 3)), .exit])).isOk == false
-- a scalar stored and loaded through the frame pointer
#guard verdictB (birEnv
  [.lddw (v 0) 42, .stx 64 .fp (-8) (.reg (v 0)),
   .ldx 64 .ret .fp (-8), .exit]) == .ok 42
-- a partial load of the frame reads the stored bytes little-endian
#guard verdictB (birEnv
  [.lddw (v 0) 0x0102030405060708, .stx 64 .fp (-8) (.reg (v 0)),
   .ldx 16 .ret .fp (-8), .exit]) == .ok 0x0708
-- a location spilled and reloaded is the location
#guard verdictB (birEnv
  [.stx 64 .fp (-16) (.reg .fp), .ldx 64 (v 1) .fp (-16),
   .lddw (v 0) 9, .stx 32 (v 1) (-4) (.reg (v 0)), .ldx 32 .ret .fp (-4), .exit]) == .ok 9
-- a byte read of a spilled slot is refused
#guard match verdictB (birEnv
  [.stx 64 .fp (-16) (.reg .fp), .ldx 32 .ret .fp (-16), .exit]) with
  | .error m => m.endsWith "holds a spilled value"
  | .ok _ => false
-- a location stored unaligned is a leak
#guard match verdictB (birEnv [.stx 64 .fp (-12) (.reg .fp), .exit]) with
  | .error m => (m.splitOn "a store of a location").length == 2
  | .ok _ => false
-- an uninitialized frame byte is refused
#guard match verdictB (birEnv [.ldx 8 .ret .fp (-1), .exit]) with
  | .error m => m.endsWith "which is uninitialized"
  | .ok _ => false
-- a frame object through `lea`
#guard verdictB (birEnv
  [.lea (v 0) "k", .stx 32 (v 0) 0 (.imm 5), .ldx 32 .ret (v 0) 0, .exit]
  [] [{ name := "k", size := 8, base := -8 }]) == .ok 5

/-! ### The context and the packet -/

-- a context field by its row's offset and width
#guard (runB (birEnv [.ldx 32 .ret .ctx 12, .exit]) shared [("ingress_ifindex", 7)]).map (·.1)
  == .ok 7
-- an access that is not a row is refused
#guard (verdictB (birEnv [.ldx 32 .ret .ctx 8, .exit])).isOk == false
-- `data` and `data_end` yield the packet's bounds; the length is
-- their difference, and a byte load past the end is refused
#guard verdictB (birEnv
  [.ldx 32 (v 0) .ctx 0, .ldx 32 (v 1) .ctx 4, .mov .w64 (v 2) (.reg (v 1)),
   .alu .sub .w64 (v 2) (.reg (v 0)), .mov .w64 .ret (.reg (v 2)), .exit])
  (shared [1, 2, 3]) == .ok 3
#guard verdictB (birEnv
  [.ldx 32 (v 0) .ctx 0, .ldx 8 .ret (v 0) 2, .exit]) (shared [1, 2, 3]) == .ok 3
#guard (verdictB (birEnv
  [.ldx 32 (v 0) .ctx 0, .ldx 8 .ret (v 0) 3, .exit]) (shared [1, 2, 3])).isOk == false
-- the carve as the flattening emits it: a bounds test on the moved
-- location, then the load
#guard verdictB (birEnv
  [.ldx 32 (v 0) .ctx 0, .ldx 32 (v 1) .ctx 4,
   .mov .w64 (v 2) (.reg (v 0)), .alu .add .w64 (v 2) (.imm 2),
   .jcond .gt .w64 (v 2) (.reg (v 1)) ⟨9⟩,
   .ldx 16 .ret (v 0) 0, .exit,
   .mov .w64 .ret (.imm 1), .exit] [(9, 7)]) (shared [0x34, 0x12]) == .ok 0x1234
#guard verdictB (birEnv
  [.ldx 32 (v 0) .ctx 0, .ldx 32 (v 1) .ctx 4,
   .mov .w64 (v 2) (.reg (v 0)), .alu .add .w64 (v 2) (.imm 2),
   .jcond .gt .w64 (v 2) (.reg (v 1)) ⟨9⟩,
   .ldx 16 .ret (v 0) 0, .exit,
   .mov .w64 .ret (.imm 1), .exit] [(9, 7)]) (shared [0x34]) == .ok 1

/-! ### Maps -/

-- direct value access: a store, then a load through `mapval`
#guard match runB (birEnv
  [.mapval (v 0) "counters" 8, .stx 64 (v 0) 0 (.imm 11), .ldx 64 .ret (v 0) 0, .exit]) with
  | .ok (11, st) => st.bytesAt (.map "counters" 0) 8 8 == Machine.leBytes 11 8
  | _ => false
-- a hash lookup by helper: the key in a frame object, absent then
-- present after an update
#guard verdictB (birEnv
  [.lea (v 0) "k", .stx 32 (v 0) 0 (.imm 3),
   .mapref (v 1) "table", .call (.builtin .lookup) [v 1, v 0] (some (v 2)),
   .jcond .ne .w64 (v 2) (.imm 0) ⟨1⟩,
   .lea (v 3) "val", .stx 64 (v 3) 0 (.imm 99),
   .call (.builtin .update) [v 1, v 0, v 3] (some (v 4)),
   .call (.builtin .lookup) [v 1, v 0] (some (v 2)),
   .jcond .eq .w64 (v 2) (.imm 0) ⟨2⟩,
   .ldx 64 .ret (v 2) 0, .exit,
   .mov .w64 .ret (.imm 7), .exit]
  [(1, 10), (2, 12)]
  [{ name := "k", size := 8, base := -8 }, { name := "val", size := 8, base := -16 }]) == .ok 99
-- a map pointer in arithmetic is refused
#guard (verdictB (birEnv
  [.mapref (v 1) "table", .alu .add .w64 (v 1) (.imm 1), .exit])).isOk == false

/-! ### Protocol and exit -/

-- a lock taken and not released: the exit is refused
#guard match verdictB (birEnv
  [.mapval (v 0) "counters" 0, .call (.builtin .lock) [v 0] none,
   .mov .w64 .ret (.imm 0), .exit]) with
  | .error m => m.endsWith "while a resource is held"
  | .ok _ => false
-- taken and released: the run halts, and a kernel call under the
-- lock is refused
#guard verdictB (birEnv
  [.mapval (v 0) "counters" 0, .call (.builtin .lock) [v 0] none,
   .call (.builtin .unlock) [v 0] none, .mov .w64 .ret (.imm 4), .exit]) == .ok 4
#guard match verdictB (birEnv
  [.mapval (v 0) "counters" 0, .call (.builtin .lock) [v 0] none,
   .call (.kernel "ktime") [] (some (v 1)),
   .call (.builtin .unlock) [v 0] none, .mov .w64 .ret (.imm 4), .exit]) with
  | .error m => (m.splitOn "while a spin lock is held").length == 2
  | .ok _ => false
-- a kernel call traced with its arguments, and `redirect`'s answer
#guard match runB (birEnv
  [.lddw (v 0) 5, .call (.kernel "redirect") [v 0] (some .ret), .exit]) with
  | .ok (4, st) => st.trace == [.call "redirect" [.scalar 5] (.ok (some (.scalar 4)))]
  | _ => false
-- an atomic add with fetch on a map value
#guard match runB (birEnv
  [.mapval (v 0) "counters" 0, .stx 64 (v 0) 0 (.imm 10), .lddw (v 1) 5,
   .atomic .add .w64 true (v 0) 0 (v 1), .mov .w64 .ret (.reg (v 1)), .exit]) with
  | .ok (10, st) => st.bytesAt (.map "counters" 0) 0 8 == Machine.leBytes 15 8
  | _ => false

/-! ### Read-only regions, the read-only packet, frames, and slots -/

-- a store into a map the program may only read is refused; a load
-- is admitted
#guard match verdictB (birEnv
  [.mapval (v 0) "rodata" 0, .stx 64 (v 0) 0 (.imm 1), .exit]) with
  | .error m => m.endsWith "which the program may only read"
  | .ok _ => false
#guard verdictB (birEnv [.mapval (v 0) "rodata" 0, .ldx 64 .ret (v 0) 0, .exit]) == .ok 0
-- a load from a map the program may only write is refused; a store
-- is admitted
#guard match verdictB (birEnv
  [.mapval (v 0) "wonly" 0, .ldx 64 .ret (v 0) 0, .exit]) with
  | .error m => m.endsWith "which the program may only write"
  | .ok _ => false
#guard verdictB (birEnv
  [.mapval (v 0) "wonly" 0, .stx 64 (v 0) 0 (.imm 1), .mov .w64 .ret (.imm 2), .exit]) == .ok 2
-- `update` on a map the program may only read is refused
#guard match verdictB (birEnv
  [.lea (v 0) "k", .stx 32 (v 0) 0 (.imm 0), .lea (v 3) "val", .stx 64 (v 3) 0 (.imm 9),
   .mapref (v 1) "rodata", .call (.builtin .update) [v 1, v 0, v 3] (some (v 4)), .exit]
  [] [{ name := "k", size := 8, base := -8 }, { name := "val", size := 8, base := -16 }]) with
  | .error m => m.endsWith "which the program may only read"
  | .ok _ => false
-- a store through the packet in a kind that may only read it is
-- refused; the same store in xdp is admitted
#guard match verdictB (birEnv
  [.ldx 32 (v 0) .ctx 0, .stx 8 (v 0) 0 (.imm 1), .exit] (kind := roPkt)) (shared [1, 2, 3]) with
  | .error m => m.endsWith "may only read the packet"
  | .ok _ => false
#guard verdictB (birEnv
  [.ldx 32 (v 0) .ctx 0, .stx 8 (v 0) 0 (.imm 7), .ldx 8 .ret (v 0) 0, .exit])
  (shared [1, 2, 3]) == .ok 7
-- a callee writes through the caller's frame location it received,
-- and the caller reads the byte back after the return
#guard verdictB (birEnv
  [.callSub ⟨1⟩ [.fp] (some (v 0)), .ldx 32 .ret .fp (-4), .exit,
   .arg (v 1) 0, .stx 32 (v 1) (-4) (.imm 5), .mov .w64 .ret (.imm 0), .exit] [(1, 3)]) == .ok 5
-- the callee's own frame, reached through a location it spilled into
-- the caller's frame, is refused after the return
#guard match verdictB (birEnv
  [.callSub ⟨1⟩ [.fp] (some (v 0)), .ldx 64 (v 2) .fp (-8), .ldx 32 .ret (v 2) (-4), .exit,
   .arg (v 1) 0, .stx 64 (v 1) (-8) (.reg .fp), .mov .w64 .ret (.imm 0), .exit] [(1, 4)]) with
  | .error m => (m.splitOn "a frame that has returned").length == 2
  | .ok _ => false
-- a load or store whose bytes touch the lock slot is refused, an
-- access beside it admitted, and the lock's own operations reach it
#guard match verdictB (birEnv [.mapval (v 0) "locked" 0, .ldx 32 .ret (v 0) 0, .exit]) with
  | .error m => m.endsWith "overlaps a slot field"
  | .ok _ => false
#guard match verdictB (birEnv
  [.mapval (v 0) "locked" 0, .stx 64 (v 0) 2 (.imm 1), .exit]) with
  | .error m => m.endsWith "overlaps a slot field"
  | .ok _ => false
#guard match verdictB (birEnv
  [.mapval (v 0) "locked" 0, .lddw (v 1) 1, .atomic .add .w32 false (v 0) 0 (v 1), .exit]) with
  | .error m => m.endsWith "overlaps a slot field"
  | .ok _ => false
#guard verdictB (birEnv
  [.mapval (v 0) "locked" 0, .stx 64 (v 0) 8 (.imm 6), .ldx 64 .ret (v 0) 8, .exit]) == .ok 6
#guard verdictB (birEnv
  [.mapval (v 0) "locked" 0, .call (.builtin .lock) [v 0] none,
   .call (.builtin .unlock) [v 0] none, .mov .w64 .ret (.imm 3), .exit]) == .ok 3

/-! ### The bytecode convention -/

-- the same call under the fixed convention and the kernel's layout:
-- `r1` the argument, `r2` the flags word, `r0` the result, `r1` dead
-- after
#guard runC (bcEnv
  [.lddw .r1 5, .mov .w64 .r2 (.imm 0), .call (.kernel "redirect") [] none, .exit]) == .ok 4
#guard (runC (bcEnv
  [.lddw .r1 5, .call (.kernel "redirect") [] none, .exit])).isOk == false
#guard (runC (bcEnv
  [.lddw .r1 5, .mov .w64 .r2 (.imm 0), .call (.kernel "redirect") [] none,
   .mov .w64 .r0 (.reg .r1), .exit])).isOk == false
-- the context arrives in `r1` and the frame through `r10`
#guard runC (bcEnv
  [.mov .w64 .r6 (.reg .r1), .lddw .r2 3, .stx 64 .r10 (-8) (.reg .r2),
   .ldx 64 .r0 .r10 (-8), .exit]) == .ok 3
-- offsets: a forward jump over one instruction
#guard runC (bcEnv
  [.mov .w64 .r0 (.imm 1), .ja 1, .mov .w64 .r0 (.imm 2), .exit]) == .ok 1

/-! ### Well-formedness -/

#guard (wf (birEnv [.mov .w64 .ret (.reg (v 3)), .exit])).isOk == false
#guard (wf (birEnv [.lddw (v 3) 1, .mov .w64 .ret (.reg (v 3)), .exit])).isOk == true
#guard (wf (birEnv [.lddw (v 3) 1, .ja ⟨4⟩, .exit])).isOk == false
#guard (wf (birEnv [.mov .w64 .fp (.imm 0), .exit])).isOk == false
-- a register written on one path only may be uninitialized at the
-- join
#guard (wf (birEnv
  [.lddw (v 0) 1, .jcond .eq .w64 (v 0) (.imm 0) ⟨1⟩, .lddw (v 1) 2,
   .mov .w64 .ret (.reg (v 1)), .exit] [(1, 3)])).isOk == false
#guard (wf (bcEnv [.lddw .r1 5, .mov .w64 .r2 (.imm 0),
                   .call (.kernel "redirect") [] none, .exit])).isOk == true
#guard (wf (bcEnv [.lddw .r1 5, .call (.kernel "redirect") [] none, .exit])).isOk == false
#guard (wf (bcEnv [.lddw .r1 5, .call (.kernel "redirect") [.r1] none, .exit])).isOk == false

end KoitTests.BPF
