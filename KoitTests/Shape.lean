import Koit.Syntax.Parser
import Koit.Core.Desugar
import Koit.Compile.Shape
import Koit.Interface.Interface

/-!
Checks on the shape checker: the compiled corpus programs pass L1 to
L3, and hand-written inputs that break each lemma are caught: an LIR
test with no conditional jump, a cast with no instruction of its
shape, a packet access with no comparison on its path or with one
that shows too few bytes, and an index no comparison bounds.
-/

open Koit Koit.Syntax Koit.Core Koit.Check Koit.Compile Koit.BPF

/-- The reports of a unit compiled under cpu v4. -/
private def shapeOf (s : String) : Except String (List ShapeReport) := do
  let u ← match parse s with
    | .ok u => pure u
    | .error e => throw s!"parse: {e.msg}"
  let core := desugar Interface.v6_8 u
  let checked ← match checkUnit Interface.v6_8 core with
    | .error d => throw s!"check: {d}"
    | .ok c => pure c
  let openLir ← Compile.lower Interface.v6_8 (Compile.fold Interface.v6_8 core checked)
  let C ← Compile.compile Interface.v6_8 .v4 core checked
  return shapeUnit Interface.v6_8 core openLir C

private def clean (s : String) : Bool :=
  match shapeOf s with
  | .ok rs => shapeOk rs
  | .error _ => false

/-- The errors, for reading a failure. -/
private def errorsOf (s : String) : List String :=
  match shapeOf s with
  | .ok rs => rs.flatMap (·.errors)
  | .error e => [e]

private def lines (ls : List String) : String := "\n".intercalate ls

/-! ### The corpus shapes -/

private def picker : String :=
  lines ["const M = 16",
         "const ETH_P_VLAN = hton(0x8100)", "const ETH_P_IP   = hton(0x0800)",
         "type EthHdr  = { dst: u8[6], src: u8[6], proto: be16 }",
         "type VlanHdr = { tci: be16, proto: be16 }",
         "type Backend = { ip: be32, ifindex: u32 }",
         "map policy   : array[1] of { cur: u32 where cur < M }",
         "map backends : array[1] of Backend[M]",
         "program pick : xdp",
         "  verdict in { PASS, DROP, ABORTED, REDIRECT }",
         "  preserve pkt", "  default { abort }", "  on short_packet { drop }", "{",
         "  var off = 0", "  let eth = pkt.view<EthHdr>(off)?", "  off += EthHdr.size",
         "  var proto = eth.proto",
         "  repeat 2 {", "    if proto != ETH_P_VLAN { break }",
         "    let tag = pkt.view<VlanHdr>(off)?", "    proto = tag.proto",
         "    off += VlanHdr.size", "  }",
         "  if proto != ETH_P_IP { pass }",
         "  let cur = policy[0].cur?", "  let be  = backends[0][cur]",
         "  let v   = redirect(be.ifindex)?", "  return v", "}",
         "program rotate : syscall {",
         "  policy[0].cur = (policy[0].cur + 1) % M", "}"]

#guard clean picker

-- a view written through, a byte loop over it, and a cast
private def writer : String :=
  lines ["type Hdr = { a: u8, b: u16, c: u32 }",
         "map stats : array[8] of { n: u64 }",
         "program w : xdp", "  default { drop }", "  on short_packet { stats[reason & 7].n += 1; abort }", "{",
         "  let h = pkt.view<Hdr>(0)?",
         "  h.c = (h.b as u32) + 1",
         "  for i in 0..4 { if i < 2 { stats[i].n += h.a as u64 } }",
         "  pass", "}"]

#guard clean writer

/-! ### Inputs that break each lemma -/

/-- A BIR program over `xdp` from its code and labels, with locations
in `v0` to `v2` and a scalar in `v3`. -/
private def bir (code : List (Instr VReg Label)) (labels : List (Nat × Nat) := []) : BIR :=
  { name := "t", kind := "xdp", code := code.toArray, labels,
    regs := [(.v 0, .location), (.v 1, .location), (.v 2, .location), (.v 3, .scalar),
             (.v 4, .scalar)] }

private def xdp : Interface.KindDecl := (Interface.v6_8.kind? "xdp").get!

private def l3 (B : BIR) : List String :=
  (L3.run { pre := Interface.v6_8, kind := xdp, B }).1

private def tail : List (Instr VReg Label) := [.mov .w64 .ret (.imm 2), .exit]

-- a packet access with no comparison at all
#guard !(l3 (bir ([.ldx 32 (.v 0) .ctx 0, .ldx 8 (.v 3) (.v 0) 0] ++ tail))).isEmpty

-- the view test, two bytes shown: a halfword passes, a word does not,
-- and the else branch reads nothing
private def viewed (w : Nat) : BIR :=
  bir [.ldx 32 (.v 0) .ctx 0, .mov .w64 (.v 1) (.reg (.v 0)), .alu .add .w64 (.v 1) (.imm 2),
       .ldx 32 (.v 2) .ctx 4, .jcond .gt .w64 (.v 1) (.reg (.v 2)) ⟨0⟩,
       .ldx w (.v 3) (.v 0) 0, .mov .w64 .ret (.imm 2), .exit] [(0, 6)]

#guard (l3 (viewed 16)).isEmpty
#guard !(l3 (viewed 32)).isEmpty

-- the same fact from the other side and the taken branch
private def viewedTaken : BIR :=
  bir [.ldx 32 (.v 0) .ctx 0, .mov .w64 (.v 1) (.reg (.v 0)), .alu .add .w64 (.v 1) (.imm 2),
       .ldx 32 (.v 2) .ctx 4, .jcond .ge .w64 (.v 2) (.reg (.v 1)) ⟨1⟩,
       .ja ⟨0⟩, .ldx 16 (.v 3) (.v 0) 0, .mov .w64 .ret (.imm 2), .exit] [(0, 7), (1, 6)]

#guard (l3 viewedTaken).isEmpty

-- a variable offset: the pointer the add makes is the one tested, and
-- a pointer from a different add is not
private def offsetView (tested : Bool) : BIR :=
  bir ([.ldx 32 (.v 0) .ctx 0, .mov .w64 (.v 3) (.imm 4),
        .mov .w64 (.v 1) (.reg (.v 0)), .alu .add .w64 (.v 1) (.reg (.v 3)),
        .mov .w64 (.v 2) (.reg (.v 1)), .alu .add .w64 (.v 2) (.imm 1),
        .ldx 32 (.v 0) .ctx 4, .jcond .gt .w64 (.v 2) (.reg (.v 0)) ⟨0⟩] ++
       (if tested then [] else
        [.ldx 32 (.v 0) .ctx 0, .mov .w64 (.v 1) (.reg (.v 0)), .alu .add .w64 (.v 1) (.reg (.v 3))]) ++
       [.ldx 8 (.v 4) (.v 1) 0, .mov .w64 .ret (.imm 2), .exit])
      [(0, if tested then 9 else 12)]

#guard (l3 (offsetView true)).isEmpty
#guard !(l3 (offsetView false)).isEmpty

-- an index into a map value: a loaded word needs a comparison, and a
-- comparison on its path bounds it
private def indexed (tested : Bool) : BIR :=
  bir ([.mapval (.v 0) "m" 0, .ldx 64 (.v 3) (.v 0) 8] ++
       (if tested then [.jcond .ge .w64 (.v 3) (.imm 4) ⟨0⟩] else []) ++
       [.mov .w64 (.v 1) (.reg (.v 0)), .alu .add .w64 (.v 1) (.reg (.v 3)),
        .ldx 8 (.v 4) (.v 1) 0, .mov .w64 .ret (.imm 2), .exit])
      [(0, if tested then 6 else 5)]

#guard (l3 (indexed true)).isEmpty
#guard !(l3 (indexed false)).isEmpty

-- a resize stales the pointer
private def resized : BIR :=
  bir [.ldx 32 (.v 0) .ctx 0, .mov .w64 (.v 1) (.reg (.v 0)), .alu .add .w64 (.v 1) (.imm 2),
       .ldx 32 (.v 2) .ctx 4, .jcond .gt .w64 (.v 1) (.reg (.v 2)) ⟨0⟩,
       .mov .w64 (.v 3) (.imm 0), .call (.kernel "pkt.adjust_head") [.v 3] (some (.v 4)),
       .ldx 16 (.v 3) (.v 0) 0, .mov .w64 .ret (.imm 2), .exit] [(0, 8)]

#guard !(l3 resized).isEmpty

-- L1: a test in LIR with no conditional jump in BIR
private def oneTest : List LIR.Stmt :=
  [.ite default { op := .lt, signed := false, w := 32, l := .lit 32 0, r := .lit 32 1 } [] []]

private def noJump : BIR := bir tail

private def noJumpBytecode : Bytecode :=
  { name := "t", kind := "xdp", code := #[.mov .w64 0 (.imm 2), .exit] }

#guard !(passL1 oneTest noJump noJumpBytecode).1.isEmpty
#guard (passL1 [] noJump noJumpBytecode).1.isEmpty

-- L2: a narrowing cast with no mask in the code
private def oneCast : List LIR.Stmt :=
  [.«let» default "x" .u8 (.cast false 32 false 8 (.lit 32 300))]

#guard !(passL2 oneCast noJump).1.isEmpty
#guard (passL2 oneCast (bir ([.alu .and .w32 (.v 3) (.imm 255)] ++ tail))).1.isEmpty
