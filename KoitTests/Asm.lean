import Koit.Compile.Asm
import Koit.Prelude.Stage1

/-!
Checks on the LLVM-syntax printer and the byte lines: the spellings
`llvm-mc` prints for each instruction form, and the byte order of a
word. The runner's round trip through `llvm-mc` is the real test;
these pin the forms it exercises least.
-/

open Koit Koit.Compile Koit.BPF

private def asm (ins : Instr Reg Int) : String :=
  match asmInstr Prelude.stage1 "xdp" ins with
  | .ok s => s
  | .error e => s!"error: {e}"

#guard asm (.alu .add .w64 1 (.reg 2)) == "r1 += r2"
#guard asm (.alu .arsh .w32 1 (.imm 24)) == "w1 s>>= 24"
#guard asm (.alu .sdiv .w64 1 (.reg 2)) == "r1 s/= r2"
#guard asm (.mov .w64 1 (.imm (-1))) == "r1 = -1"
#guard asm (.movsx .w32 16 1 2) == "w1 = (s16)w2"
#guard asm (.«end» .be 16 1) == "r1 = be16 r1"
#guard asm (.ldx 64 1 10 (-8)) == "r1 = *(u64 *)(r10 - 8)"
#guard asm (.ldx 32 2 1 0) == "w2 = *(u32 *)(r1 + 0)"
#guard asm (.stx 8 1 0 (.reg 2)) == "*(u8 *)(r1 + 0) = w2"
#guard asm (.stx 32 1 8 (.imm 5)) == "*(u32 *)(r1 + 8) = 5"
#guard asm (.ja (-5)) == "goto -5"
#guard asm (.ja 40000) == "gotol +40000"
#guard asm (.jcond .sge .w32 1 (.reg 2) (-3)) == "if w1 s>= w2 goto -3"
#guard asm (.jcond .set .w64 1 (.imm 8) 3) == "if r1 & 8 goto +3"
#guard asm (.lddw 1 (2 ^ 64 - 1)) == "r1 = -1 ll"
#guard asm (.mapref 1 "m") == "ld_pseudo r1, 1, 0"
#guard asm (.mapval 1 "m" 16) == "ld_pseudo r1, 2, 0"
#guard asm (.call (.builtin .lookup) [] none) == "call 1"
#guard asm (.call (.kernel "redirect") [] none) == "call 23"
#guard asm (.atomic .add .w64 false 1 0 2) == "lock *(u64 *)(r1 + 0) += r2"
#guard asm (.atomic .band .w32 true 1 0 2) == "w2 = atomic_fetch_and((u32 *)(r1 + 0), w2)"
#guard asm (.atomic .xchg .w32 true 1 0 2) == "w2 = xchg32_32(r1 + 0, w2)"
#guard asm (.atomic .cmpxchg .w64 true 1 0 2) == "r0 = cmpxchg_64(r1 + 0, r0, r2)"
#guard asm .exit == "exit"

-- the word `r1 = *(u32 *)(r6 + 0)` is 0x61 0x61 0x00 ... in memory
private def oneWord : Object :=
  { name := "p", kind := "xdp", section_ := "xdp", cpu := .v3,
    words := #[0x6161], relocs := [], notes := [] }

#guard oneWord.printBytes == "# program p\n0x61 0x61 0x00 0x00 0x00 0x00 0x00 0x00\n"
