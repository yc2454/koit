import Koit.Compile.Encode

/-!
The bytecode in the assembler syntax of LLVM's BPF backend, the form
kernel developers read and `llvm-mc` prints, and the words as the
byte lines its disassembler reads. The two serve the round trip the
runner makes when `llvm-mc` is present: our words disassembled by
LLVM must print as our program in this syntax, and our program
assembled by LLVM must encode to our words. That is the independent
reading of the encoder's word layout until a kernel is in the loop;
it is a check, not a proof, and it needs no LLVM to build or to test
the rest.
-/

namespace Koit.Compile

open Koit.BPF (Instr Src Cls AluOp Cmp Reg Bytecode Cpu)
open Koit.Core (AtomicOp)

/-- A register at a class: `r1` at 64 bits, `w1` at 32. -/
def asmReg (cls : Cls) (r : Reg) : String :=
  match cls with
  | .w64 => s!"r{r.val}"
  | .w32 => s!"w{r.val}"

def asmSrc (cls : Cls) : Src Reg → String
  | .reg r => asmReg cls r
  | .imm k => toString k

/-- `(r1 + 8)`, `(r10 - 8)`. -/
def asmAddr (r : Reg) (off : Int) : String :=
  if off < 0 then s!"(r{r.val} - {-off})" else s!"(r{r.val} + {off})"

/-- `+5`, `-3`. -/
def asmRel (off : Int) : String := if off < 0 then s!"{off}" else s!"+{off}"

def asmAlu : AluOp → String
  | .add => "+"
  | .sub => "-"
  | .mul => "*"
  | .div => "/"
  | .sdiv => "s/"
  | .mod => "%"
  | .smod => "s%"
  | .and => "&"
  | .or => "|"
  | .xor => "^"
  | .lsh => "<<"
  | .rsh => ">>"
  | .arsh => "s>>"

def asmCmp : Cmp → String
  | .eq => "=="
  | .ne => "!="
  | .gt => ">"
  | .ge => ">="
  | .lt => "<"
  | .le => "<="
  | .sgt => "s>"
  | .sge => "s>="
  | .slt => "s<"
  | .sle => "s<="
  | .set => "&"

/-- The class LLVM spells the data register of a `w`-bit access at. -/
def dataCls (w : Nat) : Cls := if w < 64 then .w32 else .w64

/-- One instruction in LLVM's syntax; the callee's number needs the
call table. -/
def asmInstr (pre : Interface) (kind : String) (ins : Instr Reg Int) : Except String String := do
  match ins with
  | .alu op cls d s => return s!"{asmReg cls d} {asmAlu op}= {asmSrc cls s}"
  | .mov cls d s => return s!"{asmReg cls d} = {asmSrc cls s}"
  | .movsx cls w d s => return s!"{asmReg cls d} = (s{w}){asmReg cls s}"
  | .«end» to w d => return s!"r{d.val} = {to.print}{w} r{d.val}"
  -- under cpu v3 and v4 the data register of a narrow access is a `w`
  | .ldx w d s off => return s!"{asmReg (dataCls w) d} = *(u{w} *){asmAddr s off}"
  | .stx w d off s => return s!"*(u{w} *){asmAddr d off} = {asmSrc (dataCls w) s}"
  | .ja off =>
    return (if -32768 ≤ off && off < 32768 then s!"goto {asmRel off}" else s!"gotol {asmRel off}")
  | .jcond cmp cls a b off =>
    return s!"if {asmReg cls a} {asmCmp cmp} {asmSrc cls b} goto {asmRel off}"
  | .lddw d k =>
    -- LLVM prints the constant signed
    let v : Int := if k ≥ 2 ^ 63 then (k : Int) - 2 ^ 64 else k
    return s!"r{d.val} = {v} ll"
  | .lea .. => throw "`lea` in bytecode"
  | .mapref d _ => return s!"ld_pseudo r{d.val}, 1, 0"
  | .mapval d _ _ => return s!"ld_pseudo r{d.val}, 2, 0"
  | .call h _ _ =>
    match ← calleeTarget pre kind h with
    | .inl id => return s!"call {id}"
    | .inr name => return s!"call {name}"
  | .callSub off _ _ => return s!"call {off}"
  | .arg .. => throw "`arg` in bytecode"
  | .atomic op cls fetch d off s =>
    let bits := cls.bits
    let name : String := match op with
      | .add => "add" | .band => "and" | .bor => "or" | .bxor => "xor"
      | .xchg => "xchg" | .cmpxchg => "cmpxchg"
    let sym : String := match op with
      | .add => "+" | .band => "&" | .bor => "|" | .bxor => "^" | _ => ""
    let suffix := match cls with
      | .w64 => "_64"
      | .w32 => "32_32"
    let addr := asmAddr d off
    let r0 := asmReg cls 0
    match op with
    | .xchg => return s!"{asmReg cls s} = xchg{suffix}({addr.drop 1 |>.dropRight 1}, {asmReg cls s})"
    | .cmpxchg =>
      return s!"{r0} = cmpxchg{suffix}({addr.drop 1 |>.dropRight 1}, {r0}, {asmReg cls s})"
    | _ =>
      if fetch then
        return s!"{asmReg cls s} = atomic_fetch_{name}((u{bits} *){addr}, {asmReg cls s})"
      else return s!"lock *(u{bits} *){addr} {sym}= {asmReg cls s}"
  | .exit => return "exit"

/-- A program, one instruction per line under a comment naming it. -/
def printAsm (pre : Interface) (p : Bytecode) : Except String String := do
  -- a subprogram call names the callee's label, which the assembler
  -- resolves to the offset the comment carries; the label is placed
  -- at the callee's entry
  let mut lines : List String := []
  for (ins, i) in p.code.toList.zipIdx do
    if let some (n, _) := p.subs.find? (·.2 == i) then lines := lines ++ [s!"{n}:"]
    match ins with
    | .callSub off _ _ =>
      let t := (i : Int) + off + 1
      match p.subs.find? fun (_, e) => (e : Int) == t with
      | some (n, _) => lines := lines ++ [s!"call {n} # {off}"]
      | none => throw s!"a subprogram call to instruction {t}, which no subprogram starts at"
    | _ => lines := lines ++ [← asmInstr pre p.kind ins]
  return "\n".intercalate (s!"# program {p.name}" :: lines) ++ "\n"

/-- The words of an object as `llvm-mc --disassemble` reads them:
the bytes of each word in memory order, little-endian, one word per
line, under a comment naming the program. -/
def Object.printBytes (o : Object) : String :=
  let byte (b : Nat) : String :=
    let digits := "0123456789abcdef".toList
    s!"0x{digits[b / 16]!}{digits[b % 16]!}"
  let wordBytes (w : Nat) : String :=
    " ".intercalate ((List.range 8).map fun i => byte (w / 256 ^ i % 256))
  "\n".intercalate (s!"# program {o.name}" :: o.words.toList.map wordBytes) ++ "\n"

end Koit.Compile
