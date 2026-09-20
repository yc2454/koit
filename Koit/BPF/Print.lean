import Koit.BPF.Syntax

/-!
The printer of the instruction set, one instruction per line in the
notation of `bir.md` section 3, over any register and jump-target
type given their spellings; BIR prints its labels before the
instruction they name, bytecode its offsets on the jump. `koitc
lower --bir` and `--bytecode` print through it, and the runner
compares the bytecode printout with the disassembler's reading of the
encoded words.
-/

namespace Koit.BPF

def Src.print (pr : ρ → String) : Src ρ → String
  | .reg r => pr r
  | .imm k => toString k

/-- An instruction, with the registers spelled by `pr` and the jump
targets by `pt`. -/
def Instr.print (pr : ρ → String) (pt : τ → String) : Instr ρ τ → String
  | .alu op cls d s => s!"{op.print}({cls.print}) {pr d}, {s.print pr}"
  | .mov cls d s => s!"mov({cls.print}) {pr d}, {s.print pr}"
  | .movsx cls w d s => s!"movsx({cls.print}, {w}) {pr d}, {pr s}"
  | .«end» to w d => s!"end({to.print}, {w}) {pr d}"
  | .ldx w d s off => s!"ldx({w}) {pr d}, [{pr s} {offStr off}]"
  | .stx w d off s => s!"stx({w}) [{pr d} {offStr off}], {s.print pr}"
  | .ja t => s!"ja {pt t}"
  | .jcond cmp cls a b t => s!"j{cmp.print}({cls.print}) {pr a}, {b.print pr}, {pt t}"
  | .lddw d k => s!"lddw {pr d}, {k}"
  | .lea d obj => s!"lea {pr d}, {obj}"
  | .mapref d m => s!"mapref {pr d}, {m}"
  | .mapval d m k => s!"mapval {pr d}, {m} + {k}"
  | .call h args dst =>
    s!"call {h.print}" ++
      (if args.isEmpty then "" else " (" ++ ", ".intercalate (args.map pr) ++ ")") ++
      (match dst with
       | some d => s!" -> {pr d}"
       | none => "")
  | .atomic op cls fetch d off s =>
    s!"atomic {(op.spelling.drop 7).toString}({cls.print}{if fetch then ", fetch" else ""}) \
      [{pr d} {offStr off}], {pr s}"
  | .exit => "exit"
where
  offStr (off : Int) : String := if off < 0 then s!"- {-off}" else s!"+ {off}"

/-- A program: its objects and registers as a header, then the code
with each label on the line before the instruction it names. -/
def Program.print (pr : ρ → String) (pt : τ → String) (p : Program ρ τ) : String :=
  let header :=
    [s!"program {p.name} : {p.kind}"] ++
    p.objects.map (fun o => s!"  frame {o.name} : {o.size} at {o.base}") ++
    (if p.regs.isEmpty then [] else
      [s!"  regs " ++ ", ".intercalate (p.regs.map fun (r, c) =>
        s!"{pr r} : {match c with
          | .scalar => "scalar" | .location => "location" | .handle => "handle"}")])
  let labelsAt (i : Nat) : List String :=
    p.labels.filterMap fun (l, at_) => if at_ == i then some s!"L{l}:" else none
  let body := (List.range p.code.size).flatMap fun i =>
    labelsAt i ++ [s!"  {i}: {(p.code[i]!).print pr pt}"]
  "\n".intercalate (header ++ body) ++ "\n"

def BIR.print (p : BIR) : String := Program.print VReg.print Label.print p

def Bytecode.print (p : Bytecode) : String :=
  Program.print Reg.print (fun off => if off < 0 then s!"{off}" else s!"+{off}") p

end Koit.BPF
