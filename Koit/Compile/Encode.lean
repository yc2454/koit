import Koit.Compile.Alloc

/-!
Pass E, the encoding: bytecode to the kernel's words. One 64-bit word
per instruction, `opcode:8 dst:4 src:4 off:16 imm:32`, two for
`lddw`, with the opcode tables of the kernel's instruction-set
document; a map reference is `lddw` with the pseudo source register
the loader recognizes and a relocation naming the map; a call is the
helper's number, or a kfunc by name through a relocation. The object
also carries a note per call naming the callee the model sees, since
the words alone do not say which builtin a helper number stands for
once its size and flags are in registers; the notes are not loaded.
The one property worth proving is the round trip, `encode_decode`,
stated in `Rules.lean`: the words, the relocations, and the notes
decode to the program they came from.
-/

namespace Koit.Compile

open Koit.BPF (Instr Src Cls AluOp Cmp Endian Reg Bytecode Cpu Callee Builtin)
open Koit.Machine (toNatMod wrap)

/-- What the loader patches: a map's descriptor, a map value's
address, or a kfunc's BTF id. -/
inductive RelocKind where
  | mapFd (m : String)
  | mapValue (m : String) (off : Nat)
  | kfunc (name : String)
  deriving Repr, BEq, Inhabited

structure Reloc where
  index : Nat
  kind  : RelocKind
  deriving Repr, BEq, Inhabited

/-- The callee of the call at a word, as the model sees it. -/
structure Note where
  index  : Nat
  callee : Callee
  deriving Repr, BEq, Inhabited

/-- One program's object: its words with the relocations and the
notes, and what the loader needs to place it. -/
structure Object where
  name     : String
  kind     : String
  section_ : String
  cpu      : Cpu
  words    : Array Nat
  relocs   : List Reloc
  notes    : List Note
  deriving Inhabited

/-! ### The tables -/

def aluCode : AluOp → Nat
  | .add => 0x00 | .sub => 0x10 | .mul => 0x20 | .div | .sdiv => 0x30
  | .or => 0x40 | .and => 0x50 | .lsh => 0x60 | .rsh => 0x70
  | .mod | .smod => 0x90 | .xor => 0xa0 | .arsh => 0xc0

def cmpCode : Cmp → Nat
  | .eq => 0x10 | .gt => 0x20 | .ge => 0x30 | .set => 0x40 | .ne => 0x50
  | .sgt => 0x60 | .sge => 0x70 | .lt => 0xa0 | .le => 0xb0 | .slt => 0xc0 | .sle => 0xd0

def sizeCode (w : Nat) : Except String Nat :=
  match w with
  | 64 => pure 0x18 | 32 => pure 0x00 | 16 => pure 0x08 | 8 => pure 0x10
  | _ => throw s!"no access of {w} bits"

def atomicCode (op : Core.AtomicOp) (fetch : Bool) : Nat :=
  match op with
  | .add => 0x00 ||| (if fetch then 1 else 0)
  | .bor => 0x40 ||| (if fetch then 1 else 0)
  | .band => 0x50 ||| (if fetch then 1 else 0)
  | .bxor => 0xa0 ||| (if fetch then 1 else 0)
  | .xchg => 0xe1
  | .cmpxchg => 0xf1

/-- The class of an ALU or jump instruction: 64 or 32 bits. -/
def aluClass : Cls → Nat
  | .w64 => 0x07
  | .w32 => 0x04

def jmpClass : Cls → Nat
  | .w64 => 0x05
  | .w32 => 0x06

/-- The source bit: a register operand. -/
def srcBit : Src Reg → Nat
  | .reg _ => 0x08
  | .imm _ => 0x00

def srcReg : Src Reg → Nat
  | .reg r => r.val
  | .imm _ => 0

def srcImm : Src Reg → Int
  | .reg _ => 0
  | .imm k => k

/-! ### Encoding -/

/-- One word from its fields; the offset and the immediate must fit
their fields. -/
def word (code dst src : Nat) (off : Int) (imm : Int) : Except String Nat := do
  unless -32768 ≤ off && off < 32768 do throw s!"an offset of {off} does not fit 16 bits"
  unless -2 ^ 31 ≤ imm && imm < 2 ^ 31 do throw s!"an immediate of {imm} does not fit 32 bits"
  return code ||| (dst <<< 8) ||| (src <<< 12) ||| (toNatMod off 16 <<< 16) ||| (toNatMod imm 32 <<< 32)

/-- The helper number or the kfunc name a callee encodes as. -/
def calleeTarget (pre : Interface) (kind : String) : Callee → Except String (Nat ⊕ String)
  | .builtin b =>
    match b, b.helper with
    | _, some name =>
      match pre.helperId? name with
      | some id => pure (.inl id)
      | none => throw s!"{pre.kernel} has no helper bpf_{name}"
    | .enter r, none =>
      match pre.resource? r with
      | some { acquireKernel := some name, .. } => pure (.inr name)
      | _ => throw s!"no kernel function acquires `{r}`"
    | .leave r, none =>
      match pre.resource? r with
      | some decl => pure (.inr decl.normalExit)
      | none => throw s!"no declaration for `{r}`"
    | b, none => throw s!"`{b.print}` has no helper"
  | .kernel name =>
    match pre.call? name with
    | some decl =>
      match decl.implIn kind with
      | .helper id _ => pure (.inl id)
      | .kfunc kname _ => pure (.inr kname)
      | .inline => throw s!"`{name}` is inline and reaches the encoder as a call"
    | none => throw s!"unknown kernel function `{name}`"

/-- One instruction's words, with the relocation and the note it
adds at the index `i`. -/
def encodeInstr (pre : Interface) (kind : String) (cpu : Cpu) (i : Nat) (ins : Instr Reg Int) :
    Except String (List Nat × List Reloc × List Note) := do
  let one (w : Except String Nat) : Except String (List Nat × List Reloc × List Note) := do
    return ([← w], [], [])
  match ins with
  | .alu op cls d s =>
    let off : Int := match op with
      | .sdiv | .smod => 1
      | _ => 0
    one (word (aluClass cls ||| aluCode op ||| srcBit s) d.val (srcReg s) off (srcImm s))
  | .mov cls d s => one (word (aluClass cls ||| 0xb0 ||| srcBit s) d.val (srcReg s) 0 (srcImm s))
  | .movsx cls w d s => one (word (aluClass cls ||| 0xb0 ||| 0x08) d.val s.val w 0)
  | .«end» to w d =>
    one (word (0x04 ||| 0xd0 ||| (match to with | .be => 0x08 | .le => 0x00)) d.val 0 0 w)
  | .ldx w d s off => one (word (0x01 ||| 0x60 ||| (← sizeCode w)) d.val s.val off 0)
  | .stx w d off (.reg s) => one (word (0x03 ||| 0x60 ||| (← sizeCode w)) d.val s.val off 0)
  | .stx w d off (.imm k) => one (word (0x02 ||| 0x60 ||| (← sizeCode w)) d.val 0 off k)
  | .ja off =>
    if -32768 ≤ off && off < 32768 then one (word 0x05 0 0 off 0)
    else if cpu == .v4 then one (word 0x06 0 0 0 off)
    else throw s!"a jump of {off} instructions needs cpu v4"
  | .jcond cmp cls a b off =>
    one (word (jmpClass cls ||| cmpCode cmp ||| srcBit b) a.val (srcReg b) off (srcImm b))
  | .lddw d k =>
    unless k < 2 ^ 64 do throw s!"a constant of more than 64 bits"
    let lo : Nat := k % 2 ^ 32
    let hi : Nat := k / 2 ^ 32
    return ([← word 0x18 d.val 0 0 (wrap true 32 (lo : Int)), hi <<< 32], [], [])
  | .lea _ _ => throw "`lea` reaches the encoder"
  | .mapref d m =>
    return ([← word 0x18 d.val 1 0 0, 0], [{ index := i, kind := .mapFd m }], [])
  | .mapval d m k =>
    unless k < 2 ^ 31 do throw s!"a value offset of {k} does not fit"
    return ([← word 0x18 d.val 2 0 0, k <<< 32], [{ index := i, kind := .mapValue m k }], [])
  | .call h _ _ =>
    match ← calleeTarget pre kind h with
    | .inl id => return ([← word 0x85 0 0 0 id], [], [{ index := i, callee := h }])
    | .inr name =>
      return ([← word 0x85 0 2 0 0], [{ index := i, kind := .kfunc name }], [{ index := i, callee := h }])
  | .atomic op cls fetch d off s =>
    let size := match cls with
      | .w64 => 0x18
      | .w32 => 0x00
    one (word (0x03 ||| 0xc0 ||| size) d.val s.val off (atomicCode op fetch))
  | .exit => one (word 0x95 0 0 0 0)

/-- A program's object. -/
def encode (pre : Interface) (p : Bytecode) : Except String Object := do
  let some kind := pre.kind? p.kind | throw s!"unknown kind `{p.kind}`"
  let mut words : Array Nat := #[]
  let mut relocs : List Reloc := []
  let mut notes : List Note := []
  for ins in p.code do
    let (ws, rs, ns) ← encodeInstr pre p.kind p.cpu words.size ins
      |>.mapError (s!"in `{p.name}`: " ++ ·)
    words := words ++ ws.toArray
    relocs := relocs ++ rs
    notes := notes ++ ns
  return { name := p.name, kind := p.kind, section_ := kind.section_, cpu := p.cpu,
           words, relocs, notes }

/-! ### Decoding -/

/-- The fields of a word. -/
def fields (w : Nat) : Nat × Nat × Nat × Int × Int :=
  (w % 256, (w >>> 8) % 16, (w >>> 12) % 16, wrap true 16 ((w >>> 16) % 65536),
   wrap true 32 (w >>> 32))

def regOf (n : Nat) : Except String Reg :=
  if h : n < 11 then pure ⟨n, h⟩ else throw s!"register {n} does not exist"

def aluOfCode (code : Nat) (off : Int) : Except String AluOp :=
  match code, off with
  | 0x00, _ => pure .add | 0x10, _ => pure .sub | 0x20, _ => pure .mul
  | 0x30, 0 => pure .div | 0x30, 1 => pure .sdiv
  | 0x40, _ => pure .or | 0x50, _ => pure .and | 0x60, _ => pure .lsh | 0x70, _ => pure .rsh
  | 0x90, 0 => pure .mod | 0x90, 1 => pure .smod
  | 0xa0, _ => pure .xor | 0xc0, _ => pure .arsh
  | c, _ => throw s!"no ALU operation {c}"

def cmpOfCode (code : Nat) : Except String Cmp :=
  match code with
  | 0x10 => pure .eq | 0x20 => pure .gt | 0x30 => pure .ge | 0x40 => pure .set
  | 0x50 => pure .ne | 0x60 => pure .sgt | 0x70 => pure .sge | 0xa0 => pure .lt
  | 0xb0 => pure .le | 0xc0 => pure .slt | 0xd0 => pure .sle
  | c => throw s!"no comparison {c}"

def widthOf (size : Nat) : Except String Nat :=
  match size with
  | 0x18 => pure 64 | 0x00 => pure 32 | 0x08 => pure 16 | 0x10 => pure 8
  | s => throw s!"no access size {s}"

def atomicOf (imm : Int) : Except String (Core.AtomicOp × Bool) :=
  match imm with
  | 0x00 => pure (.add, false) | 0x01 => pure (.add, true)
  | 0x40 => pure (.bor, false) | 0x41 => pure (.bor, true)
  | 0x50 => pure (.band, false) | 0x51 => pure (.band, true)
  | 0xa0 => pure (.bxor, false) | 0xa1 => pure (.bxor, true)
  | 0xe1 => pure (.xchg, true) | 0xf1 => pure (.cmpxchg, true)
  | k => throw s!"no atomic operation {k}"

/-- The program an object decodes to, its code from the words with
the relocations and the notes. -/
def decode (pre : Interface) (o : Object) : Except String Bytecode := do
  let mut code : Array (Instr Reg Int) := #[]
  let mut i := 0
  while i < o.words.size do
    let (opcode, dstN, srcN, off, imm) := fields o.words[i]!
    let d ← regOf dstN
    let s ← regOf srcN
    let cls : Cls := if opcode % 8 == 0x07 || opcode % 8 == 0x05 then .w64 else .w32
    let srcX := opcode % 16 ≥ 8
    let op := opcode / 16 * 16
    let ins ← match opcode % 8 with
      | 0x07 | 0x04 =>
        if op == 0xb0 then
          if srcX && off != 0 then pure (Instr.movsx cls off.toNat d s)
          else pure (Instr.mov cls d (if srcX then .reg s else .imm imm))
        else if op == 0xd0 then
          pure (Instr.«end» (if srcX then .be else .le) imm.toNat d)
        else
          pure (Instr.alu (← aluOfCode op off) cls d (if srcX then .reg s else .imm imm))
      | 0x01 =>
        unless op == 0x60 || op == 0x70 do throw s!"no load {opcode}"
        pure (Instr.ldx (← widthOf (opcode / 8 % 4 * 8)) d s off)
      | 0x00 =>
        unless opcode == 0x18 do throw s!"no load {opcode}"
        unless i + 1 < o.words.size do throw "a truncated `lddw`"
        let next := o.words[i + 1]!
        let ins ← match o.relocs.find? (·.index == i) with
          | some { kind := .mapFd m, .. } => pure (Instr.mapref d m)
          | some { kind := .mapValue m k, .. } => pure (Instr.mapval d m k)
          | some { kind := .kfunc _, .. } => throw "a kfunc relocation on a constant"
          | none => pure (Instr.lddw d (toNatMod imm 32 + (next >>> 32) * 2 ^ 32))
        i := i + 1
        pure ins
      | 0x03 =>
        if op == 0x60 || op == 0x70 then
          pure (Instr.stx (← widthOf (opcode / 8 % 4 * 8)) d off (.reg s))
        else if op == 0xc0 || op == 0xd0 then
          let (aop, fetch) ← atomicOf imm
          let acls : Cls := if opcode == 0xdb then .w64 else if opcode == 0xc3 then .w32
            else default
          unless opcode == 0xdb || opcode == 0xc3 do throw s!"no atomic {opcode}"
          pure (Instr.atomic aop acls fetch d off s)
        else throw s!"no store {opcode}"
      | 0x02 =>
        unless op == 0x60 || op == 0x70 do throw s!"no store {opcode}"
        pure (Instr.stx (← widthOf (opcode / 8 % 4 * 8)) d off (.imm imm))
      | 0x05 | 0x06 =>
        if op == 0x00 then pure (Instr.ja (if opcode == 0x05 then off else imm))
        else if op == 0x80 then
          match o.notes.find? (·.index == i) with
          | some n => pure (Instr.call n.callee [] none)
          | none => throw s!"no note for the call at {i}"
        else if op == 0x90 then pure Instr.exit
        else pure (Instr.jcond (← cmpOfCode op) cls d (if srcX then .reg s else .imm imm) off)
      | c => throw s!"no instruction class {c}"
    code := code.push ins
    i := i + 1
  return { name := o.name, kind := o.kind, code, cpu := o.cpu }

/-! ### Printing -/

def hex16 (w : Nat) : String :=
  let ds := Nat.toDigits 16 w
  String.ofList (List.replicate (16 - ds.length) '0' ++ ds)

def Object.print (o : Object) : String :=
  let header := s!"object {o.name} : {o.kind} section {o.section_}"
  let words := o.words.toList.zipIdx.map fun (w, i) => s!"  {i}: {hex16 w}"
  let relocs := o.relocs.map fun r => match r.kind with
    | .mapFd m => s!"  reloc {r.index}: map {m}"
    | .mapValue m off => s!"  reloc {r.index}: map {m} value + {off}"
    | .kfunc n => s!"  reloc {r.index}: kfunc {n}"
  "\n".intercalate ([header] ++ words ++ relocs) ++ "\n"

end Koit.Compile
