import Koit.Interface.Decls
import Koit.Core.Print

/-!
The eBPF instruction set, cpu v3 with the v4 additions, as one syntax
over two parameters: the register type and the jump-target type. BIR
is its instance over virtual registers and labels, bytecode its
instance over `r0` to `r10` and signed offsets, and the two differ in
nothing else but the conventions of `State.lean`: whether a call's
operands are on the instruction or in `r1` to `r5`, and whether
`lea` is admitted. The semantics of every instruction is written
once, in `Semantics.lean`, and pass E prints the bytecode instance to
the kernel's words.

The map builtins take the map's handle as their first operand, the
value `mapref` yields, so that one call here is one call in the
kernel's stream; `copy` and `fill` of LIR do not exist here, the
flattening expands them into loads and stores.
-/

namespace Koit.BPF

open Koit.Core (Resource AtomicOp)

/-- The operation class, the kernel's ALU and ALU32, JMP and JMP32
distinction. -/
inductive Cls where
  | w64
  | w32
  deriving Repr, BEq, DecidableEq, Inhabited

def Cls.bits : Cls → Nat
  | .w64 => 64
  | .w32 => 32

def Cls.print (c : Cls) : String := toString c.bits

/-- The ALU operations; `sdiv` and `smod` are v4. -/
inductive AluOp where
  | add | sub | mul | div | sdiv | mod | smod
  | and | or | xor | lsh | rsh | arsh
  deriving Repr, BEq, DecidableEq, Inhabited

def AluOp.print : AluOp → String
  | .add => "add" | .sub => "sub" | .mul => "mul" | .div => "div" | .sdiv => "sdiv"
  | .mod => "mod" | .smod => "smod" | .and => "and" | .or => "or" | .xor => "xor"
  | .lsh => "lsh" | .rsh => "rsh" | .arsh => "arsh"

/-- The comparisons of `jcond`; the `s` forms are signed, `set` tests
`a & b`. -/
inductive Cmp where
  | eq | ne | gt | ge | lt | le | sgt | sge | slt | sle | set
  deriving Repr, BEq, DecidableEq, Inhabited

def Cmp.print : Cmp → String
  | .eq => "eq" | .ne => "ne" | .gt => "gt" | .ge => "ge" | .lt => "lt" | .le => "le"
  | .sgt => "sgt" | .sge => "sge" | .slt => "slt" | .sle => "sle" | .set => "set"

/-- The byte order `end` converts to. -/
inductive Endian where
  | be
  | le
  deriving Repr, BEq, DecidableEq, Inhabited

def Endian.print : Endian → String
  | .be => "be"
  | .le => "le"

/-- The builtins of the machine: the map and ring operations with the
kernel's fixed semantics, the protocol operations of the resource
declarations, and `printk`, whose format is metadata of the instruction. -/
inductive Builtin where
  | lookup
  | update
  | delete
  | reserve (n : Nat)
  | submit
  | discard
  | lock
  | unlock
  | enter (r : Resource)
  | leave (r : Resource)
  /-- `printk` with its format, the number of scalars the source
  passed, so that the trace records them at every level, and the
  frame object holding the kernel's format with its size, which the
  allocation passes to the helper. -/
  | printk (fmt : String) (n : Nat) (size : Nat)
  deriving Repr, BEq, Inhabited

/-- What a `call` calls: a builtin, or a kernel function by the name
of its declaration. -/
inductive Callee where
  | builtin (b : Builtin)
  | kernel (decl : String)
  deriving Repr, BEq, Inhabited

/-- A source operand: a register, or the immediate of the `_imm`
forms. -/
inductive Src (ρ : Type) where
  | reg (r : ρ)
  | imm (k : Int)
  deriving Repr, BEq, Inhabited

/-- The instructions. `w` is an access or extension width in
`{8, 16, 32, 64}`, `off` a signed displacement. -/
inductive Instr (ρ τ : Type) where
  /-- `alu(op, cls) d s` and `alu_imm`. -/
  | alu (op : AluOp) (cls : Cls) (d : ρ) (s : Src ρ)
  /-- `mov(cls) d s` and `mov_imm`. -/
  | mov (cls : Cls) (d : ρ) (s : Src ρ)
  /-- v4: the sign-extending move from `w` in `{8, 16, 32}`. -/
  | movsx (cls : Cls) (w : Nat) (d s : ρ)
  /-- `end(to, w) d`, `w` in `{16, 32, 64}`. -/
  | «end» (to : Endian) (w : Nat) (d : ρ)
  /-- `ldx(w) d [s + off]`. -/
  | ldx (w : Nat) (d s : ρ) (off : Int)
  /-- `stx(w) [d + off] s` and `st(w) [d + off] k`. -/
  | stx (w : Nat) (d : ρ) (off : Int) (s : Src ρ)
  | ja (t : τ)
  /-- `jcond(cmp, cls) a b L` and `jcond_imm`. -/
  | jcond (cmp : Cmp) (cls : Cls) (a : ρ) (b : Src ρ) (t : τ)
  /-- A 64-bit constant. -/
  | lddw (d : ρ) (k : Nat)
  /-- BIR only: the location of a frame object. -/
  | lea (d : ρ) (obj : String)
  /-- The map's handle. -/
  | mapref (d : ρ) (m : String)
  /-- Direct value access: `k` bytes into the value of an `array[1]`
  map. -/
  | mapval (d : ρ) (m : String) (k : Nat)
  /-- `call h`: in BIR with its operands and its result register on
  the instruction; in bytecode with none, the arguments in `r1` to
  `r5` and the result in `r0`. -/
  | call (h : Callee) (args : List ρ) (dst : Option ρ)
  /-- `atomic(op, cls, fetch) [d + off] s`. -/
  | atomic (op : AtomicOp) (cls : Cls) (fetch : Bool) (d : ρ) (off : Int) (s : ρ)
  | exit
  deriving Repr, BEq, Inhabited

/-- The class of a virtual register, metadata for the allocation. -/
inductive RegClass where
  | scalar
  | location
  | handle
  deriving Repr, BEq, DecidableEq, Inhabited

/-- The cpu version a program is compiled for. -/
inductive Cpu where
  | v3
  | v4
  deriving Repr, BEq, DecidableEq, Inhabited

/-- A frame object: a stack object of the source or a key frame the
lowering added, with the offset from the frame's top the flattening
assigned it, negative and 8-aligned. -/
structure FrameObj where
  name  : String
  size  : Nat
  align : Nat := 8
  base  : Int
  deriving Repr, Inhabited

/-- One flat program per koit program: its instructions, the labels
as a table from label number to instruction index, its frame
objects, and, in BIR, its virtual registers with their classes. -/
structure Program (ρ τ : Type) where
  name    : String
  kind    : String
  code    : Array (Instr ρ τ)
  labels  : List (Nat × Nat) := []
  objects : List FrameObj := []
  regs    : List (ρ × RegClass) := []
  cpu     : Cpu := .v3
  deriving Inhabited

/-! ### The two instances -/

/-- BIR's virtual registers: the four the flattening designates, and
the numbered ones. `ctx` holds the context location from entry to
exit and `fp` the frame's, both read-only; `ret` carries a verdict to
`exit` and is the `r0` of `cmpxchg`; `reason` carries a failure's
reason to its handler. -/
inductive VReg where
  | ctx
  | fp
  | ret
  | reason
  | v (n : Nat)
  deriving Repr, BEq, DecidableEq, Inhabited

def VReg.print : VReg → String
  | .ctx => "v_ctx"
  | .fp => "v_fp"
  | .ret => "v_ret"
  | .reason => "v_reason"
  | .v n => s!"v{n}"

/-- A label of BIR, by number. -/
structure Label where
  id : Nat
  deriving Repr, BEq, DecidableEq, Inhabited

def Label.print (l : Label) : String := s!"L{l.id}"

/-- Bytecode's registers, `r0` to `r10`. -/
abbrev Reg := Fin 11

def Reg.print (r : Reg) : String := s!"r{r.val}"

def Reg.r0 : Reg := 0
def Reg.r1 : Reg := 1
def Reg.r2 : Reg := 2
def Reg.r3 : Reg := 3
def Reg.r4 : Reg := 4
def Reg.r5 : Reg := 5
def Reg.r6 : Reg := 6
def Reg.r7 : Reg := 7
def Reg.r8 : Reg := 8
def Reg.r9 : Reg := 9
def Reg.r10 : Reg := 10

/-- BIR: the instruction set over virtual registers and labels. -/
abbrev BIR := Program VReg Label

/-- Bytecode: the instruction set over `r0` to `r10` and signed
instruction offsets. -/
abbrev Bytecode := Program Reg Int

/-! ### Helpers on the syntax -/

/-- How many operands a builtin takes; `printk` as many as the source
passed. -/
def Builtin.arity : Builtin → Nat
  | .lookup | .delete => 2
  | .update => 3
  | .reserve _ | .submit | .discard | .lock | .unlock => 1
  | .enter _ | .leave _ => 0
  | .printk _ n _ => n + 1

/-- The kernel's argument layout of a builtin, for the fixed
convention and the encoder: the map operations take the map first
and a flags word last, `reserve` its size, `printk` the format's
location and size before its arguments. -/
def Builtin.abi : Builtin → List Interface.AbiArg
  | .lookup => [.arg 0, .arg 1]
  | .update => [.arg 0, .arg 1, .arg 2, .const 0]
  | .delete => [.arg 0, .arg 1]
  | .reserve n => [.arg 0, .const n, .const 0]
  | .submit | .discard => [.arg 0, .const 0]
  | .lock | .unlock => [.arg 0]
  | .enter _ | .leave _ => []
  | .printk _ n size => [.fmt, .const size] ++ (List.range n).map fun i => .arg (i + 1)

/-- The kernel helper a builtin calls, by its name without `bpf_`;
the number is the kernel side of the interface's. The scope declarations are
kfuncs, encoded by the name their resource declaration gives. -/
def Builtin.helper : Builtin → Option String
  | .lookup => some "map_lookup_elem"
  | .update => some "map_update_elem"
  | .delete => some "map_delete_elem"
  | .reserve _ => some "ringbuf_reserve"
  | .submit => some "ringbuf_submit"
  | .discard => some "ringbuf_discard"
  | .lock => some "spin_lock"
  | .unlock => some "spin_unlock"
  | .printk .. => some "trace_printk"
  | .enter _ | .leave _ => none

def Builtin.print : Builtin → String
  | .lookup => "lookup"
  | .update => "update"
  | .delete => "delete"
  | .reserve n => s!"reserve {n}"
  | .submit => "submit"
  | .discard => "discard"
  | .lock => "lock"
  | .unlock => "unlock"
  | .enter r => s!"enter {r}"
  | .leave r => s!"leave {r}"
  | .printk fmt n size => s!"printk {Core.strLit fmt} {n} {size}"

def Callee.print : Callee → String
  | .builtin b => b.print
  | .kernel decl => decl

/-- The registers an instruction reads, a call its explicit operands;
under the fixed convention the well-formedness check adds the
argument registers the callee's arity selects. -/
def Instr.reads : Instr ρ τ → List ρ
  | .alu _ _ d s => d :: srcRegs s
  | .mov _ _ s => srcRegs s
  | .movsx _ _ _ s => [s]
  | .«end» _ _ d => [d]
  | .ldx _ _ s _ => [s]
  | .stx _ d _ s => d :: srcRegs s
  | .jcond _ _ a b _ => a :: srcRegs b
  | .call _ args _ => args
  | .atomic _ _ _ d _ s => [d, s]
  | _ => []
where
  srcRegs : Src ρ → List ρ
    | .reg r => [r]
    | .imm _ => []

/-- The register an instruction writes, if any; a call's result
register is the convention's. -/
def Instr.writes : Instr ρ τ → Option ρ
  | .alu _ _ d _ | .mov _ d _ | .movsx _ _ d _ | .«end» _ _ d | .ldx _ d _ _
  | .lddw d _ | .lea d _ | .mapref d _ | .mapval d _ _ => some d
  | .call _ _ dst => dst
  | .atomic _ _ true _ _ s => some s
  | _ => none

end Koit.BPF
