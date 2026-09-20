import Koit.Compile.Flatten

/-!
Pass D, the naive allocation: BIR to bytecode. Every virtual register
lives in an 8-byte spill slot below the frame objects, except the
context, which is copied from `r1` into `r6` at entry and stays
there, and the frame pointer, which is `r10`. Each BIR instruction
becomes loads of its operands from their slots into `r1` to `r3`, the
instruction on those registers, and a store of the result to its
slot. A call takes the kernel's calling convention here: the
callee's argument layout says which register carries which koit
operand, the context, a constant, a place's size, or `printk`'s
format, and the allocation materializes each into `r1` to `r5`,
calls, and stores `r0`. The inline rows, which the kernel computes
without a call, become the kernel's own instruction sequences. `lea`
is `mov r1, r10; add r1, base`; the exit sequence loads `r0` from
the verdict's slot. Labels become signed offsets from the
instruction after the jump. The program is rejected with its frame
size when the objects and the slots exceed 512 bytes.

It is provable directly, one BIR step matched by a fixed sequence of
bytecode steps, and it is what the verifier sees from clang at low
optimization, so it is accepted; a linear-scan allocation over `r6`
to `r9` comes later as an untrusted pass with a verified checker.
Its theorem, `alloc_correct`, is stated in `Rules.lean`.
-/

namespace Koit.Compile

open Koit.BPF (Instr Src Cls VReg Label Reg BIR Bytecode Cpu)
open Koit.Interface (KindRow CallRow AbiArg)

/-- What the allocation yields: the bytecode, the slot of each
virtual register, and the bytecode index each BIR instruction starts
at, which the relation of `alloc_correct` speaks of. -/
structure Allocated where
  prog   : Bytecode
  slots  : List (VReg × Int)
  starts : Array Nat
  deriving Inhabited

/-- A jump target before resolution: a label of BIR, or an offset
inside one instruction's expansion. -/
inductive Target where
  | lbl (l : Label)
  | rel (off : Int)
  deriving Repr, Inhabited

/-- The virtual registers a program mentions, besides the context and
the frame pointer. -/
def vregsOf (p : BIR) : List VReg :=
  let fromCode := p.code.toList.flatMap fun ins =>
    ins.reads ++ ins.writes.toList ++ (match ins with
      | .call _ args dst => args ++ dst.toList
      | _ => [])
  let all := p.regs.map (·.1) ++ fromCode ++ [.ret, .reason]
  (all.filter fun r => r != .ctx && r != .fp).eraseDups

/-- The slot of a virtual register: below the objects, one per
register in order. -/
def slotTable (p : BIR) : List (VReg × Int) :=
  let bottom : Int := p.objects.foldl (fun acc o => min acc o.base) 0
  (vregsOf p).zipIdx.map fun (v, i) => (v, bottom - 8 * (i + 1))

/-- The scratch registers of an expansion. -/
def r0 : Reg := .r0
def r1 : Reg := .r1
def r2 : Reg := .r2
def r3 : Reg := .r3

/-- What an expansion reads: the slots, the program, the kind's row,
the interface, and the sizes of the types the kernel functions' memory
parameters name. -/
structure ACtx where
  slots  : List (VReg × Int)
  prog   : BIR
  kind   : KindRow
  pre    : Interface
  sizeOf : Core.Ty → Option Nat

abbrev AM := ReaderT ACtx (Except String)

abbrev Code := List (Instr Reg Target)

def slotOf (v : VReg) : AM Int := do
  match (← read).slots.lookup v with
  | some off => pure off
  | none => throw s!"no slot for {v.print}"

/-- The instructions that bring a virtual register's value into a
scratch register, or the fixed register it lives in. -/
def fetch (v : VReg) (scratch : Reg) : AM (Reg × Code) := do
  match v with
  | .ctx => return (.r6, [])
  | .fp => return (.r10, [])
  | v => return (scratch, [.ldx 64 scratch .r10 (← slotOf v)])

/-- A virtual register's value into exactly the register given. -/
def fetchInto (v : VReg) (target : Reg) : AM Code := do
  let (r, ls) ← fetch v target
  return ls ++ (if r == target then [] else [.mov .w64 target (.reg r)])

/-- A source operand: the immediate, or the register the virtual one
is brought into. -/
def fetchSrc (s : Src VReg) (scratch : Reg) : AM (Src Reg × Code) := do
  match s with
  | .imm k => return (.imm k, [])
  | .reg v =>
    let (r, is) ← fetch v scratch
    return (.reg r, is)

/-- The store of a scratch register into a virtual register's slot. -/
def spill (v : VReg) (r : Reg) : AM Code := do
  return [.stx 64 .r10 (← slotOf v) (.reg r)]

/-- A constant into a register: a 32-bit immediate sign-extended, or
`lddw`. -/
def constant (r : Reg) (k : Int) : Code :=
  if -2 ^ 31 ≤ k && k < 2 ^ 31 then [.mov .w64 r (.imm k)]
  else [.lddw r (Machine.toNatMod k 64)]

/-- The location of a frame object into a register. -/
def objectInto (r : Reg) (obj : String) : AM Code := do
  let some o := (← read).prog.objects.find? (·.name == obj) | throw s!"no frame object `{obj}`"
  return [.mov .w64 r (.reg .r10), .alu .add .w64 r (.imm o.base)]

/-- The argument register of the `j`-th position of a layout. -/
def argReg (j : Nat) : Reg := ⟨(j + 1) % 11, Nat.mod_lt _ (by decide)⟩

/-- The koit parameters of a callee, for the sizes a layout asks. -/
def paramsOf (h : BPF.Callee) : AM (List Core.Param) := do
  match h with
  | .kernel name =>
    match (← read).pre.call? name with
    | some { sig := .fn params _, .. } => pure params
    | _ => pure []
  | .builtin _ => pure []

/-- A call under the kernel's convention: each position of the
layout materialized in its register, the call, the result stored. -/
def expandCall (h : BPF.Callee) (abi : List AbiArg) (args : List VReg) (dst : Option VReg) :
    AM Code := do
  unless abi.length ≤ 5 do throw s!"`{h.print}` takes more than five kernel arguments"
  let params ← paramsOf h
  let mut loads : Code := []
  for (a, j) in abi.zipIdx do
    let target := argReg j
    match a with
    | .arg i =>
      let some v := args[i]? | throw s!"`{h.print}`: the layout names argument {i}"
      loads := loads ++ (← fetchInto v target)
    | .ctx => loads := loads ++ [.mov .w64 target (.reg .r6)]
    | .const k => loads := loads ++ constant target k
    | .argSize i =>
      let some p := params[i]? | throw s!"`{h.print}`: the layout sizes argument {i}"
      let pointee := match p.ty with
        | .ref _ t | .view _ t => t
        | t => t
      let some n := (← read).sizeOf pointee | throw s!"no layout for `{pointee.print}`"
      loads := loads ++ constant target n
    | .fmt =>
      match h with
      | .builtin (.printk _ _ obj _) => loads := loads ++ (← objectInto target obj)
      | _ => throw s!"`{h.print}`: the layout names a format"
  let store ← match dst with
    | some d => spill d r0
    | none => pure []
  return loads ++ [.call h [] none] ++ store

/-- The kernel's own instruction sequence for an inline row. -/
def expandInline (name : String) (args : List VReg) (dst : Option VReg) : AM Code := do
  let c ← read
  let store (r : Reg) : AM Code := match dst with
    | some d => spill d r
    | none => pure []
  match name, args with
  | "pkt.len", [] =>
    let some data := c.kind.ctxBounds.find? (!·.isEnd) | throw "the kind has no packet"
    let some dataEnd := c.kind.ctxBounds.find? (·.isEnd) | throw "the kind has no packet"
    return [.ldx 32 r1 .r6 data.offset, .ldx 32 r2 .r6 dataEnd.offset,
            .alu .sub .w64 r2 (.reg r1)] ++ (← store r2)
  | "csum_add", [csum, addend] =>
    -- the 32-bit sum with the end-around carry: `res + (res < addend)`
    return (← fetchInto csum r1) ++ (← fetchInto addend r2) ++
      [.alu .add .w32 r1 (.reg r2), .jcond .ge .w32 r1 (.reg r2) (.rel 1),
       .alu .add .w32 r1 (.imm 1)] ++ (← store r1)
  | "csum_fold", [csum] =>
    -- two folds of the high half into the low, then the complement
    let fold : Code := [.mov .w32 r2 (.reg r1), .alu .rsh .w32 r2 (.imm 16),
                        .alu .and .w32 r1 (.imm 0xffff), .alu .add .w32 r1 (.reg r2)]
    return (← fetchInto csum r1) ++ fold ++ fold ++
      [.alu .xor .w32 r1 (.imm 0xffff)] ++ (← store r1)
  | name, _ => throw s!"`{name}` has no inline sequence"

/-- One BIR instruction as bytecode, with the jumps still on BIR's
labels. -/
def expand (ins : Instr VReg Label) : AM Code := do
  match ins with
  | .alu op cls d s =>
    let (rd, ld) ← fetch d r1
    let (src, ls) ← fetchSrc s r2
    return ld ++ ls ++ [.alu op cls rd src] ++ (← spill d rd)
  | .mov cls d s =>
    let (src, ls) ← fetchSrc s r1
    -- a 64-bit move of a value just fetched into `r1` is the fetch
    let move : Code := match cls, src with
      | .w64, .reg r => if r == r1 then [] else [.mov .w64 r1 (.reg r)]
      | _, _ => [.mov cls r1 src]
    return ls ++ move ++ (← spill d r1)
  | .movsx cls w d s =>
    let (rs, ls) ← fetch s r1
    return ls ++ [.movsx cls w r1 rs] ++ (← spill d r1)
  | .«end» to w d =>
    let (rd, ld) ← fetch d r1
    return ld ++ [.«end» to w rd] ++ (← spill d rd)
  | .ldx w d s off =>
    let (rs, ls) ← fetch s r1
    return ls ++ [.ldx w r2 rs off] ++ (← spill d r2)
  | .stx w d off s =>
    let (rd, ld) ← fetch d r1
    let (src, ls) ← fetchSrc s r2
    return ld ++ ls ++ [.stx w rd off src]
  | .ja t => return [.ja (.lbl t)]
  | .jcond cmp cls a b t =>
    let (ra, la) ← fetch a r1
    let (src, lb) ← fetchSrc b r2
    return la ++ lb ++ [.jcond cmp cls ra src (.lbl t)]
  | .lddw d k => return [.lddw r1 k] ++ (← spill d r1)
  | .lea d obj => return (← objectInto r1 obj) ++ (← spill d r1)
  | .mapref d m => return [.mapref r1 m] ++ (← spill d r1)
  | .mapval d m k => return [.mapval r1 m k] ++ (← spill d r1)
  | .call h args dst =>
    let c ← read
    match h with
    | .kernel name =>
      let some row := c.pre.call? name | throw s!"unknown kernel function `{name}`"
      if row.isInline then expandInline name args dst
      else expandCall h (row.implIn c.kind.name).abi args dst
    | .builtin b => expandCall h b.abi args dst
  | .atomic op cls f d off s =>
    let (rd, ld) ← fetch d r1
    let (rs, ls) ← fetch s r2
    match op with
    | .cmpxchg =>
      let retSlot ← slotOf .ret
      let store ← spill .ret r0
      return ld ++ ls ++ [.ldx 64 r0 .r10 retSlot, .atomic op cls f rd off rs] ++ store
    | _ =>
      let store ← if f then spill s rs else pure []
      return ld ++ ls ++ [.atomic op cls f rd off rs] ++ store
  | .exit => return [.ldx 64 r0 .r10 (← slotOf .ret), .exit]

/-- Whether an offset fits the 16-bit field of a jump. -/
def fitsJump (off : Int) : Bool := -32768 ≤ off && off < 32768

/-- Pass D on one program. -/
def allocate (pre : Interface) (sizeOf : Core.Ty → Option Nat) (p : BIR) :
    Except String Allocated := do
  let some kind := pre.kind? p.kind | throw s!"unknown kind `{p.kind}`"
  let slots := slotTable p
  let bottom : Int := p.objects.foldl (fun acc o => min acc o.base) 0
  let frame := (-bottom).toNat + 8 * slots.length
  if frame > BPF.Frame.size then
    throw s!"the frame of `{p.name}` needs {frame} bytes, {(-bottom).toNat} of objects and \
      {slots.length} spill slots, above {BPF.Frame.size}"
  let ctx : ACtx := { slots, prog := p, kind, pre, sizeOf }
  -- the entry: the context into `r6`
  let mut code : Array (Instr Reg Target) := #[.mov .w64 .r6 (.reg .r1)]
  let mut starts : Array Nat := #[]
  for ins in p.code do
    starts := starts.push code.size
    let expanded ← (expand ins).run ctx |>.mapError (s!"in `{p.name}`: " ++ ·)
    code := code ++ expanded.toArray
  -- targets to offsets from the instruction after the jump
  let target (i : Nat) : Target → Except String Int
    | .rel off => pure off
    | .lbl l => do
      let some bi := p.labels.lookup l.id | throw s!"label {l.id} is not defined"
      let some t := starts[bi]? | throw s!"label {l.id} is outside the code"
      let off : Int := (t : Int) - ((i : Int) + 1)
      unless fitsJump off do
        throw s!"a jump of {off} instructions in `{p.name}` needs more than 16 bits"
      return off
  let mut out : Array (Instr Reg Int) := #[]
  for (ins, i) in code.toList.zipIdx do
    out := out.push (← match ins with
      | .ja t => do
        let off ← target i t
        pure (Instr.ja off)
      | .jcond cmp cls a b t => do
        let off ← target i t
        pure (Instr.jcond cmp cls a b off)
      | .alu op cls d s => pure (.alu op cls d s)
      | .mov cls d s => pure (.mov cls d s)
      | .movsx cls w d s => pure (.movsx cls w d s)
      | .«end» to w d => pure (.«end» to w d)
      | .ldx w d s off => pure (.ldx w d s off)
      | .stx w d off s => pure (.stx w d off s)
      | .lddw d k => pure (.lddw d k)
      | .lea d obj => pure (.lea d obj)
      | .mapref d m => pure (.mapref d m)
      | .mapval d m k => pure (.mapval d m k)
      | .call h args dst => pure (.call h args dst)
      | .atomic op cls fetch d off s => pure (.atomic op cls fetch d off s)
      | .exit => pure .exit)
  return { prog := { name := p.name, kind := p.kind, code := out, objects := p.objects,
                     cpu := p.cpu },
           slots, starts }

/-- Pass D on a unit's programs. -/
def allocateAll (pre : Interface) (sizeOf : Core.Ty → Option Nat) (ps : List BIR) :
    Except String (List Allocated) :=
  ps.mapM (allocate pre sizeOf)

/-- The machine's environment for a bytecode program. -/
def bytecodeEnv (pre : Interface) (env : Check.Env) (O : Bytecode) :
    Except String (BPF.Env Reg Int) := do
  let some kind := pre.kind? O.kind | throw s!"unknown kind `{O.kind}`"
  return { pre, kind, conv := BPF.bytecodeConv, prog := O,
           sizeOf := fun t => match env.layout t with
             | .ok (n, _) => some n
             | .error _ => none }

end Koit.Compile
