import Koit.BPF.Print
import Koit.BPF.Semantics

/-!
Well-formedness of a program of the instruction set, which the
flattening guarantees and the allocation assumes: every label is
defined once and every jump targets a label or an instruction; `lea`
names a declared object and appears only where the convention admits
it; the designated context and frame registers are never written;
the code ends in `exit` or a jump, never by falling off; and every
register is written before it is read on every path, which is a
forward must-be-initialized analysis over the control flow, the
`let` discipline of LIR carried down.
-/

namespace Koit.BPF

variable {ρ τ : Type} [DecidableEq ρ]

abbrev W := Except String

def wfErr (msg : String) : W α := throw msg

/-- The successors of the instruction at `i`. -/
def successors (X : Env ρ τ) (i : Nat) : W (List Nat) := do
  let some ins := X.prog.code[i]? | wfErr s!"no instruction at {i}"
  let target (t : τ) : W Nat :=
    match X.conv.resolve X.prog.labels i t with
    | some j => if j < X.prog.code.size then pure j else wfErr s!"a jump at {i} leaves the code"
    | none => wfErr s!"a jump at {i} to a label the program does not define"
  match ins with
  | .exit => return []
  | .ja t => return [← target t]
  | .jcond _ _ _ _ t =>
    let fall := i + 1
    unless fall < X.prog.code.size do wfErr s!"the code falls off its end after {i}"
    return [← target t, fall]
  | _ =>
    unless i + 1 < X.prog.code.size do wfErr s!"the code falls off its end after {i}"
    return [i + 1]

/-- The registers an instruction reads under the convention, with a
call reading the fixed argument registers its callee's arity
selects, and `cmpxchg` the result register. -/
def readsOf (X : Env ρ τ) (ins : Instr ρ τ) : List ρ :=
  match ins, X.conv.fixedCall with
  | .call h _ _, some (regs, _) =>
    match layout X h with
    | .ok abi => regs.take abi.length
    | .error _ => []
  | .atomic .cmpxchg _ _ d _ s, _ => [d, s, X.conv.ret]
  | ins, _ => ins.reads

/-- The registers an instruction writes, and those it leaves
uninitialized, under the convention. -/
def writesOf (X : Env ρ τ) (ins : Instr ρ τ) : List ρ × List ρ :=
  match ins, X.conv.fixedCall with
  | .call .., some (_, dead) => ([X.conv.ret], dead)
  | .call _ _ dst, none => (dst.toList, [])
  | .atomic .cmpxchg .., _ => ([X.conv.ret], [])
  | ins, _ => (ins.writes.toList, [])

/-- The must-be-initialized analysis: at entry the context and frame
registers; through an instruction, its writes added and its dead
registers removed; at a join, the intersection. A read outside the
set is an error naming the instruction. -/
def checkInit (X : Env ρ τ) : W Unit := do
  let n := X.prog.code.size
  let entry : List ρ := [X.conv.ctx, X.conv.fp]
  -- the set at the entry of each instruction, none until reached
  let mut sets : Array (Option (List ρ)) := Array.replicate n none
  sets := sets.set! 0 (some entry)
  let mut changed := true
  let mut rounds := 0
  while changed && rounds ≤ n + 1 do
    changed := false
    rounds := rounds + 1
    for i in [0:n] do
      if let some s := sets[i]! then
        let ins := X.prog.code[i]!
        let (ws, dead) := writesOf X ins
        let out := (s ++ ws).filter (fun r => !dead.contains r)
        for j in ← successors X i do
          let merged := match sets[j]! with
            | none => out
            | some t => t.filter out.contains
          match sets[j]! with
          | some t => if t.length != merged.length then changed := true
          | none => changed := true
          sets := sets.set! j (some merged)
  for i in [0:n] do
    if let some s := sets[i]! then
      let ins := X.prog.code[i]!
      for r in readsOf X ins do
        unless s.contains r do
          wfErr s!"instruction {i} reads {X.conv.name r}, which may be uninitialized"

/-- A program is well-formed under its environment. -/
def wf (X : Env ρ τ) : W Unit := do
  let p := X.prog
  if p.code.isEmpty then wfErr "an empty program"
  -- labels defined once, at instructions
  for (l, at_) in p.labels do
    unless at_ < p.code.size do wfErr s!"label {l} is outside the code"
    if (p.labels.filter (·.1 == l)).length > 1 then wfErr s!"label {l} is defined twice"
  for i in [0:p.code.size] do
    let ins := p.code[i]!
    let _ ← successors X i
    match ins with
    | .lea _ obj =>
      unless X.conv.lea do wfErr s!"instruction {i}: `lea` under a convention without it"
      unless p.objects.any (·.name == obj) do
        wfErr s!"instruction {i}: no frame object `{obj}`"
    | .call h args dst =>
      match X.conv.fixedCall with
      | some _ =>
        unless args.isEmpty && dst.isNone do
          wfErr s!"instruction {i}: a call with operands under the fixed convention"
      | none =>
        let n ← arity X h |>.mapError (·.describe)
        unless args.length == n do
          wfErr s!"instruction {i}: `{h.print}` takes {n} operands, {args.length} given"
    | _ => pure ()
    let (ws, _) := writesOf X ins
    for r in X.conv.pinned do
      if ws.contains r then wfErr s!"instruction {i} writes {X.conv.name r}, which is read-only"
  -- objects in the frame, 8-aligned, disjoint
  for o in p.objects do
    unless o.base % 8 == 0 && o.base < 0 && o.base + o.size ≤ 0 && -512 ≤ o.base do
      wfErr s!"frame object `{o.name}` at {o.base} of {o.size} bytes is not in the frame"
    for o' in p.objects do
      if o.name != o'.name && o.base < o'.base + o'.size && o'.base < o.base + o.size then
        wfErr s!"frame objects `{o.name}` and `{o'.name}` overlap"
  checkInit X

end Koit.BPF
