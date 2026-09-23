import Koit.BPF.Semantics
import Koit.Core.Interp

/-!
The executable form of the machine: `step` iterated under a fuel
bound from a loaded state to a halted one, answering with the
verdict and the final state, or with the cause of the refusal and
the instruction it was refused at. `koitc run --bir` and `--bytecode`
run this on the flattened and the allocated program and compare its
verdict, maps, packet, and trace with the levels above.
-/

namespace Koit.BPF

open Koit.Machine (Kernel)

variable {ρ τ : Type} [DecidableEq ρ]

/-- Where a run stopped short of halting: the cause and the `pc`. -/
structure Refusal where
  cause : Cause
  pc    : Nat
  deriving Repr

def Refusal.describe (r : Refusal) : String :=
  s!"at instruction {r.pc}: {r.cause.describe}"

/-- A halted run: the verdict at the kind's width and the state. -/
structure Halt (ρ : Type) where
  verdict : Nat
  state   : State ρ

/-- The run from `m`: `step` until halted, refused, or out of fuel. -/
def run (X : Env ρ τ) (K : Kernel) (m : State ρ) : Nat → Except Refusal (Halt ρ)
  | 0 => .error { cause := .malformed "out of fuel", pc := m.pc }
  | fuel + 1 =>
    -- a taken tail call ends this program; the driver runs the entry
    if m.machine.tailTo.isSome then .ok { verdict := 0, state := m } else
    match halted? X m with
    | some v => .ok { verdict := v, state := m }
    | none =>
      match step X K m with
      | .ok m' => run X K m' fuel
      | .error c => .error { cause := c, pc := m.pc }

/-- A unit's programs run in order over one map state on the machine,
each from its own environment, reporting as Core's `runUnit` does so
that the runner compares the levels line by line. -/
def runUnit (pre : Interface) (core : Core.CompUnit) (progs : List (Env ρ τ))
    (packet : ByteArray) (ctx : List (String × Nat)) (only : Option String) (fuel : Nat) :
    Except String (List Core.Sem.Report × List String) := do
  let env : Check.Env := { interface := pre, license := core.license.map (·.2),
                           types := core.types, consts := core.consts,
                           configs := core.configs, maps := core.maps, fns := core.fns,
                           contracts := core.contracts }
  let mut maps ← Core.Sem.initMaps env core
  let mut reports : List Core.Sem.Report := []
  for X in progs do
    if only.isSome && only != some X.prog.name then continue
    let st : Machine.State := { maps, packet }
    let mut Y := X
    let mut h ← match run X Machine.synthetic (load X st ctx) fuel with
      | .ok h0 => pure h0
      | .error r => throw s!"`{X.prog.name}` {r.describe}"
    -- a taken tail call: the entry runs on the same machine state
    let mut hops := 0
    while h.state.machine.tailTo.isSome && hops ≤ Machine.maxTailCalls do
      let some name := h.state.machine.tailTo | break
      let some Z := progs.find? (·.prog.name == name) | throw s!"no program `{name}`"
      let mach := { h.state.machine with tailTo := none }
      h ← match run Z Machine.synthetic (load Z mach ctx) fuel with
        | .ok h1 => pure h1
        | .error r => throw s!"`{Z.prog.name}` {r.describe}"
      Y := Z
      hops := hops + 1
    maps := h.state.machine.maps
    let (s, w) := match Y.kind.verdictTy with
      | .int _ s w => (s, w)
      | _ => (false, 32)
    reports := reports ++ [{ program := X.prog.name,
                             verdict := Core.Sem.verdictName Y.kind
                               (Core.Sem.Val.mkInt s w h.verdict),
                             log := h.state.machine.log }]
  return (reports, Core.Sem.printMaps env maps)

/-- The run agrees with the relation: a halt it reaches is a `Star`
to a halted state. Stated now, proved after the design settles. -/
theorem run_sound (X : Env ρ τ) (K : Kernel) (m : State ρ) (fuel : Nat) (h : Halt ρ) :
    run X K m fuel = .ok h → Star X K m h.state ∧ Halted X h.state h.verdict := by
  sorry

end Koit.BPF
