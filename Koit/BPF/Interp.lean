import Koit.BPF.Semantics

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
    match halted? X m with
    | some v => .ok { verdict := v, state := m }
    | none =>
      match step X K m with
      | .ok m' => run X K m' fuel
      | .error c => .error { cause := c, pc := m.pc }

/-- The run agrees with the relation: a halt it reaches is a `Star`
to a halted state. Stated now, proved after the design settles. -/
theorem run_sound (X : Env ρ τ) (K : Kernel) (m : State ρ) (fuel : Nat) (h : Halt ρ) :
    run X K m fuel = .ok h → Star X K m h.state ∧ Halted X h.state h.verdict := by
  sorry

end Koit.BPF
