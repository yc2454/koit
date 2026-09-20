import Koit.Compile.Lower
import Koit.Compile.Inline
import Koit.Compile.Flatten
import Koit.LIR.Interp

/-!
The theorems of the lowering, stated: what each pass preserves, the
relations they are stated under, and the lemmas pass B leans on. The
compiler's correctness is a forward simulation per pass under a
relation that refines `Agree`, the equality of the shared state,
and the passes compose by relational composition. The proofs come
after the design settles, by fragment, the picker first; every
statement here compiles with `sorry`.
-/

namespace Koit.Compile

open Koit.Core
open Koit.Core.Sem (State Val Loc Binding)
open Koit.Machine (Kernel KernelOk)
open Koit.Check (Env Ctx Local Checked UnitOk Synth StmtOk)

/-! ### The relations -/

/-- `Agree`: the shared states of two levels are equal, one equality
of one structure, the maps, the packet and its token, the kernel
objects, the held stack as rows and objects, and the trace; the
levels' private halves, locals and registers, are not mentioned. -/
def Agree (a b : Machine.State) : Prop := a = b

/-- The LIR value of a Core binding under `Γ`: a scalar fitted to its
type, a place as its location with its token. -/
def lirValueOf (t : Ty) (b : Binding) : Option Val :=
  match t, b with
  | .ref .., .place l | .view .., .place l | .own .., .place l => some (.loc l)
  | _, .val (.int s w v _) => some (Val.mkInt s w v)
  | _, .val (.be w v) => some (Val.mkInt false w v)
  | _, .val (.bool bv) => some (Val.mkInt false 8 (if bv then 1 else 0))
  | _, _ => none

/-- `R_B st_C st_L`: `Agree` on the shared states and, for every Core
name in scope with its type in `Γ` and its LIR name in the renaming,
a scalar bound to `v` in Core is bound to `fit(T, v)` in LIR and a
place is bound to its location; a moved name is unbound in LIR. The
names LIR introduces are unconstrained. -/
def R_B (Γ : List Local) (names : List (String × String)) (stC : State)
    (stL : LIR.Sem.State) : Prop :=
  Agree stC.machine stL.machine ∧
  ∀ l ∈ Γ, ∀ b, stC.local? l.name = some b →
    match b, names.lookup l.name with
    | .moved, some x' => stL.local? x' = none
    | b, some x' => ∃ v, lirValueOf l.ty b = some v ∧ stL.local? x' = some v
    | _, none => False

/-! ### Theorem B -/

/-- The LIR program a Core program lowers to, in the lowered unit. -/
def lowered (pre : Prelude) (u : CompUnit) (checked : Checked) (p : Program) :
    Option LIR.Program :=
  match lower pre (fold pre u checked) with
  | .ok U => U.programs.find? (·.name == p.name)
  | .error _ => none

def loweredFns (pre : Prelude) (u : CompUnit) (checked : Checked) : List LIR.Fn :=
  match lower pre (fold pre u checked) with
  | .ok U => U.fns
  | .error _ => []

/-- Theorem B, `lower_correct`: for a kernel within its contracts and
a unit the checker accepts, every halting run of a program is
matched by a run of its lowering to the same verdict, with the
shared state agreeing at the halt. Every test Core has, the lowering
emits; the one branch it adds is dead under the Core derivation. -/
theorem lower_correct (pre : Prelude) (u : CompUnit) (checked : Checked) (K : Kernel) :
    KernelOk K → Check.checkUnit pre u = .ok checked →
    ∀ p ∈ u.programs, ∀ P, lowered pre u checked p = some P →
    ∀ st v st', Sem.Initial pre u p st →
      Sem.ExecProgram K st p (.halt v) st' →
      ∃ stL', LIR.Sem.ExecProgram K (loweredFns pre u checked) (LIR.Sem.ofCore st) P
                (.halt v) stL' ∧
              Agree st'.machine stL'.machine := by
  sorry

/-! ### The lemmas pass B leans on -/

/-- A state typed by the environment: every local in scope is bound
to a value of its type. -/
def StateTyped (env : Env) (st : State) : Prop :=
  ∀ l ∈ env.locals, ∃ b, st.local? l.name = some b ∧ (lirValueOf l.ty b).isSome

/-- Lemma W, widths: in a run of a well-typed program, an expression
the checker gives type `int(s,w)` evaluates to an integer that
`fit(int(s,w), ·)` leaves unchanged, and a polymorphic literal meets
an operand of that type. This is the preservation half of T1 for
expressions, stated separately so that B can cite it: the dynamic
meeting of widths in Core and the static widths in LIR agree. -/
theorem width_preservation (env : Env) (K : Ctx) (e : Expr) (t : Ty) (s : Bool) (w : Nat)
    (Kr : Kernel) (st : State) (v : Val) (st' : State) :
    Synth env K e t → env.norm t = .ok (.int t.span s w) → StateTyped env st →
    Sem.EvalExpr Kr st e (.ok v) st' →
    (∃ x poly, v = .int s w x poly ∧ Machine.wrap s w x = x) := by
  sorry

/-- The owned names a state marks moved. -/
def movedIn (st : State) : List String :=
  st.locals.filterMap fun (x, b) => match b with
    | .moved => some x
    | _ => none

/-- Lemma M, moves: in a well-typed program the set of owned names
moved on a path is a function of the program point. The join rule of
`move` and the loop rule, restated as a semantic invariant: after a
statement the checker accepts under facts whose moved set is the
state's, the state's moved set is the one the checker computed. It
is why the release code at each exit is static. -/
theorem moves_static (env : Env) (K : Ctx) (s : Stmt) (env' : Env) (F' : Koit.Facts.Facts)
    (ns : List String) (E : Koit.Effects.Effs) (Kr : Kernel) (st st' : State) :
    StmtOk env K s env' F' ns E → StateTyped env st →
    (movedIn st).eraseDups = (K.facts.moved.map (·.1)).eraseDups →
    Sem.ExecStmt Kr st s .normal st' →
    (movedIn st').eraseDups = (F'.moved.map (·.1)).eraseDups := by
  sorry

/-- Lemma H, releases: the lowered `hold` releases exactly as Core
does. For a `hold` statement whose lowering runs from a related
state: on the normal outcome the normal release has run once, on
every other outcome the abnormal release has run once, and on a
path through `move x` neither has, so that the LIR held stack after
the statement is Core's. Stated as the `hold` case of the
statement-level form of Theorem B on the held stacks alone. -/
theorem hold_releases (pre : Prelude) (u : CompUnit) (checked : Checked) (K : Kernel)
    (c : LCtx) (sp : Koit.Span) (r : Resource) (x : Option String) (acq : Fallible)
    (body : List Stmt) (els : Option (List Stmt)) (ss : List LIR.Stmt) (c' : LCtx)
    (st st' : State) (stL : LIR.Sem.State) (o : Sem.Outcome) (oL : LIR.Sem.Outcome)
    (stL' : LIR.Sem.State) :
    KernelOk K → Check.checkUnit pre u = .ok checked →
    runLM (lowerHold c sp r x acq body els) = .ok (ss, c') →
    Agree st.machine stL.machine →
    Sem.ExecStmt K st (.hold sp r x acq body els) o st' →
    LIR.Sem.ExecStmts K (loweredFns pre u checked) stL ss oL stL' →
    (∀ m, o ≠ .err m) → (∀ m, oL ≠ .err m) →
    st'.held = stL'.held := by
  sorry

/-! ### Theorem I -/

/-- Theorem I, `inline_correct`: a run of a program of a well-formed
LIR unit is a run of its inlined form to the same verdict, with the
shared state agreeing; the locals of the inlined copies are fresh. -/
theorem inline_correct (pre : Prelude) (U : LIR.CompUnit) (K : Kernel) :
    LIR.wf pre U = .ok () →
    ∀ P ∈ U.programs, ∀ P', (inline U).programs.find? (·.name == P.name) = some P' →
    ∀ st v st', LIR.Sem.ExecProgram K U.fns st P (.halt v) st' →
      ∃ st'', LIR.Sem.ExecProgram K [] st P' (.halt v) st'' ∧
              Agree st'.machine st''.machine := by
  sorry

/-! ### Theorem C -/

/-- The verdict pattern of a Core value at its width, what the
machine halts with. -/
def verdictPattern : Val → Nat
  | .int _ w x _ => Machine.toNatMod x w
  | .be w x => Machine.toNatMod x w
  | .bool b => if b then 1 else 0
  | .loc _ => 0

/-- The context values of an LIR state, as the machine loads them. -/
def ctxValues (st : LIR.Sem.State) : List (String × Nat) :=
  st.ctx.map fun (f, v) => (f, verdictPattern v)

/-- Theorem C, `flatten_correct`: a halting run of a closed LIR
program is matched by a run of the machine on its flattening, from
the loaded state to a halted one with the same verdict, the shared
state agreeing. `R_C`, the relation the induction carries, holds the
locals in scope in their registers in normal form and LIR's stack
regions in the frame at the objects' bases. -/
theorem flatten_correct (pre : Prelude) (cpu : BPF.Cpu) (P : LIR.Program) (B : BPF.BIR)
    (K : Kernel) :
    flattenProgram pre cpu P = .ok B →
    ∀ st v st', LIR.Sem.ExecProgram K [] st P (.halt v) st' →
      ∀ X, birEnv pre st.env B = .ok X →
        ∃ m, BPF.Star X K (BPF.load X st.machine (ctxValues st)) m ∧
             BPF.Halted X m (verdictPattern v) ∧ Agree st'.machine m.machine := by
  sorry

end Koit.Compile
