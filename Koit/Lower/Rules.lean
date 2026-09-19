import Koit.Lower.Lower
import Koit.Lower.Inline
import Koit.Lower.LIRInterp

/-!
The theorems of the lowering, stated: what each pass preserves, the
relations they are stated under, and the lemmas pass B leans on. The
compiler's correctness is a forward simulation per pass under a
relation that refines `Agree`, the equality of the shared state,
and the passes compose by relational composition. The proofs come
after the design settles, by fragment, the picker first; every
statement here compiles with `sorry`.
-/

namespace Koit.Lower

open Koit.Core
open Koit.Sem (State Val Loc Binding HeldRes Kernel KernelOk Initial)
open Koit.Check (Env Ctx Local Checked UnitOk Synth StmtOk)

/-! ### The relations -/

/-- The held stack read as its rows and objects, names dropped. -/
def heldView (h : List HeldRes) : List (Resource × Option (Sem.Region × Nat)) :=
  h.map fun e => (e.row.res, e.obj.map fun l => (l.region, l.off))

/-- `Agree st m`: the shared parts of two states are equal, the
maps, the packet and its token, the kernel objects, the trace, and
the held stack read as rows and objects; locals are not mentioned. -/
def Agree (a b : State) : Prop :=
  a.maps.map (fun (n, ms) => (n, ms.slots, ms.entries, ms.ring)) =
    b.maps.map (fun (n, ms) => (n, ms.slots, ms.entries, ms.ring)) ∧
  a.packet = b.packet ∧ a.layout = b.layout ∧
  a.kernelObjs = b.kernelObjs ∧ a.ctx = b.ctx ∧
  heldView a.held = heldView b.held ∧
  a.trace.length = b.trace.length ∧
  (a.trace.zip b.trace).all (fun (e, e') => (repr e).pretty == (repr e').pretty) = true

/-- The LIR value of a Core binding under `Γ`: a scalar fitted to its
type, a place as its location with its token. -/
def lirValueOf (t : Ty) (b : Binding) : Option Val :=
  match t, b with
  | .ref .., .place l | .view .., .place l | .own .., .place l => some (.loc l)
  | _, .val (.int s w v _) => some (Val.mkInt s w v)
  | _, .val (.be w v) => some (Val.mkInt false w v)
  | _, .val (.bool bv) => some (Val.mkInt false 8 (if bv then 1 else 0))
  | _, _ => none

/-- `R_B st_C st_L`: `Agree` on the shared parts and, for every Core
name in scope with its type in `Γ` and its LIR name in the renaming,
a scalar bound to `v` in Core is bound to `fit(T, v)` in LIR and a
place is bound to its location; a moved name is unbound in LIR. The
names LIR introduces are unconstrained. -/
def R_B (Γ : List Local) (names : List (String × String)) (stC stL : State) : Prop :=
  Agree stC stL ∧
  ∀ l ∈ Γ, ∀ b, stC.local? l.name = some b →
    match b, names.lookup l.name with
    | .moved, some x' => stL.local? x' = none
    | b, some x' => ∃ v, lirValueOf l.ty b = some v ∧ stL.local? x' = some (.val v)
    | _, none => False

/-- The LIR initial state of a Core initial state: the same shared
state and an empty frame. -/
def initB (st : State) : State := { st with locals := [] }

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
    ∀ st v st', Initial pre u p st →
      Sem.ExecProgram K st p (.halt v) st' →
      ∃ stL', LIR.ExecProgram K (loweredFns pre u checked) (initB st) P (.halt v) stL' ∧
              Agree st' stL' := by
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
    (∃ x poly, v = .int s w x poly ∧ Sem.wrap s w x = x) := by
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
the statement reads as Core's after `releaseRes`. Stated as the
`hold` case of the statement-level form of Theorem B on the held
stacks alone. -/
theorem hold_releases (pre : Prelude) (u : CompUnit) (checked : Checked) (K : Kernel)
    (c : LCtx) (sp : Koit.Span) (r : Resource) (x : Option String) (acq : Fallible)
    (body : List Stmt) (els : Option (List Stmt)) (ss : List LIR.Stmt) (c' : LCtx)
    (st st' stL : State) (o : Sem.Outcome) (oL : LIR.Outcome) (stL' : State) :
    KernelOk K → Check.checkUnit pre u = .ok checked →
    runLM (lowerHold c sp r x acq body els) = .ok (ss, c') →
    Agree st stL →
    Sem.ExecStmt K st (.hold sp r x acq body els) o st' →
    LIR.ExecStmts K (loweredFns pre u checked) stL ss oL stL' →
    (∀ m, o ≠ .err m) → (∀ m, oL ≠ .err m) →
    heldView st'.held = heldView stL'.held := by
  sorry

/-! ### Theorem I -/

/-- Theorem I, `inline_correct`: a run of a program of a well-formed
LIR unit is a run of its inlined form to the same verdict, with the
shared state agreeing; the locals of the inlined copies are fresh. -/
theorem inline_correct (pre : Prelude) (U : LIR.CompUnit) (K : Kernel) :
    LIR.wf pre U = .ok () →
    ∀ P ∈ U.programs, ∀ P', (inline U).programs.find? (·.name == P.name) = some P' →
    ∀ st v st', LIR.ExecProgram K U.fns st P (.halt v) st' →
      ∃ st'', LIR.ExecProgram K [] st P' (.halt v) st'' ∧ Agree st' st'' := by
  sorry

end Koit.Lower
