import Koit.Facts.Facts

/-!
An emitter of entailments as solver queries, for the testing
cross-check: every entailment the procedure accepts can be handed to
a bit-vector solver, which must find the facts together with the
negated predicate unsatisfiable. The type system never calls a
solver; this file only writes text.
-/

namespace Koit.Facts.Smt

open Koit.Core

/-- The name of a place as a solver constant. -/
def atomName (p : Place) : String := "|" ++ p.print ++ "|"

/-- The integer type of an expression when one of its operands fixes
it; a literal or a constant alone has none. -/
partial def typeOf (sc : Scope) : Expr → Option (Bool × Nat)
  | .char .. => some (false, 8)
  | .var s x =>
    match sc.place (.var s x) with
    | some (_, .int sg w) => some (sg, w)
    | _ => none
  | .read _ p =>
    match sc.place p with
    | some (_, .int sg w) => some (sg, w)
    | _ => none
  | .arith _ _ l r => typeOf sc l <|> typeOf sc r
  | .cast _ _ t =>
    match sc.sort t with
    | some (.int sg w) => some (sg, w)
    | _ => none
  | _ => none

/-- A bit-vector literal of the width. -/
def litTerm (w : Nat) (v : Int) : String :=
  if v ≥ 0 then s!"(_ bv{v} {w})" else s!"(bvneg (_ bv{-v} {w}))"

mutual

/-- An integer term at the type, when the expression translates. -/
partial def intTerm (sc : Scope) (sg : Bool) (w : Nat) : Expr → Option String
  | .lit _ v _ => some (litTerm w v)
  | .char _ c => if w == 8 then some (litTerm 8 c.toNat) else none
  | .size _ t => (sc.size t).map fun n => litTerm w n
  | .var s x =>
    match sc.place (.var s x) with
    | some (_, .int sg' w') =>
      if sg == sg' && w == w' then some (atomName (.var s x)) else none
    | some _ => none
    | none => (sc.const x).map (litTerm w)
  | .read _ p =>
    match sc.place p with
    | some (_, .int sg' w') =>
      if sg == sg' && w == w' then some (atomName p) else none
    | _ => none
  | .arith _ op l r => do
    let a ← intTerm sc sg w l
    let b ← intTerm sc sg w r
    let zero := litTerm w 0
    let mask := litTerm w (w - 1)
    some <| match op with
      | .add => s!"(bvadd {a} {b})"
      | .sub => s!"(bvsub {a} {b})"
      | .mul => s!"(bvmul {a} {b})"
      | .div =>
        if sg then s!"(ite (= {b} {zero}) {zero} (bvsdiv {a} {b}))"
        else s!"(ite (= {b} {zero}) {zero} (bvudiv {a} {b}))"
      | .mod =>
        if sg then s!"(ite (= {b} {zero}) {a} (bvsrem {a} {b}))"
        else s!"(ite (= {b} {zero}) {a} (bvurem {a} {b}))"
      | .band => s!"(bvand {a} {b})"
      | .bor => s!"(bvor {a} {b})"
      | .bxor => s!"(bvxor {a} {b})"
      | .shl => s!"(bvshl {a} (bvand {b} {mask}))"
      | .shr =>
        if sg then s!"(bvashr {a} (bvand {b} {mask}))"
        else s!"(bvlshr {a} (bvand {b} {mask}))"
  | .cast _ e t => do
    let some (.int sg' w') := sc.sort t | none
    unless sg == sg' && w == w' do none
    match typeOf sc e with
    | some (sge, we) =>
      let a ← intTerm sc sge we e
      if w < we then some s!"((_ extract {w - 1} 0) {a})"
      else if w > we then
        if sge then some s!"((_ sign_extend {w - we}) {a})"
        else some s!"((_ zero_extend {w - we}) {a})"
      else some a
    | none =>
      match e with
      | .bool .. | .cmp .. | .not .. | .and .. | .or .. => do
        let b ← boolTerm sc e
        some s!"(ite {b} {litTerm w 1} {litTerm w 0})"
      | _ => intTerm sc sg w e
  | _ => none

/-- A boolean term. -/
partial def boolTerm (sc : Scope) : Expr → Option String
  | .bool _ b => some (if b then "true" else "false")
  | .var s x =>
    match sc.place (.var s x) with
    | some (_, .bool) => some (atomName (.var s x))
    | _ => none
  | .read _ p =>
    match sc.place p with
    | some (_, .bool) => some (atomName p)
    | _ => none
  | .cmp _ op l r => do
    let (sg, w) := (typeOf sc l <|> typeOf sc r).getD (false, 64)
    let a ← intTerm sc sg w l
    let b ← intTerm sc sg w r
    some <| match op with
      | .eq => s!"(= {a} {b})"
      | .ne => s!"(distinct {a} {b})"
      | .lt => if sg then s!"(bvslt {a} {b})" else s!"(bvult {a} {b})"
      | .le => if sg then s!"(bvsle {a} {b})" else s!"(bvule {a} {b})"
      | .gt => if sg then s!"(bvsgt {a} {b})" else s!"(bvugt {a} {b})"
      | .ge => if sg then s!"(bvsge {a} {b})" else s!"(bvuge {a} {b})"
  | .not _ e => do some s!"(not {← boolTerm sc e})"
  | .and _ l r => do some s!"(and {← boolTerm sc l} {← boolTerm sc r})"
  | .or _ l r => do some s!"(or {← boolTerm sc l} {← boolTerm sc r})"
  | _ => none

end

/-- The declaration of a place's constant, if the place is one the
domain computes with. -/
def declare (sc : Scope) (p : Place) : Option String :=
  match sc.place p with
  | some (_, .int _ w) => some s!"(declare-const {atomName p} (_ BitVec {w}))"
  | some (_, .bool) => some s!"(declare-const {atomName p} Bool)"
  | _ => none

/-- The query for `F |= P`: the facts asserted, `P` denied, and
`check-sat`, which must answer `unsat`. A fact outside the fragment
is left as a comment, and so is `P` when it cannot be stated. -/
def query (sc : Scope) (F : Facts) (P : Expr) : String :=
  let atoms := (F.facts.flatMap Fact.atoms ++ P.atoms).foldl
    (fun acc p => if hasPlace acc p then acc else acc ++ [p]) []
  let decls := atoms.filterMap (declare sc)
  let asserts := F.facts.map fun
    | .pred e => match boolTerm sc e with
      | some t => s!"(assert {t})"
      | none => s!"; fact outside the fragment: {e.print}"
    | .off h e => s!"; off({h}) = {e.print}"
  let goal := match boolTerm sc P with
    | some t => s!"(assert (not {t}))"
    | none => s!"; demand outside the fragment: {P.print}"
  "\n".intercalate (["(set-logic QF_BV)"] ++ decls ++ asserts ++
    [goal, "(check-sat)"])

end Koit.Facts.Smt
