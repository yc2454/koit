import Koit.Facts.Smt

/-!
The decision procedure for `F |= P`, in two tiers: membership of `P`
among the facts, with names known equal substituted for each other,
and then forward interpretation of `P` in the state the facts build,
with the domain of `Domain.lean`. No solver. The procedure decides
what a verifier's own range and bit tracking re-derives from the
tests the program emits, so a demand it discharges can be left
without a runtime test; a demand it cannot discharge is an error the
programmer answers with a `check`, never a test inserted silently.

`entails_sound` states that the procedure decides a subset of the
semantic entailment of `Facts.lean`.
-/

namespace Koit.Facts

open Koit.Core

/-- The equality classes of atoms the facts state equal: `x == y`
between two places. Each class lists its members, the first the
representative. -/
def classes (F : Facts) : List (List Place) :=
  F.facts.foldl (fun cs f =>
    match f with
    | .pred (.cmp _ .eq a b) =>
      let isAtom : Expr → Bool
        | .var .. | .read .. => true
        | _ => false
      match a.atoms, b.atoms with
      | [p], [q] =>
        if !(isAtom a && isAtom b) then cs else
        let ci := cs.findIdx? (hasPlace · p)
        let cj := cs.findIdx? (hasPlace · q)
        match ci, cj with
        | some i, some j =>
          if i == j then cs
          else
            let merged := cs[i]! ++ cs[j]!
            (cs.eraseIdx j).set (if j < i then i - 1 else i) merged
        | some i, none => cs.set i (cs[i]! ++ [q])
        | none, some j => cs.set j (cs[j]! ++ [p])
        | none, none => cs ++ [[p, q]]
      | _, _ => cs
    | _ => cs) []

/-- The representative of an atom. -/
def rep (cs : List (List Place)) (p : Place) : Place :=
  match cs.find? (hasPlace · p) with
  | some (r :: _) => r
  | _ => p

mutual

/-- The expression with every atom replaced by its representative. -/
partial def canonExpr (cs : List (List Place)) : Expr → Expr
  | .var s x => match rep cs (.var s x) with
    | .var _ y => .var s y
    | p => .read s p
  | .read s p => match rep cs p with
    | .var _ y => .var s y
    | q => .read s (canonPlace cs q)
  | .arith s op l r => .arith s op (canonExpr cs l) (canonExpr cs r)
  | .cmp s op l r => .cmp s op (canonExpr cs l) (canonExpr cs r)
  | .not s e => .not s (canonExpr cs e)
  | .and s l r => .and s (canonExpr cs l) (canonExpr cs r)
  | .or s l r => .or s (canonExpr cs l) (canonExpr cs r)
  | .cast s e t => .cast s (canonExpr cs e) t
  | e => e

partial def canonPlace (cs : List (List Place)) : Place → Place
  | .field s p f => .field s (canonPlace cs p) f
  | .index s p i => .index s (canonPlace cs p) (canonExpr cs i)
  | .slot s m i => .slot s m (canonExpr cs i)
  | p => p

end

/-- Tier one: `P` is a fact, up to positions and equal names. -/
def member (F : Facts) (P : Expr) : Bool :=
  let cs := classes F
  let P' := canonExpr cs P
  F.facts.any fun
    | .pred e => Expr.same (canonExpr cs e) P'
    | .off .. => false

/-- Tier two: `P` evaluates to true in the state the facts build. -/
def evalTrue (sc : Scope) (F : Facts) (P : Expr) : Bool :=
  match eval sc (F.state sc) P with
  | .bool .yes => true
  | _ => false

/-- `F |= P`. On an exited path every demand holds. With `sc.smt`,
each accepted entailment is traced as a solver query. -/
def entails (sc : Scope) (F : Facts) (P : Expr) : Bool :=
  if F.bottom then true else
  let P := F.resolveExpr P
  let ok := member F P || evalTrue sc F P
  if ok && sc.smt then
    dbgTrace ("; koit entailment\n" ++ Smt.query sc F P ++ "\n") fun _ => ok
  else ok

/-- The one value `e` can have under the facts, if the state knows
it: for a message that names the constant instead of the formula. -/
def constOf (sc : Scope) (F : Facts) (e : Expr) : Option Int :=
  if F.bottom then none else
  (eval sc (F.state sc) (F.resolveExpr e)).const?

/-- The largest value `e` can have under the facts, for the cap of a
loop whose bound is `e`: `none` when the facts say nothing and the
type is the only bound. -/
def upperOf (sc : Scope) (F : Facts) (e : Expr) : Option Int :=
  if F.bottom then some 0 else
  match eval sc (F.state sc) (F.resolveExpr e) with
  | .int a => if a.isEmpty then some 0 else some a.hi
  | .poly v => some v
  | _ => none

/-- `F |= e in vals`: every value `e` can take under the facts is one
of `vals`. A verdict set is such a demand, and an interval inside the
set satisfies it where the disjunction of equalities would not
evaluate. -/
def entailsIn (sc : Scope) (F : Facts) (e : Expr) (vals : List Int) : Bool :=
  if F.bottom then true else
  match eval sc (F.state sc) (F.resolveExpr e) with
  | .poly v => vals.contains v
  | .int a =>
    if a.isEmpty then true
    else if a.hi - a.lo > 64 then false
    else (List.range (a.hi - a.lo + 1).toNat).all fun k =>
      let v := a.lo + k
      -- a value the known bits rule out need not be in the set
      (toBits a.w v ^^^ a.kv) &&& a.km != 0 || vals.contains v
  | _ => false

/-- Soundness of the procedure: what it accepts is entailed. Stated
now, proved after the corpus. -/
theorem entails_sound (sc : Scope) (F : Facts) (P : Expr) :
    entails sc F P = true → Entails sc F P := by
  sorry

end Koit.Facts
