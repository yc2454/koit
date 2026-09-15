import Koit.Facts.Entail

/-!
Checks on the abstract domain and on the facts: the transfer
functions that must be exact, the join, the narrowing at a
comparison, and the fact operations `kill`, `meet`, `assume`, and
`record` over a small scope of stack locals.
-/

open Koit Koit.Core Koit.Facts

private def sp : Span := noSpan
private def u32 : Abs := Abs.top false 32
private def c32 (v : Int) : Abs := Abs.const false 32 v
private def range (lo hi : Int) : Abs := Abs.reduce { u32 with lo, hi }

-- exact `%` and `/` by a constant, `&` by a mask
#guard (u32.mod (c32 16)).lo == 0 && (u32.mod (c32 16)).hi == 15
#guard (u32.mod (c32 16)).km == (0xFFFFFFFF ^^^ 15)
#guard ((range 0 7).mod (c32 16)) == range 0 7
#guard (u32.mod (c32 0)) == u32
#guard ((range 0 100).div (c32 10)).hi == 10
#guard (u32.band (c32 0xF0)).hi == 0xF0
#guard (u32.band (c32 0xF0)).km == (0xFFFFFFFF ^^^ 0xF0)
-- wrapping: an unbounded sum is unbounded again
#guard (u32.add (c32 1)) == u32
#guard ((range 0 7).add (c32 1)) == range 1 8
-- casts: truncation keeps the low bits, widening keeps the value
#guard ((range 0 300).cast false 8) == Abs.top false 8
#guard ((range 0 200).cast false 8) ==
  Abs.reduce { Abs.top false 8 with lo := 0, hi := 200 }
#guard ((Abs.top false 8).cast false 32) == range 0 255
#guard ((c32 5).cast true 64) == Abs.const true 64 5
-- comparison and narrowing
#guard Abs.cmp .lt (range 0 7) (c32 8) == .yes
#guard Abs.cmp .lt (range 0 8) (c32 8) == .maybe
#guard Abs.cmp .eq (c32 3) (c32 3) == .yes
#guard (Abs.narrow .lt u32 (c32 16)).1 == range 0 15
#guard (Abs.narrow .ge u32 (range 3 5)).1.lo == 3
-- the join is the hull, keeping the bits both agree on
#guard ((range 0 5).join (range 3 9)) == range 0 9
#guard ((c32 4).join (c32 6)).km &&& 1 == 1

/-! ### Facts over a scope of stack locals -/

private def v (x : String) : Expr := .var sp x
private def n (k : Nat) : Expr := .lit sp k (toString k)
private def lt (a b : Expr) : Expr := .cmp sp .lt a b
private def le (a b : Expr) : Expr := .cmp sp .le a b
private def eq (a b : Expr) : Expr := .cmp sp .eq a b
private def add (a b : Expr) : Expr := .arith sp .add a b

/-- A scope of unsigned locals of the given widths, on the stack. -/
def scopeOf (locals : List (String × Nat))
    (consts : List (String × Int) := []) : Scope :=
  { place := fun
      | .var _ x =>
        (locals.lookup x).map fun w => (Origin.stack, Shape.int false w)
      | _ => none,
    const := fun c => consts.lookup c,
    sort := fun
      | .int _ s w => some (.int s w)
      | .bool _ => some .bool
      | _ => none,
    size := fun _ => none }

private def sc := scopeOf [("x", 32), ("y", 32), ("i", 64), ("nn", 64)]

private def facts (ps : List Expr) : Facts :=
  ps.foldl (fun F p => F.add (.pred p)) {}

-- assume splits conjunctions and pushes negation to the comparison
#guard (Facts.assume sc {}
  (.and sp (lt (v "x") (n 5)) (lt (v "y") (n 6)))).facts.length == 2
#guard (Facts.assume sc {} (Facts.negate (lt (v "x") (n 5)))).print ==
  ["x >= 5"]
-- a store kills the facts about its place and records the store
#guard (Facts.record sc (facts [lt (v "x") (n 5)]) (.var sp "x") (n 9)).print
  == ["x == 9"]
-- a store whose value reads the place records nothing
#guard (Facts.record sc (facts [lt (v "x") (n 5)]) (.var sp "x")
  (add (v "x") (n 1))).print == []
-- a call keeps stack facts
#guard ((facts [lt (v "x") (n 5)]).killShared sc).print == ["x < 5"]
-- the meet keeps what both know and the hull of the rest
#guard let m := (Facts.meet sc (facts [lt (v "x") (n 5), lt (v "y") (n 2)])
    (facts [lt (v "x") (n 7), lt (v "y") (n 2)])).print
  m.contains "y < 2" && m.contains "x <= 6" && !m.contains "x < 5"
-- an exited path contributes nothing
#guard (Facts.meet sc (facts [lt (v "x") (n 5)]).bot
  (facts [lt (v "y") (n 2)])).print == ["y < 2"]
