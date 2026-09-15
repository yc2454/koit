import KoitTests.Facts

/-!
Checks on entailment: the entailments each program of the corpus
relies on, written out over the facts its checker has at the demand,
and the ones the procedure must refuse.
-/

open Koit Koit.Core Koit.Facts

private def sp : Span := noSpan
private def v (x : String) : Expr := .var sp x
private def n (k : Nat) : Expr := .lit sp k (toString k)
private def lt (a b : Expr) : Expr := .cmp sp .lt a b
private def le (a b : Expr) : Expr := .cmp sp .le a b
private def ne (a b : Expr) : Expr := .cmp sp .ne a b
private def eq (a b : Expr) : Expr := .cmp sp .eq a b
private def add (a b : Expr) : Expr := .arith sp .add a b
private def mul (a b : Expr) : Expr := .arith sp .mul a b
private def mod (a b : Expr) : Expr := .arith sp .mod a b
private def band (a b : Expr) : Expr := .arith sp .band a b
private def u32 (e : Expr) : Expr := .cast sp e (.int sp false 32)
private def u64 (e : Expr) : Expr := .cast sp e (.int sp false 64)

private def sc := scopeOf [("h", 32), ("cur", 32), ("x", 32), ("y", 32),
  ("b", 8), ("i", 64), ("nn", 64), ("rlen", 64), ("nkeys", 64), ("vv", 32)]
  [("M", 16), ("MAX_KEY", 250), ("DATA_SIZE", 1303), ("SLOTS", 3250000),
   ("MAX_KEYS", 30), ("MAXLEN", 32), ("PASS", 2), ("DROP", 1), ("REDIRECT", 4)]

private def facts (ps : List Expr) : Facts :=
  ps.foldl (fun F p => F.add (.pred p)) {}

private def ent (ps : List Expr) (P : Expr) : Bool := entails sc (facts ps) P

-- by-example-m1, picker: the marked load's refinement, membership;
-- the modulo, by interpretation
#guard ent [lt (v "cur") (v "M")] (lt (v "cur") (v "M"))
#guard ent [] (lt (mod (add (v "cur") (n 1)) (v "M")) (v "M"))
#guard !ent [] (lt (add (v "cur") (n 1)) (v "M"))
-- bmc-cache: the hash into the slots, the key length bound, the loop
-- index under the refined local, the length through a cast
#guard ent [] (lt (mod (v "h") (v "SLOTS")) (v "SLOTS"))
#guard ent [lt (v "i") (v "MAX_KEY")] (le (add (v "i") (n 1)) (v "MAX_KEY"))
#guard ent [le (v "nn") (v "MAX_KEY"), le (n 0) (v "i"), lt (v "i") (v "nn")]
  (lt (v "i") (v "DATA_SIZE"))
#guard ent [le (v "nn") (v "DATA_SIZE")] (le (u32 (v "nn")) (v "DATA_SIZE"))
#guard ent [le (v "rlen") (v "DATA_SIZE"), lt (v "i") (v "rlen")]
  (lt (v "i") (v "DATA_SIZE"))
-- bmc-request-path: the negated exit condition, then the cast
#guard ent [ne (v "nn") (n 0), le (v "nn") (v "MAX_KEY")]
  (le (u32 (v "nn")) (v "MAX_KEY"))
#guard ent [lt (v "nkeys") (v "MAX_KEYS")] (lt (v "nkeys") (v "MAX_KEYS"))
-- by-example-m4: the loop bound and the count
#guard ent [lt (v "i") (v "MAXLEN")] (le (add (v "i") (n 1)) (v "MAXLEN"))
-- by-example-f: the branch
#guard ent [lt (v "x") (n 4)] (lt (v "x") (n 4))
-- monitor-filter and picker: a verdict within the set
#guard entailsIn sc (facts [le (n 1) (v "vv"), le (v "vv") (n 2)]) (v "vv")
  [2, 1]
#guard entailsIn sc (facts [eq (v "vv") (v "REDIRECT")]) (v "vv") [2, 1, 0, 4]
#guard !entailsIn sc (facts [eq (v "vv") (v "REDIRECT")]) (v "vv") [2, 1]
#guard constOf sc (facts [eq (v "vv") (v "REDIRECT")]) (v "vv") == some 4
-- tests/ok/facts.ko: a mask, a byte widened, a product reduced
#guard ent [eq (band (v "x") (n 0xFFFFFFF0)) (n 0)] (lt (v "x") (n 16))
#guard !ent [eq (band (v "x") (n 0xF0)) (n 0)] (lt (v "x") (n 16))
#guard ent [] (lt (mod (u32 (v "b")) (v "M")) (v "M"))
#guard ent [] (lt (mod (mul (v "x") (n 7)) (v "M")) (v "M"))
-- equal names substitute for each other
#guard ent [eq (v "y") (v "x"), lt (v "x") (n 5)] (lt (v "y") (n 5))
-- what the procedure refuses: a looser bound, an unknown, an off-by-one
#guard !ent [lt (v "x") (n 20)] (lt (v "x") (n 5))
#guard !ent [] (lt (v "x") (n 16))
#guard !ent [le (v "i") (n 4096)] (lt (v "i") (n 4096))
-- the cap of a loop bound
#guard upperOf sc (facts [le (v "nn") (v "MAX_KEY")]) (v "nn") == some 250
#guard upperOf sc {} (v "nn") == some (2 ^ 64 - 1)
-- the solver query names the atoms and denies the goal
private def q : String :=
  Smt.query sc (facts [lt (v "x") (n 20)]) (lt (v "x") (n 5))
#guard (q.splitOn "(declare-const |x| (_ BitVec 32))").length == 2
#guard (q.splitOn "(assert (not (bvult |x| (_ bv5 32))))").length == 2
