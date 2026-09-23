import Koit.Compile.Compile

/-!
The shape checker behind `koitc shape`: the syntactic part of Lemma
L, tested on every compiled unit. Lemma L says that every fact the
checker spent is a branch on the path of the emitted code, that every
cast is an instruction the verifier tracks exactly, and that the
register an access indexes with is the one the comparison tested. No
theorem proves acceptance, since the verifier is not modeled; these
three checks are a test, not a proof, and their failures are compiler
bugs.

- L1, the tests. Pass B emits a test wherever Core has a marker,
  closed LIR has one `if` per test, the flattening one `jcond` per
  `if`, and the allocation adds none but the one inside `csum_add`'s
  expansion. The check counts the markers of each Core body against
  the tests of its LIR, compares the comparisons of each closed LIR
  program with the conditional jumps of its BIR by family and class,
  and counts the bytecode's.
- L2, the casts. The cast table of the target, restated here rather
  than read from the flattening, gives each LIR cast its instruction;
  the BIR must contain at least that many of each shape. BIR has no
  statement boundaries, so a count by shape is what can be tested
  without re-running the pass.
- L3, the indexes. A forward analysis over BIR tracks which registers
  hold packet pointers, by the instruction that gave them their
  variable part and a constant offset, which hold `data_end`, and
  which scalars carry a bound: a constant, a narrow load, a mask, or
  a comparison on their path. A packet access needs a comparison of
  a pointer with the same variable part against `data_end`, covering
  its bytes, on every path that reaches it; a scalar added to a
  location needs a bound. This is the verifier's own linking of a
  bounds check to the pointers that share its id, so a failure here
  is a program the verifier rejects.
-/

namespace Koit.Compile

open Koit.Core (CmpOp)
open Koit.BPF (Instr Src Cls AluOp Cmp VReg Label RegClass Cpu BIR Bytecode)
open Koit.Interface (KindDecl)

/-! ### L1, the tests -/

/-- A comparison's family, which the flattening's negations and flips
preserve: equality, unsigned order, signed order, or the bit test no
LIR comparison becomes. -/
inductive Family where
  | eq | ord | sord | set
  deriving BEq, Repr, Inhabited

def Family.print : Family → String
  | .eq => "equality"
  | .ord => "unsigned"
  | .sord => "signed"
  | .set => "bit-test"

def familyOf (op : CmpOp) (signed : Bool) : Family :=
  match op with
  | .eq | .ne => .eq
  | _ => if signed then .sord else .ord

def familyOfCmp : Cmp → Family
  | .eq | .ne => .eq
  | .gt | .ge | .lt | .le => .ord
  | .sgt | .sge | .slt | .sle => .sord
  | .set => .set

/-- A test as the check sees it: its family and its class. -/
abbrev TestKey := Family × Cls

def TestKey.print (k : TestKey) : String := s!"{k.1.print} at {k.2.print}"

/-- The tests of LIR statements, one per `if`, in order. -/
partial def lirTests (ss : List LIR.Stmt) : List TestKey :=
  ss.flatMap fun s =>
    match s with
    | .ite _ c t e => (familyOf c.op c.signed, clsOf c.w) :: (lirTests t ++ lirTests e)
    | .block _ b | .loop _ b => lirTests b
    | .call _ _ _ _ u a => lirTests (u.getD []) ++ lirTests (a.getD [])
    | _ => []

/-- The conditional jumps of a program of the instruction set. -/
def jumpTests (code : Array (Instr ρ τ)) : List TestKey :=
  code.toList.filterMap fun
    | .jcond cmp cls .. => some (familyOfCmp cmp, cls)
    | _ => none

/-- How many times each element occurs, in order of first
appearance. -/
def tally [BEq α] (ks : List α) : List (α × Nat) :=
  ks.foldl (fun acc k =>
    if acc.any (·.1 == k) then
      acc.map fun (k', n) => if k' == k then (k', n + 1) else (k', n)
    else acc ++ [(k, 1)]) []

def describeTests (t : List (TestKey × Nat)) : String :=
  if t.isEmpty then "none" else
  ", ".intercalate (t.map fun (k, n) => s!"{n} {k.print}")

/-- The markers of a Core body that pass B emits a test for: a
branch, a loop's bound, a `try` other than one on a `T?` function,
whose test is the callee's return, and a `hold` whose acquisition can
fail. A boolean condition may lower to more tests than this counts,
never to fewer. -/
partial def coreMarkers (ss : List Core.Stmt) : Nat :=
  ss.foldl (fun n s => n + match s with
    | .ite _ _ t e => 1 + coreMarkers t + coreMarkers e
    | .loop _ _ b | .«for» _ _ _ _ b => 1 + coreMarkers b
    | .«try» _ _ op t e _ =>
      (match op with | .callopt .. => 0 | _ => 1) + coreMarkers t + coreMarkers e
    | .hold _ _ _ _ b e =>
      (if e.isSome then 1 else 0) + coreMarkers b + coreMarkers (e.getD [])
    | _ => 0) 0

/-- Pass B on every body: at least one LIR test per Core marker. The
errors, the markers, and the tests. -/
def passB (core : Core.CompUnit) (lir : LIR.CompUnit) : List String × Nat × Nat := Id.run do
  let mut errs : List String := []
  let mut markers := 0
  let mut tests := 0
  let bodies : List (String × List Core.Stmt × Option (List LIR.Stmt)) :=
    core.fns.map (fun f =>
      (f.name, f.body, (lir.fns.find? (·.name == f.name)).map (·.body))) ++
    core.programs.map (fun p =>
      (p.name, p.body ++ p.handlers.flatMap (·.body),
       (lir.programs.find? (·.name == p.name)).map fun q =>
         q.body ++ q.handlers.flatMap (·.body)))
  for (name, cb, lb) in bodies do
    let m := coreMarkers cb
    match lb with
    | none => errs := errs ++ [s!"pass B: `{name}` has no LIR body"]
    | some lb =>
      let t := (lirTests lb).length
      markers := markers + m
      tests := tests + t
      if t < m then
        errs := errs ++ [s!"pass B: `{name}` has {m} markers in Core and {t} tests in LIR"]
  return (errs, markers, tests)

/-- L1 on one program: the LIR tests and the BIR jumps agree by
family and class, and the bytecode has the BIR's jumps plus one per
inline checksum add. The errors, the tests, and the bytecode's
jumps. -/
def passL1 (body : List LIR.Stmt) (B : BIR) (A : Bytecode) : List String × Nat × Nat :=
  let lt := tally (lirTests body)
  let bt := tally (jumpTests B.code)
  let keys := (lt.map (·.1) ++ bt.map (·.1)).eraseDups
  let same := keys.all fun k => (lt.lookup k).getD 0 == (bt.lookup k).getD 0
  let e1 := if same then [] else
    [s!"L1: LIR tests {describeTests lt}; BIR jumps {describeTests bt}"]
  let inl := B.code.toList.countP fun
    | .call (.kernel "csum_add") .. => true
    | _ => false
  let nB := (jumpTests B.code).length
  let nA := (jumpTests A.code).length
  let e2 := if nA == nB + inl then [] else
    [s!"L1: BIR has {nB} conditional jumps and the bytecode {nA}, \
      with {inl} inline checksum adds"]
  (e1 ++ e2, (lirTests body).length, nA)

/-! ### L2, the casts -/

/-- The instruction a cast is, as the table of the target has it. -/
inductive Shape where
  | movsx (cls : Cls) (w : Nat)
  /-- `lsh_imm k; arsh_imm k` at the class. -/
  | pair (cls : Cls) (k : Nat)
  | mov32
  | mask (w : Nat)
  deriving BEq, Repr, Inhabited

def Shape.print : Shape → String
  | .movsx cls w => s!"movsx({cls.print}, {w})"
  | .pair cls k => s!"lsh_imm({cls.print}) {k}; arsh_imm({cls.print}) {k}"
  | .mov32 => "mov(32) d d"
  | .mask w => s!"and_imm(32) d mask_{w}"

/-- The cast table: the instruction of a cast from `int(s,w)` to
`int(s',w')`, or none when the normal form already has it. To 64
from a signed source below 64, the sign extension from 32; to 32
from 64, the 32-bit move; to a narrow width, the mask for unsigned
and the sign extension from the width for signed; every other cast
is the identity on the register. -/
def castShape (cpu : Cpu) (s : Bool) (w : Nat) (s' : Bool) (w' : Nat) : Option Shape :=
  if w' == 64 then
    if s && w < 64 then
      some (match cpu with | .v4 => .movsx .w64 32 | .v3 => .pair .w64 32)
    else none
  else if w' == 32 then
    if w == 64 then some .mov32 else none
  else if s' then
    some (match cpu with | .v4 => .movsx .w32 w' | .v3 => .pair .w32 (32 - w'))
  else some (.mask w')

mutual

/-- The shapes of the casts in an expression, in order. -/
partial def exprCasts (cpu : Cpu) : LIR.Expr → List Shape
  | .cast s w s' w' e => (castShape cpu s w s' w').toList ++ exprCasts cpu e
  | .arith _ _ _ l r => exprCasts cpu l ++ exprCasts cpu r
  | .bswap _ e => exprCasts cpu e
  | .load _ _ a | .addr a => addrCasts cpu a
  | _ => []

partial def addrCasts (cpu : Cpu) : LIR.Addr → List Shape
  | .plus a _ => addrCasts cpu a
  | .index a e _ => addrCasts cpu a ++ exprCasts cpu e
  | _ => []

end

/-- The shapes of the casts in statements. -/
partial def stmtCasts (cpu : Cpu) (ss : List LIR.Stmt) : List Shape :=
  ss.flatMap fun s =>
    match s with
    | .«let» _ _ _ e | .assign _ _ e | .ctxStore _ _ e | .raise _ _ e => exprCasts cpu e
    | .store _ _ a e => addrCasts cpu a ++ exprCasts cpu e
    | .ite _ c t e =>
      exprCasts cpu c.l ++ exprCasts cpu c.r ++ stmtCasts cpu t ++ stmtCasts cpu e
    | .block _ b | .loop _ b => stmtCasts cpu b
    | .ret _ e => (e.map (exprCasts cpu)).getD []
    | .call _ _ _ args u a =>
      args.flatMap (exprCasts cpu) ++ stmtCasts cpu (u.getD []) ++ stmtCasts cpu (a.getD [])
    | .builtin _ _ _ args | .kernel _ _ _ args => args.flatMap (exprCasts cpu)
    | _ => []

/-- The shapes of the table that occur in BIR code: a sign-extending
move onto its own register, a 32-bit move onto its own register, a
mask of a byte or a halfword at 32 bits, and a shift pair. -/
def codeShapes (code : Array (Instr VReg Label)) : List Shape := Id.run do
  let mut out : List Shape := []
  for i in [0:code.size] do
    match code[i]! with
    | .movsx cls w d s => if d == s then out := out ++ [.movsx cls w]
    | .mov .w32 d (.reg s) => if d == s then out := out ++ [.mov32]
    | .alu .and .w32 _ (.imm k) =>
      if k == 255 then out := out ++ [.mask 8]
      else if k == 65535 then out := out ++ [.mask 16]
    | .alu .lsh cls d (.imm k) =>
      match code[i + 1]? with
      | some (.alu .arsh cls' d' (.imm k')) =>
        if cls == cls' && d == d' && k == k' && k > 0 then out := out ++ [.pair cls k.toNat]
      | _ => pure ()
    | _ => pure ()
  return out

/-- L2 on one program: the BIR has at least as many instructions of
each shape as the LIR's casts need. The errors and the casts with an
instruction. -/
def passL2 (body : List LIR.Stmt) (B : BIR) : List String × Nat := Id.run do
  let expected := stmtCasts B.cpu body
  let found := tally (codeShapes B.code)
  let mut errs : List String := []
  for (sh, n) in tally expected do
    let m := (found.lookup sh).getD 0
    if m < n then
      errs := errs ++ [s!"L2: {n} casts need `{sh.print}` and the code has {m}"]
  return (errs, expected.length)

/-! ### L3, the indexes -/

/-- What the analysis knows of a register. -/
inductive Val where
  /-- A location that is not a packet pointer, or a handle; also
  what an unwritten register reads as. -/
  | other
  /-- A packet pointer: `data`, plus the variable part the
  instruction `id` added, `0` for none, plus a constant. -/
  | pkt (id : Nat) (off : Int)
  | pend
  /-- A scalar: whether a bound is known for it, and the instruction
  that originated it when one did. -/
  | sc (bounded : Bool) (origin : Option Nat)
  /-- A location whose provenance a join or a resize lost. -/
  | lost
  deriving BEq, Repr, Inhabited

def Val.isLoc : Val → Bool
  | .sc .. => false
  | _ => true

/-- The join of two registers' values: equal values stay, two scalars
keep a common bound and a common origin, anything else is lost. -/
def Val.join (a b : Val) : Val :=
  if a == b then a else
  match a, b with
  | .sc b1 o1, .sc b2 o2 => .sc (b1 && b2) (if o1 == o2 then o1 else none)
  | _, _ => .lost

/-- The state at a program point: the registers with a value other
than `other`, sorted, and per variable part the bytes a comparison
with `data_end` has shown readable. -/
structure LState where
  regs   : List (VReg × Val) := []
  extent : List (Nat × Int) := []
  deriving BEq, Inhabited

def vrank : VReg → Nat
  | .ctx => 0
  | .fp => 1
  | .ret => 2
  | .reason => 3
  | .v n => 4 + n

def LState.get (st : LState) (r : VReg) : Val := (st.regs.lookup r).getD .other

def LState.set (st : LState) (r : VReg) (v : Val) : LState :=
  let rest := st.regs.filter (·.1 != r)
  let regs := if v == .other then rest else
    ((r, v) :: rest).toArray.qsort (fun a b => vrank a.1 < vrank b.1) |>.toList
  { st with regs }

/-- A comparison on `r` bounds it, and every register of the same
origin, as the verifier links copies of a scalar. -/
def LState.bound (st : LState) (r : VReg) : LState :=
  match st.get r with
  | .sc _ (some o) =>
    { st with regs := st.regs.map fun (r', v) =>
        match v with
        | .sc _ (some o') => if o' == o then (r', .sc true (some o)) else (r', v)
        | _ => (r', v) }
  | .sc false none => st.set r (.sc true none)
  | _ => st

/-- `n` bytes from the base of the variable part `id` shown readable. -/
def LState.extend (st : LState) (id : Nat) (n : Int) : LState :=
  if n < 0 then st else
  let cur := (st.extent.lookup id).getD n
  let rest := st.extent.filter (·.1 != id)
  { st with extent := ((id, max cur n) :: rest).toArray.qsort (fun a b => a.1 < b.1) |>.toList }

def LState.join (a b : LState) : LState :=
  let keys := (a.regs.map (·.1) ++ b.regs.map (·.1)).eraseDups
  let regs := keys.filterMap fun r =>
    let v := (a.get r).join (b.get r)
    if v == .other then none else some (r, v)
  let regs := regs.toArray.qsort (fun x y => vrank x.1 < vrank y.1) |>.toList
  let extent := a.extent.filterMap fun (id, n) =>
    match b.extent.lookup id with
    | some m => some (id, min n m)
    | none => none
  { regs, extent }

/-- After a resize every packet pointer is stale and every extent
gone. -/
def LState.resized (st : LState) : LState :=
  { regs := st.regs.map fun (r, v) =>
      match v with
      | .pkt .. | .pend => (r, .lost)
      | _ => (r, v),
    extent := [] }

/-- The analysis of one program. -/
structure L3 where
  pre  : Interface
  kind : KindDecl
  B    : BIR

/-- One instruction's effect: the successors with their states, the
errors, and the packet accesses and indexes it checked. -/
structure Step where
  next   : List (Nat × LState) := []
  errors : List String := []
  pkts   : Nat := 0
  idxs   : Nat := 0
  deriving Inhabited

/-- A scalar this instruction originates, bounded when `bounded`. -/
def freshSc (i : Nat) (bounded : Bool := false) : Val := .sc bounded (some i)

/-- What a call leaves in its result register: a location for the
builtins and declarations that yield one, else a scalar of unknown bound. -/
def L3.result (X : L3) (h : BPF.Callee) (i : Nat) : Val :=
  match h with
  | .builtin .lookup | .builtin (.reserve _) => .other
  | .builtin _ => freshSc i
  | .kernel decl =>
    match X.pre.call? decl with
    | some r => if LIR.rowResult r == .ptr then .other else freshSc i
    | none => .lost

/-- The context offset of `data` or `data_end` in the program's kind. -/
def L3.bound? (X : L3) (isEnd : Bool) : Option Int :=
  (X.kind.ctxBounds.find? (·.isEnd == isEnd)).map fun b => (b.offset : Int)

def L3.target (X : L3) (l : Label) : List Nat := (X.B.labels.lookup l.id).toList

def L3.at (X : L3) (i : Nat) : String :=
  match X.B.code[i]? with
  | some ins => s!"instruction {i}, `{ins.print VReg.print Label.print}`"
  | none => s!"instruction {i}"

/-- An access through `b` at displacement `k` of `w` bits: a packet
access needs a comparison covering its bytes; whether it was one. -/
def L3.access (X : L3) (st : LState) (i : Nat) (b : VReg) (k : Int) (w : Nat) :
    Option String × Bool :=
  match st.get b with
  | .pkt id ob =>
    let lo := ob + k
    let hi := lo + w / 8
    if lo < 0 then
      (some s!"L3: {X.at i} reaches before the packet pointer in {b.print}", true)
    else
      match st.extent.lookup id with
      | none =>
        (some s!"L3: {X.at i} accesses the packet through {b.print}, which no \
          comparison with data_end on its path covers", true)
      | some n =>
        if hi ≤ n then (none, true)
        else
          (some s!"L3: {X.at i} needs {hi} bytes from the packet pointer in {b.print}, \
            and the comparison on its path shows {n}", true)
  | .pend => (some s!"L3: {X.at i} accesses the packet through data_end", true)
  | .lost =>
    (some s!"L3: {X.at i} accesses memory through {b.print}, a location the check \
      cannot trace to one test", true)
  | _ => (none, false)

/-- A scalar added to a location needs a bound. -/
def L3.index (X : L3) (st : LState) (i : Nat) (r : VReg) : Option String :=
  match st.get r with
  | .sc false _ =>
    some s!"L3: {X.at i} indexes with {r.print}, which no comparison on its path bounds"
  | .lost => some s!"L3: {X.at i} indexes with {r.print}, a value the check cannot trace"
  | _ => none

/-- The states after a conditional jump, taken and fallen through: a
comparison of a packet pointer with `data_end` shows the pointer's
bytes readable on the side where it lies below, strictly one more,
and a comparison bounds a scalar on the side that gives it an upper
bound, or fixes it. -/
def refine (st : LState) (cmp : Cmp) (a : VReg) (b : Src VReg) : LState × LState :=
  let va := st.get a
  let vb := match b with
    | .reg r => some (st.get r)
    | .imm _ => none
  let (t, f) := match va, vb, cmp with
    | .pkt id off, some .pend, .le => (st.extend id off, st)
    | .pkt id off, some .pend, .lt => (st.extend id (off + 1), st)
    | .pkt id off, some .pend, .gt => (st, st.extend id off)
    | .pkt id off, some .pend, .ge => (st, st.extend id (off + 1))
    | .pend, some (.pkt id off), .ge => (st.extend id off, st)
    | .pend, some (.pkt id off), .gt => (st.extend id (off + 1), st)
    | .pend, some (.pkt id off), .lt => (st, st.extend id off)
    | .pend, some (.pkt id off), .le => (st, st.extend id (off + 1))
    | _, _, _ => (st, st)
  let (t, f) := match va, cmp with
    | .sc .., .lt | .sc .., .le | .sc .., .slt | .sc .., .sle | .sc .., .eq => (t.bound a, f)
    | .sc .., .gt | .sc .., .ge | .sc .., .sgt | .sc .., .sge | .sc .., .ne => (t, f.bound a)
    | _, _ => (t, f)
  match b, vb, cmp with
  | .reg r, some (.sc ..), .lt | .reg r, some (.sc ..), .le | .reg r, some (.sc ..), .slt
  | .reg r, some (.sc ..), .sle | .reg r, some (.sc ..), .ne => (t, f.bound r)
  | .reg r, some (.sc ..), .gt | .reg r, some (.sc ..), .ge | .reg r, some (.sc ..), .sgt
  | .reg r, some (.sc ..), .sge | .reg r, some (.sc ..), .eq => (t.bound r, f)
  | _, _, _ => (t, f)

/-- Whether an operation with an immediate bounds its result: a mask,
a right shift, a division, a modulo. -/
def boundsBy (op : AluOp) (k : Int) : Bool :=
  match op with
  | .and => k ≥ 0
  | .rsh | .div | .mod => true
  | _ => false

/-- The instruction at `i` from `st`. -/
def L3.step (X : L3) (i : Nat) (st : LState) : Step :=
  match X.B.code[i]? with
  | none => { errors := [s!"L3: no instruction at {i}"] }
  | some ins =>
    let fall := i + 1
    let next (st : LState) : Step := { next := [(fall, st)] }
    let withAccess (b : VReg) (k : Int) (w : Nat) (s : Step) : Step :=
      let (e, isPkt) := X.access st i b k w
      { s with errors := e.toList ++ s.errors, pkts := s.pkts + (if isPkt then 1 else 0) }
    -- what a location becomes with a scalar added
    let derived (v : Val) : Val :=
      match v with
      | .pkt .. => .pkt i 0
      | .other => .other
      | _ => .lost
    match ins with
    | .alu op cls d s =>
      match s with
      | .imm k =>
        let v := match op, st.get d with
          | .add, .pkt id off => .pkt id (off + k)
          | .sub, .pkt id off => .pkt id (off - k)
          | _, .sc b o => .sc (b || boundsBy op k || cls == .w32) o
          | _, .other => .other
          | _, _ => .lost
        next (st.set d v)
      | .reg r =>
        match st.get d, st.get r with
        | .sc b1 o1, .sc b2 _ =>
          let v := if b1 && b2 then .sc true o1
            else .sc (cls == .w32 || boundsBy op 0 && op != .and) (some i)
          next (st.set d v)
        | vd, .sc .. =>
          let v := if op == .add || op == .sub then derived vd else .lost
          let s := next (st.set d v)
          { s with errors := (X.index st i r).toList, idxs := 1 }
        | .sc .., vr =>
          let v := if op == .add then derived vr else .lost
          let s := next (st.set d v)
          { s with errors := (X.index st i d).toList, idxs := 1 }
        | _, _ =>
          next (st.set d (if op == .sub then .sc false (some i) else .lost))
    | .mov cls d s =>
      match s with
      | .imm _ => next (st.set d (.sc true (some i)))
      | .reg r =>
        let v := match st.get r, cls with
          | .sc _ o, .w32 => .sc true o
          | v, .w32 => if v.isLoc then .lost else v
          | v, .w64 => v
        next (st.set d v)
    | .movsx _ _ d s =>
      next (st.set d (match st.get s with | .sc b o => .sc b o | _ => .lost))
    | .«end» _ w d =>
      next (st.set d (match st.get d with | .sc b o => .sc (b || w < 64) o | _ => .lost))
    | .ldx w d s off =>
      if s == .ctx then
        let v := if X.bound? false == some off then .pkt 0 0
          else if X.bound? true == some off then .pend
          else freshSc i (w < 64)
        next (st.set d v)
      else
        withAccess s off w (next (st.set d (freshSc i (w < 64))))
    | .stx w d off _ => withAccess d off w (next st)
    | .ja t => { next := (X.target t).map (·, st) }
    | .jcond cmp _ a b t =>
      let (ts, fs) := refine st cmp a b
      { next := (X.target t).map (·, ts) ++ [(fall, fs)] }
    | .lddw d _ => next (st.set d (.sc true (some i)))
    | .lea d _ | .mapref d _ | .mapval d _ _ => next (st.set d .other)
    | .call h _ dst =>
      let resize := match h with
        | .kernel decl =>
          match X.pre.call? decl with
          | some r => Machine.hasFlag r.effects .resize
          | none => false
        | .builtin _ => false
      let st := if resize then st.resized else st
      let st := match dst with
        | some d => st.set d (X.result h i)
        | none => st
      next st
    | .atomic _ cls fetch d off s =>
      let st' := if fetch then st.set s (.sc (cls == .w32) (some i)) else st
      withAccess d off cls.bits (next st')
    | .exit => {}

/-- The analysis to its fixed point, then every instruction checked
under the state that reaches it. The errors, the packet accesses,
and the indexes checked. -/
def L3.run (X : L3) : List String × Nat × Nat := Id.run do
  let n := X.B.code.size
  let mut states : Array (Option LState) := Array.replicate n none
  if n > 0 then states := states.set! 0 (some {})
  let mut changed := true
  let mut rounds := 0
  while changed && rounds ≤ 4 * n + 8 do
    changed := false
    rounds := rounds + 1
    for i in [0:n] do
      if let some st := states[i]! then
        for (j, sj) in (X.step i st).next do
          if j < n then
            let merged := match states[j]! with
              | none => sj
              | some t => t.join sj
            unless states[j]! == some merged do
              changed := true
              states := states.set! j (some merged)
  if changed then return (["L3: the analysis did not converge"], 0, 0)
  let mut errs : List String := []
  let mut pkts := 0
  let mut idxs := 0
  for i in [0:n] do
    if let some st := states[i]! then
      let r := X.step i st
      errs := errs ++ r.errors
      pkts := pkts + r.pkts
      idxs := idxs + r.idxs
  return (errs, pkts, idxs)

/-! ### The report -/

/-- What the check says of one program, or of the unit's pass B when
the name is empty: the summary lines when it passes, the errors when
it does not. -/
structure ShapeReport where
  name   : String
  lines  : List String := []
  errors : List String := []
  deriving Inhabited

def ShapeReport.print (r : ShapeReport) : List String :=
  let pre := if r.name.isEmpty then "" else s!"{r.name}: "
  (r.errors ++ r.lines).map (pre ++ ·)

def shapeProgram (pre : Interface) (p : LIR.Program) (B : BIR) (A : Bytecode) : ShapeReport :=
  let body := p.body ++ p.handlers.flatMap (·.body)
  let (e1, nTests, nA) := passL1 body B A
  let (e2, nCasts) := passL2 body B
  match pre.kind? B.kind with
  | none => { name := p.name, errors := [s!"unknown kind `{B.kind}`"] }
  | some kind =>
    let (e3, pkts, idxs) := L3.run { pre, kind, B }
    let errors := e1 ++ e2 ++ e3
    let lines := if errors.isEmpty then
      [s!"L1: {nTests} tests in LIR, as many conditional jumps in BIR, {nA} in bytecode",
       s!"L2: {nCasts} casts, each with its instruction of the table",
       s!"L3: {pkts} packet accesses covered, {idxs} indexes bounded"]
      else []
    { name := p.name, lines, errors }

/-- The check on a compiled unit: pass B on the LIR before inlining,
then L1 to L3 on every program. -/
def shapeUnit (pre : Interface) (core : Core.CompUnit) (openLir : LIR.CompUnit)
    (C : Compiled) : List ShapeReport :=
  let (eB, markers, tests) := passB core openLir
  let unitLines := if eB.isEmpty then
    [s!"pass B: {markers} markers in Core, {tests} tests in LIR"] else []
  let unit : ShapeReport := { name := "", errors := eB, lines := unitLines }
  let progs := C.lir.programs.map fun p =>
    match C.birs.find? (·.name == p.name), C.allocated.find? (·.prog.name == p.name) with
    | some B, some A => shapeProgram pre p B A.prog
    | _, _ => { name := p.name, errors := ["no flattened or allocated program"] }
  unit :: progs

def shapeOk (rs : List ShapeReport) : Bool := rs.all (·.errors.isEmpty)

end Koit.Compile
