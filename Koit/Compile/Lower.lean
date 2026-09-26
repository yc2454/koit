import Koit.Compile.Fold
import Koit.LIR.Wf

/-!
Pass B, Core to LIR: the translation is per function and per
program, driven by the checker's environment for types and by four
pieces of context threaded through statements: `Γ`, the type of each
Core name in scope, from which the width and signedness of every
operator and literal are read; `ρ`, the release context, a stack of
the `block` and `loop` constructs the translation has opened and of
the release actions of the `hold` bodies it is inside; `μ`, the
owned names moved on the current path; and the depth each `br`
needs, read off `ρ`.

Expressions lower in two modes. One with no call and no map slot
reached by helper lowers to one pure LIR expression at the checker's
types. Any other lowers in administrative normal form: each call
into its own binding in Core's evaluation order, and any load that
precedes a call in that order hoisted with it, so that LIR
expressions are pure and the order of effects is Core's. Booleans in
value position become a byte set by nested tests, as the
short-circuit rules evaluate them.

Every runtime test is emitted where the source had a marker, and
two more where the verifier requires them, each with a branch the
checker's facts make dead and which returns the kind's failure
verdict: the null test after a lookup by helper into an array map,
and the bound test on a view's element reached by an index that is
not a constant, since the verifier does not carry the view's test to
a pointer with a variable added. Every
release is a statement at the exit that owes it, innermost first,
and a call to a `fails` function carries the releases the call site
owes in its `unwind`. `move` emits nothing: the sink is the release.
-/

namespace Koit.Compile

open Koit (Span)
open Koit.Core
open Koit.Check (Env Ctx Local Checked synth check)
open Koit.Interface (CallDecl ResourceDecl KindDecl)
open Koit.Facts (Origin)

/-! ### The monad and the context -/

/-- The state of the translation: fresh names, the LIR names used in
the function at hand, and the owned names the statement being
translated has moved. -/
structure LS where
  counter : Nat := 0
  used    : List String := []
  moved   : List String := []

abbrev LM := StateT LS (Except String)

def lerr (msg : String) : LM α := throw msg

def liftC (x : Check.M α) : LM α :=
  match x with
  | .ok v => pure v
  | .error d => lerr s!"{d}"

/-- A name no local of the function has: `base_N`. -/
partial def freshName (base : String) : LM String := do
  let s ← get
  let cand := s!"{base}_{s.counter}"
  set { s with counter := s.counter + 1 }
  if s.used.contains cand then freshName base
  else
    modify fun s => { s with used := cand :: s.used }
    return cand

/-- The LIR name of a Core local: its own spelling when the function
has not used it, a suffixed one otherwise, since LIR declares each
name once. -/
def nameFor (x : String) : LM String := do
  let s ← get
  if s.used.contains x then freshName x
  else
    set { s with used := x :: s.used }
    return x

/-- One entry of `ρ`: a construct the translation has opened, or the
release action of a `hold` whose body is being translated. -/
inductive Marker where
  /-- The block around a loop, which `break` leaves. -/
  | exitBlock
  | loop
  /-- The block around a loop's body, which `continue` leaves. -/
  | bodyBlock
  | plain
  deriving Repr, BEq, Inhabited

inductive Scope where
  | construct (m : Marker)
  | release (decl : ResourceDecl) (obj : Option LIR.Addr) (name : Option String)

/-- What `return` returns to. -/
inductive RetTo where
  | program (vt : LIR.Ty)
  | handler (vt : LIR.Ty)
  | fn (ret : Option LIR.Ty) (opt : Bool)

structure LCtx where
  env    : Env
  K      : Ctx
  /-- Core name to LIR name, innermost first. -/
  names  : List (String × String) := []
  /-- Innermost first. -/
  rho    : List Scope := []
  mu     : List String := []
  ret    : RetTo
  kind   : Option KindDecl
  /-- The `err` local of the enclosing failed call, for `errno`. -/
  errno  : Option String := none
  direct : List String
  fns    : List Fn

/-- A lowered expression: the statements it needs first, the pure
expression, and its type. -/
structure LE where
  pre : List LIR.Stmt
  e   : LIR.Expr
  ty  : LIR.Ty

/-! ### Types -/

def normTy (c : LCtx) (t : Ty) : LM Ty := liftC (c.env.norm t)

/-- The LIR type of a Core type: integers at their width, byte-order
values as unsigned patterns, enumerations as unsigned integers of
their declaration's width, booleans as bytes, places as locations. Below this
point no type of the source language exists. -/
def lty (c : LCtx) (t : Ty) : LM LIR.Ty := do
  match ← normTy c t with
  | .int _ s w => return .int s w
  | .be _ w => return .int false w
  | .bool _ => return .u8
  | .enum s n =>
    match c.env.interface.enum? n with
    | some decl => return .int false decl.width
    | none => lerr s!"{s.start}: unknown enumeration `{n}`"
  | _ => return .ptr

def intParts : LIR.Ty → Bool × Nat
  | .int s w => (s, w)
  | .ptr => (false, 64)

def sizeOfTy (c : LCtx) (t : Ty) : LM Nat := do
  return (← liftC (c.env.layout t)).1

def synthTy (c : LCtx) (e : Expr) : LM Ty := liftC (synth c.env c.K e)

def isPoly (c : LCtx) (e : Expr) : Bool := c.env.isPoly e

def lname (c : LCtx) (x : String) : LM String :=
  match c.names.lookup x with
  | some y => pure y
  | none => lerr s!"`{x}` has no LIR name"

/-- The type of a scalar operand: the side with a type of its own,
or the expected type, or `u64`. -/
def operandTy (c : LCtx) (l r : Expr) (expected : Option Ty) : LM Ty := do
  if !isPoly c l then synthTy c l
  else if !isPoly c r then synthTy c r
  else return expected.getD Interface.tU64

def lit (w : Nat) (k : Nat) : LIR.Expr := .lit w (k % 2 ^ w)

def zeroOf (t : LIR.Ty) : LIR.Expr := lit (intParts t).2 0

/-- The opposite comparison. -/
def negCond (c : LIR.Cond) : LIR.Cond :=
  { c with op := match c.op with
      | .eq => .ne | .ne => .eq | .lt => .ge | .ge => .lt | .le => .gt | .gt => .le }

/-! ### Purity and hoisting -/

mutual

/-- Whether a pure LIR expression reads memory or the context, and
so must be evaluated before a call that follows it in Core's
order. -/
partial def volatile : LIR.Expr → Bool
  | .load .. | .ctx _ => true
  | .arith _ _ _ l r => volatile l || volatile r
  | .cast _ _ _ _ e | .bswap _ e => volatile e
  | .addr a => volatileAddr a
  | .lit .. | .var _ => false

partial def volatileAddr : LIR.Addr → Bool
  | .pktData | .pktEnd => true
  | .index a e _ => volatileAddr a || volatile e
  | .plus a _ => volatileAddr a
  | _ => false

end

/-- The expression bound to a temporary, unless it is already a name
or a literal. -/
def hoist (sp : Span) (l : LE) : LM LE := do
  match l.e with
  | .var _ | .lit .. => return l
  | _ =>
    let t ← freshName "t"
    return { pre := l.pre ++ [.«let» sp t l.ty l.e], e := .var t, ty := l.ty }

/-- Two operands in Core's order: when the right one needs statements,
a left one that reads memory is bound first. -/
def combine (sp : Span) (l r : LE) : LM (LE × LE) := do
  if !r.pre.isEmpty && volatile l.e then
    let l ← hoist sp l
    return (l, r)
  else return (l, r)

/-- A list of operands in order, each memory read that precedes a
later operand's statements bound first. -/
def sequence (sp : Span) (les : List LE) : LM (List LIR.Stmt × List LIR.Expr) := do
  let mut acc : List LE := []
  for l in les do
    if !l.pre.isEmpty then
      acc ← acc.mapM fun a => if volatile a.e then hoist sp a else pure a
    acc := acc ++ [l]
  return (acc.flatMap (·.pre), acc.map (·.e))

/-! ### Places -/

/-- What a place denotes in LIR: a scalar local, a context field, or
an address with the type of what is there. -/
inductive PRef where
  | local (x : String) (ty : Ty)
  | ctx (f : String) (ty : Ty)
  | mem (a : LIR.Addr) (ty : Ty)

/-- Whether a place lies in the packet: its root is a view. -/
def inPacket (c : LCtx) (p : Place) : Bool :=
  match p.root with
  | some x =>
    match c.env.local? x with
    | some l =>
      match l.ty with
      | .view .. => true
      | _ => false
    | none => false
  | none => false

def plusAddr (a : LIR.Addr) (k : Nat) : LIR.Addr :=
  if k == 0 then a else
  match a with
  | .plus a' k' => .plus a' (k' + k)
  | .mapval m k' => .mapval m (k' + k)
  | a => .plus a k

/-- The releases owed and the exits: the kind's failure verdict as
the value of the branch the verifier requires and the source makes
unreachable; in a function, an early return of nothing. -/
def deadBranch (c : LCtx) (sp : Span) : List LIR.Stmt :=
  let verdict (vt : LIR.Ty) : List LIR.Stmt :=
    match c.kind with
    | some decl =>
      let (_, w) := intParts vt
      let v : Nat := match decl.defaultExit with
        | .verdict name => (decl.verdicts.lookup name).getD 0
        | .value v => Machine.toNatMod v w
      [.ret sp (some (lit w v))]
    | none => [.ret sp none]
  match c.ret with
  | .program vt | .handler vt => verdict vt
  | .fn (some t) false => [.ret sp (some (zeroOf t))]
  | .fn _ _ => [.ret sp none]

mutual

partial def lowerExpr (c : LCtx) (sp : Span) (e : Expr) (expected : Option Ty) :
    LM LE := do
  match e with
  | .lit _ v _ =>
    let t ← match expected with
      | some t => lty c t
      | none => pure .u64
    let (_, w) := intParts t
    return { pre := [], e := lit w v, ty := t }
  | .char _ ch => return { pre := [], e := lit 8 ch.toNat, ty := .u8 }
  | .bool _ b => return { pre := [], e := lit 8 (if b then 1 else 0), ty := .u8 }
  | .str .. => lerr "a string outside `printk`"
  | .var _ x =>
    match c.env.local? x with
    | some l =>
      let x' ← lname c x
      match l.ty with
      | .ref .. | .view .. | .own .. => return { pre := [], e := .addr (.var x'), ty := .ptr }
      | t => return { pre := [], e := .var x', ty := ← lty c t }
    | none =>
      if let some d := c.env.consts.find? (·.name == x) then
        lowerExpr c sp d.value (d.ty <|> expected)
      else if let some d := c.env.config? x then
        match d.init with
        | some i => lowerExpr c sp i (some d.ty)
        | none => lerr s!"`{x}` has no value for this build"
      else if let some (decl, n) := c.kind.bind fun decl =>
          (decl.verdicts.lookup x).map (decl, ·) then
        let vt ← lty c decl.verdictTy
        return { pre := [], e := lit (intParts vt).2 n, ty := vt }
      else if let some d := c.env.interface.const? x then
        lowerExpr c sp d.value (d.ty <|> expected)
      else lerr s!"unknown name `{x}`"
  | .arith _ op l r =>
    let tn ← normTy c (← operandTy c l r expected)
    let t ← lty c tn
    let (s, w) := intParts t
    let L ← lowerExpr c sp l (some tn)
    let R ← lowerExpr c sp r (some tn)
    let (L, R) ← combine sp L R
    return { pre := L.pre ++ R.pre, e := .arith op s w L.e R.e, ty := t }
  | .cmp .. | .not .. | .and .. | .or .. => boolValue c sp e
  | .cast _ e' t =>
    let src ← if isPoly c e' then pure Interface.tU64 else synthTy c e'
    let srcN ← normTy c src
    let E ← lowerExpr c sp e' (some srcN)
    let tgt ← lty c t
    if E.ty == tgt then return E
    let (s0, w0) := intParts E.ty
    let (s1, w1) := intParts tgt
    return { pre := E.pre, e := .cast s0 w0 s1 w1 E.e, ty := tgt }
  | .hton _ e' =>
    let w ← if isPoly c e' then
        match expected with
        | some t =>
          match ← normTy c t with
          | .be _ w => pure w
          | _ => lerr "`hton` outside a byte-order context"
        | none => lerr "the width of `hton` is not determined"
      else
        match ← normTy c (← synthTy c e') with
        | .int _ _ w => pure w
        | _ => lerr "`hton` of a value that is not an unsigned integer"
    let E ← lowerExpr c sp e' (some (.int sp false w))
    let e'' := match E.e with
      | .lit _ k => lit w (Machine.bswap w k)
      | e => .bswap w e
    return { pre := E.pre, e := e'', ty := .int false w }
  | .ntoh _ e' =>
    let E ← lowerExpr c sp e' none
    let (_, w) := intParts E.ty
    return { pre := E.pre, e := .bswap w E.e, ty := .int false w }
  | .read _ p =>
    let (pre, r) ← lowerPlace c sp p
    match r with
    | .local x t => return { pre, e := .var x, ty := ← lty c t }
    | .ctx f t => return { pre, e := .ctx f, ty := ← lty c t }
    | .mem a t =>
      let lt ← lty c t
      let (s, w) := intParts lt
      return { pre, e := .load s w a, ty := lt }
  | .size _ t =>
    let n ← sizeOfTy c t
    let lt ← match expected with
      | some t => lty c t
      | none => pure .u64
    return { pre := [], e := lit (intParts lt).2 n, ty := lt }
  | .move _ x =>
    modify fun s => { s with moved := s.moved ++ [x] }
    return { pre := [], e := .addr (.var (← lname c x)), ty := .ptr }
  | .call _ f args =>
    let (pre, r) ← lowerCall c sp f args none
    match r with
    | some (e, t) => return { pre, e, ty := t }
    | none => lerr s!"`{f}` yields nothing"
  | .errno _ =>
    match c.errno with
    | some err => return { pre := [], e := .var err, ty := .u32 }
    | none => lerr "`errno` outside the `else` of a helper call"
  | .invalid _ m => lerr m

/-- A boolean in value position: a byte, 0 unless the tests set it. -/
partial def boolValue (c : LCtx) (sp : Span) (e : Expr) : LM LE := do
  let b ← freshName "b"
  let sets ← boolInto c sp e b
  return { pre := .«let» sp b .u8 (lit 8 0) :: sets, e := .var b, ty := .u8 }

/-- The statements that set the byte `b` to 1 when `e` holds, with
`&&`, `||`, and `!` as nested tests in short-circuit order. -/
partial def boolInto (c : LCtx) (sp : Span) (e : Expr) (b : String) :
    LM (List LIR.Stmt) := do
  let set1 : LIR.Stmt := .assign sp b (lit 8 1)
  match e with
  | .and _ l r =>
    let (pl, cl) ← lowerCond c sp l
    return pl ++ [.ite sp cl (← boolInto c sp r b) []]
  | .or _ l r =>
    let (pl, cl) ← lowerCond c sp l
    return pl ++ [.ite sp cl [set1] (← boolInto c sp r b)]
  | .not _ e' =>
    match e' with
    | .cmp .. | .not .. | .and .. | .or .. | .bool .. => boolInto c sp (Koit.Facts.Facts.negate e') b
    | _ =>
      let (pre, cnd) ← lowerCond c sp e'
      return pre ++ [.ite sp (negCond cnd) [set1] []]
  | e =>
    let (pre, cnd) ← lowerCond c sp e
    return pre ++ [.ite sp cnd [set1] []]

/-- A condition as one comparison, with the statements it needs: a
comparison directly, a negation by the opposite comparison, and a
compound or a boolean value tested against zero. -/
partial def lowerCond (c : LCtx) (sp : Span) (e : Expr) : LM (List LIR.Stmt × LIR.Cond) := do
  match e with
  | .cmp _ op l r =>
    let tn ← normTy c (← operandTy c l r none)
    let (s, w) ← match tn with
      | .int _ s w => pure (s, w)
      | .be _ w => pure (false, w)
      -- an enumeration compares as the unsigned integer it is
      | .enum _ n =>
        match c.env.interface.enum? n with
        | some decl => pure (false, decl.width)
        | none => lerr s!"unknown enumeration `{n}`"
      | _ => lerr "a comparison of values that are not integers"
    let L ← lowerExpr c sp l (some tn)
    let R ← lowerExpr c sp r (some tn)
    let (L, R) ← combine sp L R
    return (L.pre ++ R.pre, { op, signed := s, w, l := L.e, r := R.e })
  | .not _ e' =>
    let (pre, cnd) ← lowerCond c sp e'
    return (pre, negCond cnd)
  | .and .. | .or .. =>
    let E ← boolValue c sp e
    return (E.pre, { op := .ne, signed := false, w := 8, l := E.e, r := lit 8 0 })
  | .bool _ b =>
    return ([], { op := .ne, signed := false, w := 8, l := lit 8 (if b then 1 else 0), r := lit 8 0 })
  | e =>
    let E ← lowerExpr c sp e none
    let (s, w) := intParts E.ty
    return (E.pre, { op := .ne, signed := s, w, l := E.e, r := lit w 0 })

/-- A place as an address, a scalar local, or a context field, with
the statements a lookup by helper needs. -/
partial def lowerPlace (c : LCtx) (sp : Span) (p : Place) : LM (List LIR.Stmt × PRef) := do
  match p with
  | .var _ x =>
    match c.env.local? x with
    | some l =>
      let x' ← lname c x
      match l.ty with
      | .ref _ t | .view _ t | .own _ t => return ([], .mem (.var x') t)
      | t => return ([], .local x' t)
    | none => lerr s!"`{x}` is not a place"
  | .field _ (.var _ "ctx") f =>
    match c.kind.bind fun decl => decl.ctx.find? (·.name == f) with
    | some cf => return ([], .ctx f cf.ty)
    | none => lerr s!"the context has no field `{f}`"
  -- an element of an array context field is the declaration `f[k]`
  | .index _ (.field _ (.var _ "ctx") f) (.lit _ k _) =>
    match c.kind.bind fun decl => decl.ctx.find? (·.name == s!"{f}[{k}]") with
    | some cf => return ([], .ctx cf.name cf.ty)
    | none => lerr s!"the context has no field `{f}[{k}]`"
  | .field _ q f =>
    let (pre, r) ← lowerPlace c sp q
    match r with
    | .mem a t =>
      let fields ← match ← normTy c t with
        | .struct _ fields => pure fields
        | _ => lerr s!"`{q.print}` has no fields"
      let some fd := fields.find? (·.name == f) | lerr s!"no field `{f}`"
      let some o ← liftC (Check.fieldOffset c.env t f) | lerr s!"no field `{f}`"
      return (pre, .mem (plusAddr a o) fd.ty)
    | _ => lerr s!"`{q.print}` has no fields"
  | .index _ q i =>
    let (pre, r) ← lowerPlace c sp q
    match r with
    | .mem a t =>
      let (elem, _) ← match ← normTy c t with
        | .array _ elem n => pure (elem, n)
        | _ => lerr s!"`{q.print}` is not an array"
      let esz ← sizeOfTy c elem
      let it ← if isPoly c i then pure Interface.tU64 else synthTy c i
      let I ← lowerExpr c sp i (some it)
      match I.e with
      | .lit _ k => return (pre ++ I.pre, .mem (plusAddr a (k * esz)) elem)
      | e =>
        unless inPacket c q do return (pre ++ I.pre, .mem (.index a e esz) elem)
        -- the element's address bound once, and the test the verifier
        -- requires on that very pointer, whose branch the view's window
        -- and the index demand make dead
        let el ← freshName "el"
        let test : LIR.Cond := { op := .gt, signed := false, w := 64,
                                 l := .addr (plusAddr (.var el) esz), r := .addr .pktEnd }
        return (pre ++ I.pre ++
          [.«let» sp el .ptr (.addr (.index a e esz)), .ite sp test (deadBranch c sp) []],
          .mem (.var el) elem)
    | _ => lerr s!"`{q.print}` is not an array"
  | .slot _ m i =>
    let some d := c.env.map? m | lerr s!"unknown map `{m}`"
    let v ← match d.kind with
      | .array _ v | .percpu _ v => pure v
      | _ => lerr s!"`{m}` has no slots"
    if c.direct.contains m then return ([], .mem (.mapval m 0) v)
    -- the lookup by helper, with the branch the verifier requires
    let it ← if isPoly c i then pure Interface.tU64 else synthTy c i
    let I ← lowerExpr c sp i (some it)
    let idx := if I.ty == .u32 then I.e else
      let (s, w) := intParts I.ty
      LIR.Expr.cast s w false 32 I.e
    let k ← freshName "k"
    let r ← freshName "r"
    let pre := I.pre ++
      [.frame sp k 4 (some Interface.tU32), .store sp 32 (.var k) idx,
       .builtin sp (some r) (.lookup m) [.addr (.var k)],
       .ite sp { op := .eq, signed := false, w := 64, l := .var r, r := lit 64 0 }
         (deadBranch c sp) []]
    return (pre, .mem (.var r) v)
  | .deref _ (.var _ x) =>
    match c.env.local? x with
    | some l =>
      let x' ← lname c x
      match l.ty with
      | .ref _ t | .view _ t | .own _ t => return ([], .mem (.var x') t)
      | _ => lerr s!"`*{x}` of a scalar"
    | none => lerr s!"unknown name `{x}`"
  | .deref .. => lerr "`*` applies to a name"
  | .invalid _ m => lerr m

/-- The arguments of a call against its parameters: a scalar by
value at the parameter's type, a place by its address, a moved name
by its address. -/
partial def lowerArgs (c : LCtx) (sp : Span) (params : List Param) (args : List Arg) :
    LM (List LIR.Stmt × List LIR.Expr) := do
  let mut les : List LE := []
  for (p, a) in params.zip args do
    let pn ← normTy c p.ty
    match pn, a with
    | .ref .., .place q | .view .., .place q =>
      let (pre, r) ← lowerPlace c sp q
      match r with
      | .mem addr _ => les := les ++ [{ pre, e := .addr addr, ty := .ptr }]
      | _ => lerr s!"`{q.print}` is not an aggregate place"
    | .own .., .val e => les := les ++ [← lowerExpr c sp e none]
    | _, .val e => les := les ++ [← lowerExpr c sp e (some pn)]
    | _, .place q =>
      let E ← lowerExpr c sp (.read q.span q) (some pn)
      les := les ++ [E]
    | _, .map .. => pure ()
  sequence sp les

/-- The arguments of a builtin typed by rule: scalars at their own
types, places by address. -/
partial def lowerLooseArgs (c : LCtx) (sp : Span) (args : List Arg) :
    LM (List LIR.Stmt × List LIR.Expr) := do
  let mut les : List LE := []
  for a in args do
    match a with
    | .val e => les := les ++ [← lowerExpr c sp e none]
    | .place q =>
      let (pre, r) ← lowerPlace c sp q
      match r with
      | .mem addr t =>
        -- a scalar place is read, an aggregate passed by address
        if (← normTy c t).isScalar then
          let lt ← lty c t
          let (s, w) := intParts lt
          les := les ++ [{ pre, e := .load s w addr, ty := lt }]
        else les := les ++ [{ pre, e := .addr addr, ty := .ptr }]
      | .local x t => les := les ++ [{ pre, e := .var x, ty := ← lty c t }]
      | .ctx f t => les := les ++ [{ pre, e := .ctx f, ty := ← lty c t }]
    | .map .. => pure ()
  sequence sp les

/-- A call in a value or statement position: a function of the unit
as `call`, a kernel function as a `kernel` statement whose `r0` is
cast to the declaration's result, a builtin as itself. `binder` names the
result when the source bound it. -/
partial def lowerCall (c : LCtx) (sp : Span) (f : String) (args : List Arg)
    (binder : Option String) : LM (List LIR.Stmt × Option (LIR.Expr × LIR.Ty)) := do
  if let some d := c.fns.find? (·.name == f) then
    let (pre, args') ← lowerArgs c sp d.params args
    let unwind ← if d.fails then some <$> releasesAll c sp else pure none
    match d.ret with
    | some t =>
      let base := match t with
        | .refined _ _ base _ => base
        | t => t
      let lt ← lty c base
      let x ← match binder with
        | some x => pure x
        | none => freshName "t"
      return (pre ++ [.call sp (some x) f args' unwind none], some (.var x, lt))
    | none => return (pre ++ [.call sp none f args' unwind none], none)
  let some decl := c.env.interface.call? f | lerr s!"unknown function `{f}`"
  match decl.sig with
  | .fn params ret =>
    let (pre, args') ← lowerArgs c sp params args
    let t ← freshName "t"
    let call : LIR.Stmt := .kernel sp (some t) f args'
    match ret with
    | some rt =>
      let base := match rt with
        | .refined _ _ base _ => base
        | t => t
      let lt ← lty c base
      let x ← match binder with
        | some x => pure x
        | none => freshName "t"
      let e : LIR.Expr := match lt with
        | .ptr => .var t
        | .int s w => .cast true 64 s w (.var t)
      return (pre ++ [call, .«let» sp x lt e], some (.var x, lt))
    | none => return (pre ++ [.kernel sp none f args'], none)
  | .builtin =>
    match f, args with
    | "printk", .val (.str _ fmt) :: rest =>
      let (pre, args') ← lowerLooseArgs c sp rest
      return (pre ++ [.builtin sp none (.printk fmt) args'], none)
    | "copy", [.place dst, .place src] =>
      let (pd, rd) ← lowerPlace c sp dst
      let (ps, rs) ← lowerPlace c sp src
      match rd, rs with
      | .mem da dt, .mem sa _ =>
        let n ← sizeOfTy c dt
        return (pd ++ ps ++ [.builtin sp none (.copy n) [.addr da, .addr sa]], none)
      | _, _ => lerr "`copy` takes two aggregate places"
    | "fill", [.place dst, .val b] =>
      let (pd, rd) ← lowerPlace c sp dst
      let B ← lowerExpr c sp b (some Interface.tU8)
      match rd with
      | .mem da dt =>
        let n ← sizeOfTy c dt
        return (pd ++ B.pre ++ [.builtin sp none (.fill n) [.addr da, B.e]], none)
      | _ => lerr "`fill` takes an aggregate place"
    | _, _ => lerr s!"`{f}` has no lowering in this position"

/-- The release of a resource, normally or abnormally: the builtin of
its declaration, or the kernel function its exit clause names. -/
partial def releaseStmt (c : LCtx) (sp : Span) (decl : ResourceDecl) (normal : Bool)
    (obj : Option LIR.Addr) : LM LIR.Stmt := do
  let objArgs := match obj with
    | some a => [LIR.Expr.addr a]
    | none => []
  match Machine.releaseOf c.env.interface decl normal with
  | .ok .leave => return .builtin sp none (.leave decl.res) []
  | .ok .unlock => return .builtin sp none .unlock objArgs
  | .ok .submit => return .builtin sp none .submit objArgs
  | .ok .discard => return .builtin sp none .discard objArgs
  | .ok (.kernel crow) => return .kernel sp none crow.name objArgs
  | .error m => lerr m

/-- The abnormal releases owed by every action in `ρ` up to the
construct `stop` selects, innermost first, for the names not moved. -/
partial def releasesUpTo (c : LCtx) (sp : Span) (stop : Marker → Bool) :
    LM (List LIR.Stmt) := do
  let rec go : List Scope → LM (List LIR.Stmt)
    | [] => pure []
    | .construct m :: rest => if stop m then pure [] else go rest
    | .release decl obj name :: rest => do
      let rest' ← go rest
      match name with
      | some x => if c.mu.contains x then pure rest' else
          pure ((← releaseStmt c sp decl false obj) :: rest')
      | none => pure ((← releaseStmt c sp decl false obj) :: rest')
  go c.rho

/-- Every release owed: at `return`, `raise`, and in an `unwind`. -/
partial def releasesAll (c : LCtx) (sp : Span) : LM (List LIR.Stmt) :=
  releasesUpTo c sp fun _ => false

end

/-- The depth of the `br` that leaves the construct `stop` selects,
counting the constructs from the innermost. -/
def depthTo (c : LCtx) (stop : Marker → Bool) : LM Nat := do
  let rec go : List Scope → Nat → LM Nat
    | [], _ => lerr "a loop exit outside a loop"
    | .construct m :: rest, n => if stop m then pure n else go rest (n + 1)
    | .release .. :: rest, n => go rest n
  go c.rho 0

/-! ### Statements -/

/-- A Core local entering scope: its type in `Γ` and its LIR name. -/
def bindLocal (c : LCtx) (x : String) (t : Ty) (mutable : Bool) (origin : Origin)
    (x' : String) : LCtx :=
  { c with env := c.env.bind { name := x, ty := t, mutable, origin },
           names := (x, x') :: c.names }

def pushConstruct (c : LCtx) (m : Marker) : LCtx :=
  { c with rho := .construct m :: c.rho }

/-- The moves the statement's own expressions made, taken from the
translation state into `μ`. -/
def takeMoves (c : LCtx) : LM LCtx := do
  let s ← get
  set { s with moved := [] }
  return { c with mu := c.mu ++ s.moved }

/-- The type a fallible operation binds to its name, as the checker
gives it. -/
def boundTy (c : LCtx) (f : Fallible) : LM (Option Ty × Origin) := do
  match f with
  | .view s _ t => return (some (.view s t), .pkt)
  | .lookup s m _ =>
    match c.env.map? m with
    | some { kind := .hash _ _ v, .. } => return (some (.ref s v), .map m)
    | _ => lerr s!"`{m}` is not a hash map"
  | .loadw s (.field _ q fname) =>
    let info ← liftC (Check.placeTy c.env c.K q)
    match ← normTy c info.ty with
    | .struct _ fields =>
      match fields.find? (·.name == fname) with
      | some fd => return (some (.refined s fname fd.ty (fd.pred.getD (.bool s true))), .stack)
      | none => lerr s!"no field `{fname}`"
    | _ => lerr "a marked load reads a field"
  | .loadw .. => lerr "a marked load reads a field"
  | .call _ h _ =>
    match c.env.interface.call? h with
    | some decl =>
      match decl.sig with
      | .fn _ ret => return (ret, .stack)
      | .builtin => return (none, .stack)
    | none => return (none, .stack)
  | .callopt _ f _ =>
    match c.fns.find? (·.name == f) with
    | some d =>
      match d.ret with
      | some (.opt _ t) => return (some t, .stack)
      | _ => lerr s!"`{f}` returns no optional"
    | none => lerr s!"unknown function `{f}`"
  | .coerce _ _ t => return (some t, .stack)
  | .tail .. => return (none, .stack)
  | .acquire s r f t args =>
    match c.env.interface.resource? r with
    | some decl =>
      match decl.arg with
      | .place _ | .scope => return (none, .kernel)
      | .call =>
        if f == "reserve" then
          match t with
          | some t => return (some (.own s t), .kernel)
          | none => lerr "`reserve` takes a record type"
        else
          match c.env.interface.call? f with
          | some decl =>
            match decl.sig with
            | .fn _ ret => return (ret, .kernel)
            | .builtin => lerr s!"`{f}` has no signature"
          | none => lerr s!"unknown function `{f}`"
    | none =>
      let _ := args
      lerr s!"no declaration for `{r}`"

mutual

/-- A block: its statements in order, `Γ`, the names, and `μ`
threaded through; the `μ` after it, for the statement that owns
it. -/
partial def lowerStmts (c : LCtx) : List Stmt → LM (List LIR.Stmt × List String)
  | [] => return ([], c.mu)
  | s :: rest => do
    let (ss, c') ← lowerStmt c s
    let (rest', mu) ← lowerStmts c' rest
    return (ss ++ rest', mu)

/-- One statement, and the context for the statements after it. -/
partial def lowerStmt (c : LCtx) (s : Stmt) : LM (List LIR.Stmt × LCtx) := do
  let sp := s.span
  match s with
  | .«let» _ mutable x ty init =>
    if x == "_" then
      match init with
      | .expr (.call s' f args) =>
        let (pre, _) ← lowerCall c s' f args none
        let c ← takeMoves c
        return (pre, c)
      | _ => lerr "a bare statement is a call"
    match init with
    | .expr e =>
      let t ← match ty with
        | some t => pure t
        | none => synthTy c e
      let base := match t with
        | .refined _ _ b _ => b
        | t => t
      let x' ← nameFor x
      let E ← lowerExpr c sp e (some base)
      let c ← takeMoves c
      let c := bindLocal c x t mutable .stack x'
      return (E.pre ++ [.«let» sp x' E.ty E.e], c)
    | .place p =>
      let (pre, r) ← lowerPlace c sp p
      let x' ← nameFor x
      match r with
      | .local y t =>
        let c := bindLocal c x (ty.getD t) mutable .stack x'
        return (pre ++ [.«let» sp x' (← lty c t) (.var y)], c)
      | .ctx f t =>
        let c := bindLocal c x (ty.getD t) mutable .ctx x'
        return (pre ++ [.«let» sp x' (← lty c t) (.ctx f)], c)
      | .mem a t =>
        let tn ← normTy c t
        if tn.isScalar then
          let lt ← lty c t
          let (sg, w) := intParts lt
          let c := bindLocal c x (ty.getD t) mutable .stack x'
          return (pre ++ [.«let» sp x' lt (.load sg w a)], c)
        else
          let info ← liftC (Check.placeTy c.env c.K p)
          let pty := if info.origin == .pkt then Ty.view sp t else Ty.ref sp t
          let c := bindLocal c x pty false info.origin x'
          return (pre ++ [.«let» sp x' .ptr (.addr a)], c)
    | .lit ls fields =>
      let st ← liftC (Check.structForLiteral c.env ls ty fields)
      let n ← sizeOfTy c st
      let x' ← nameFor x
      let mut stores : List LIR.Stmt := []
      for fi in fields do
        let some o ← liftC (Check.fieldOffset c.env st fi.name) | lerr s!"no field `{fi.name}`"
        let ft ← match ← normTy c st with
          | .struct _ fs => match fs.find? (·.name == fi.name) with
            | some fd => pure fd.ty
            | none => lerr s!"no field `{fi.name}`"
          | _ => lerr "a struct literal has a struct type"
        let E ← lowerExpr c sp fi.value (some ft)
        let (_, w) := intParts E.ty
        stores := stores ++ E.pre ++ [.store sp w (plusAddr (.var x') o) E.e]
      let c ← takeMoves c
      let c := bindLocal c x (.ref sp st) false .stack x'
      return (.frame sp x' n (some st) :: stores, c)
  | .assign _ p e =>
    let (pp, r) ← lowerPlace c sp p
    let t := match r with
      | .local _ t | .ctx _ t | .mem _ t => t
    let base := match t with
      | .refined _ _ b _ => b
      | t => t
    let E ← lowerExpr c sp e (some base)
    let c ← takeMoves c
    let store : LIR.Stmt ← match r with
      | .local x _ => pure (.assign sp x E.e)
      | .ctx f _ => pure (.ctxStore sp f E.e)
      | .mem a _ => pure (.store sp (intParts E.ty).2 a E.e)
    -- the value first, then the place, as the assignment rule
    -- evaluates them
    return (E.pre ++ pp ++ [store], c)
  | .ite _ cond thn els =>
    let (pre, cnd) ← lowerCond c sp cond
    let c ← takeMoves c
    let (t', muT) ← lowerStmts c thn
    let (e', _) ← lowerStmts c els
    return (pre ++ [.ite sp cnd t' e'], { c with mu := muT })
  | .loop _ n body =>
    let N ← lowerExpr c sp n (some Interface.tU64)
    let cnt ← freshName "i"
    let cb := (pushConstruct (pushConstruct (pushConstruct c .exitBlock) .loop) .bodyBlock)
    let (body', _) ← lowerStmts cb body
    let test : LIR.Cond := { op := .ge, signed := false, w := 64, l := .var cnt, r := N.e }
    return (N.pre ++
      [.block sp [.«let» sp cnt .u64 (lit 64 0),
        .loop sp [.ite sp test [.br sp 1] [], .block sp body',
                  .assign sp cnt (.arith .add false 64 (.var cnt) (lit 64 1))]]], c)
  | .«for» _ x lo hi body =>
    let L ← lowerExpr c sp lo (some Interface.tU64)
    let H ← lowerExpr c sp hi (some Interface.tU64)
    let (L, H) ← combine sp L H
    let x' ← nameFor x
    let hi' ← freshName "hi"
    let cb := bindLocal (pushConstruct (pushConstruct (pushConstruct c .exitBlock) .loop) .bodyBlock)
      x (.int sp false 64) false .stack x'
    let (body', _) ← lowerStmts cb body
    let test : LIR.Cond := { op := .ge, signed := false, w := 64, l := .var x', r := .var hi' }
    return (L.pre ++ H.pre ++
      [.block sp [.«let» sp x' .u64 L.e, .«let» sp hi' .u64 H.e,
        .loop sp [.ite sp test [.br sp 1] [], .block sp body',
                  .assign sp x' (.arith .add false 64 (.var x') (lit 64 1))]]], c)
  | .brk _ =>
    let rel ← releasesUpTo c sp (· == .exitBlock)
    let n ← depthTo c (· == .exitBlock)
    return (rel ++ [.br sp n], c)
  | .cont _ =>
    let rel ← releasesUpTo c sp (· == .bodyBlock)
    let n ← depthTo c (· == .bodyBlock)
    return (rel ++ [.br sp n], c)
  | .ret _ none =>
    let rel ← releasesAll c sp
    return (rel ++ [.ret sp none], c)
  | .ret _ (some e) =>
    let rt ← match c.ret with
      | .program vt | .handler vt => pure vt
      | .fn (some t) _ => pure t
      | .fn none _ => lerr "`return e` in a function without a result"
    let expected : Ty := match rt with
      | .int s w => .int sp s w
      | .ptr => .int sp false 64
    let E ← lowerExpr c sp e (some expected)
    let c ← takeMoves c
    let rel ← releasesAll c sp
    let e' := if E.ty == rt then E.e else
      let (s0, w0) := intParts E.ty
      let (s1, w1) := intParts rt
      LIR.Expr.cast s0 w0 s1 w1 E.e
    return (E.pre ++ rel ++ [.ret sp (some e')], c)
  | .raise _ k e =>
    let E ← lowerExpr c sp e (some Interface.tU32)
    let c ← takeMoves c
    let rel ← releasesAll c sp
    return (E.pre ++ rel ++ [.raise sp k E.e], c)
  | .«try» _ x f thn els _ => lowerTry c sp x f thn els
  | .hold _ r x acq body els => lowerHold c sp r x acq body els
  | .atomic _ x op p args =>
    let (pp, r) ← lowerPlace c sp p
    let t := match r with
      | .local _ t | .ctx _ t | .mem _ t => t
    let tn ← normTy c t
    let lt ← lty c tn
    let (sg, w) := intParts lt
    let mut les : List LE := []
    for a in args do
      les := les ++ [← lowerExpr c sp a (some tn)]
    let (pa, args') ← sequence sp les
    let c ← takeMoves c
    match r with
    | .mem a _ =>
      let x' ← match x with
        | some n => some <$> nameFor n
        | none => pure none
      let c := match x, x' with
        | some n, some n' => bindLocal c n tn false .stack n'
        | _, _ => c
      return (pp ++ pa ++ [.builtin sp x' (.atomic op sg w x.isSome) (.addr a :: args')], c)
    | .local y _ =>
      -- a local scalar is this program's alone: the read-modify-write
      -- is a read and a store
      let old ← match x with
        | some n => nameFor n
        | none => freshName "t"
      let arg0 := args'.headD (lit w 0)
      let arg1 := (args'[1]?).getD (lit w 0)
      let new : List LIR.Stmt := match op with
        | .add => [.assign sp y (.arith .add sg w (.var old) arg0)]
        | .band => [.assign sp y (.arith .band sg w (.var old) arg0)]
        | .bor => [.assign sp y (.arith .bor sg w (.var old) arg0)]
        | .bxor => [.assign sp y (.arith .bxor sg w (.var old) arg0)]
        | .xchg => [.assign sp y arg0]
        | .cmpxchg =>
          [.ite sp { op := .eq, signed := sg, w, l := .var old, r := arg0 }
            [.assign sp y arg1] []]
      let c := match x with
        | some n => bindLocal c n tn false .stack old
        | none => c
      return (pp ++ pa ++ [.«let» sp old lt (.var y)] ++ new, c)
    | .ctx .. => lerr "an atomic update on a context field"
  | .invalid _ m => lerr m

/-- `try x = F then thn else els`: the marker's test, the bound name
in the then-branch. -/
partial def lowerTry (c : LCtx) (sp : Span) (x : String) (f : Fallible)
    (thn els : List Stmt) : LM (List LIR.Stmt × LCtx) := do
  let (bt, origin) ← boundTy c f
  -- the then-branch's context, with `x` bound when it binds anything
  let bindX (c : LCtx) (x' : String) : LCtx :=
    match bt with
    | some t => if x == "_" then c else bindLocal c x t false origin x'
    | none => c
  let zero64 : LIR.Cond := { op := .eq, signed := false, w := 64, l := .var "", r := lit 64 0 }
  match f with
  | .tail _ m i =>
    -- the call, then the code for a call not taken; a taken call
    -- never returns, so nothing follows for it
    let I ← lowerExpr c sp i (some Interface.tU32)
    let c ← takeMoves c
    let (els', _) ← lowerStmts c els
    return (I.pre ++ [.builtin sp none (.tail m) [I.e]] ++ els', c)
  | .view _ off t =>
    let O ← lowerExpr c sp off (some Interface.tU64)
    let n ← sizeOfTy c t
    let h ← if x == "_" then freshName "h" else nameFor x
    let c ← takeMoves c
    let (thn', muT) ← lowerStmts (bindX c h) thn
    let (els', _) ← lowerStmts c els
    let test : LIR.Cond := { op := .gt, signed := false, w := 64,
                             l := .addr (plusAddr (.var h) n), r := .addr .pktEnd }
    return (O.pre ++ [.«let» sp h .ptr (.addr (.index .pktData O.e 1)), .ite sp test els' thn'],
            { c with mu := muT })
  | .lookup _ m k =>
    let (kp, kr) ← lowerPlace c sp k
    let ka ← match kr with
      | .mem a _ => pure a
      | _ => lerr "a key is an aggregate place"
    let r ← if x == "_" then freshName "r" else nameFor x
    let c ← takeMoves c
    let (thn', muT) ← lowerStmts (bindX c r) thn
    let (els', _) ← lowerStmts c els
    return (kp ++ [.builtin sp (some r) (.lookup m) [.addr ka],
                   .ite sp { zero64 with l := .var r } els' thn'], { c with mu := muT })
  | .loadw _ (.field _ q fname) =>
    let (qp, qr) ← lowerPlace c sp q
    let (a, qt) ← match qr with
      | .mem a t => pure (a, t)
      | _ => lerr "a marked load reads a field of an aggregate"
    let fields ← match ← normTy c qt with
      | .struct _ fs => pure fs
      | _ => lerr "a marked load reads a field"
    let some fd := fields.find? (·.name == fname) | lerr s!"no field `{fname}`"
    let some o ← liftC (Check.fieldOffset c.env qt fname) | lerr s!"no field `{fname}`"
    let lt ← lty c fd.ty
    let (sg, w) := intParts lt
    let x' ← if x == "_" then freshName "t" else nameFor x
    let load : LIR.Stmt := .«let» sp x' lt (.load sg w (plusAddr a o))
    -- the siblings the predicate mentions, each loaded once
    let pred := fd.pred.getD (.bool sp true)
    let mentioned := (pred.atoms.filterMap Place.root).eraseDups
    let mut sibs : List LIR.Stmt := []
    let mut cp : LCtx := bindLocal c x fd.ty false .stack x'
    for g in fields do
      if g.name != fname && mentioned.contains g.name then
        let some og ← liftC (Check.fieldOffset c.env qt g.name) | lerr s!"no field `{g.name}`"
        let gt ← lty c g.ty
        let (gs, gw) := intParts gt
        let g' ← freshName g.name
        sibs := sibs ++ [.«let» sp g' gt (.load gs gw (plusAddr a og))]
        cp := bindLocal cp g.name g.ty false .stack g'
    let (pp, cnd) ← lowerCond cp sp (pred.subst fname (.var sp x))
    let c ← takeMoves c
    let (thn', muT) ← lowerStmts (bindX c x') thn
    let (els', _) ← lowerStmts c els
    return (qp ++ [load] ++ sibs ++ pp ++ [.ite sp cnd thn' els'], { c with mu := muT })
  | .loadw .. => lerr "a marked load reads a field"
  | .coerce _ e (.refined _ v base pred) =>
    if x == "_" then
      -- `check P`: the predicate is the test
      let (pp, cnd) ← lowerCond c sp e
      let c ← takeMoves c
      let (thn', muT) ← lowerStmts c thn
      let (els', _) ← lowerStmts c els
      return (pp ++ [.ite sp cnd thn' els'], { c with mu := muT })
    let E ← lowerExpr c sp e (some base)
    let x' ← nameFor x
    let cp := bindLocal c x base false .stack x'
    let (pp, cnd) ← lowerCond cp sp (pred.subst v (.var sp x))
    let c ← takeMoves c
    let (thn', muT) ← lowerStmts (bindX c x') thn
    let (els', _) ← lowerStmts c els
    return (E.pre ++ [.«let» sp x' E.ty E.e] ++ pp ++ [.ite sp cnd thn' els'],
            { c with mu := muT })
  | .coerce .. => lerr "a coercion targets a refinement type"
  | .call _ h args =>
    let some decl := c.env.interface.call? h | lerr s!"unknown function `{h}`"
    match decl.sig with
    | .fn params ret =>
      let (pre, args') ← lowerArgs c sp params args
      let t ← freshName "t"
      let call : LIR.Stmt := .kernel sp (some t) h args'
      let c ← takeMoves c
      match LIR.rowResult decl with
      | .ptr =>
        -- a location result: null is the failure
        let x' ← if x == "_" then freshName "p" else nameFor x
        let (thn', muT) ← lowerStmts (bindX c x') thn
        let (els', _) ← lowerStmts c els
        return (pre ++ [.kernel sp (some x') h args', .ite sp { zero64 with l := .var x' } els' thn'],
                { c with mu := muT })
      | _ =>
        scalarFallible c sp x bt ret pre call t thn els
    | .builtin =>
      -- `insert` and `delete`, fallible builtins
      let b ← match h, args with
        | "insert", [.map _ m, _, _] => pure (LIR.Builtin.update m)
        | "delete", [.map _ m, _] => pure (LIR.Builtin.delete m)
        | _, _ => lerr s!"`{h}` has no fallible lowering"
      let (pre, args') ← lowerLooseArgs c sp args
      let t ← freshName "t"
      let call : LIR.Stmt := .builtin sp (some t) b args'
      let c ← takeMoves c
      scalarFallible c sp x bt none pre call t thn els
  | .callopt _ f args =>
    let some d := c.fns.find? (·.name == f) | lerr s!"unknown function `{f}`"
    let (pre, args') ← lowerArgs c sp d.params args
    let x' ← if x == "_" then freshName "t" else nameFor x
    let c ← takeMoves c
    let cb := pushConstruct c .plain
    let unwind ← if d.fails then some <$> releasesAll cb sp else pure none
    let (els', _) ← lowerStmts cb els
    let (thn', muT) ← lowerStmts (bindX cb x') thn
    return (pre ++ [.block sp
      (.call sp (some x') f args' unwind (some (els' ++ [.br sp 0])) :: thn')],
      { c with mu := muT })
  | .acquire .. => lerr "an acquisition outside `hold`"

/-- A fallible call whose failure is a negative return: the test, the
`err` local of the else-branch, the result cast to its type in the
then-branch. -/
partial def scalarFallible (c : LCtx) (sp : Span) (x : String) (bt : Option Ty)
    (ret : Option Ty) (pre : List LIR.Stmt) (call : LIR.Stmt) (t : String)
    (thn els : List Stmt) : LM (List LIR.Stmt × LCtx) := do
  let err ← freshName "err"
  let (els', _) ← lowerStmts { c with errno := some err } els
  let mut bindStmts : List LIR.Stmt := []
  let mut ct := c
  match x, ret, bt with
  | "_", _, _ => pure ()
  | x, some rt, some bt =>
    let base := match rt with
      | .refined _ _ b _ => b
      | t => t
    let lt ← lty c base
    let x' ← nameFor x
    let (s, w) := intParts lt
    bindStmts := [.«let» sp x' lt (.cast true 64 s w (.var t))]
    ct := bindLocal c x bt false .stack x'
  | x, _, _ => lerr s!"`{x}` binds nothing"
  let (thn', muT) ← lowerStmts ct thn
  let failed : LIR.Cond := { op := .lt, signed := true, w := 64, l := .var t, r := lit 64 0 }
  return (pre ++ [call, .ite sp failed
    (.«let» sp err .u32 (.cast true 64 false 32 (.var t)) :: els') (bindStmts ++ thn')],
    { c with mu := muT })

/-- `hold R x = acq then body else els`: the acquisition, the body in
a block under the release action, the normal release after it. -/
partial def lowerHold (c : LCtx) (sp : Span) (r : Resource) (x : Option String)
    (acq : Fallible) (body : List Stmt) (els : Option (List Stmt)) :
    LM (List LIR.Stmt × LCtx) := do
  let some decl := c.env.interface.resource? r | lerr s!"no declaration for `{r}`"
  let (bt, _) ← boundTy c acq
  let zero64 (x : String) : LIR.Cond :=
    { op := .eq, signed := false, w := 64, l := .var x, r := lit 64 0 }
  -- the body under the action, and whether the normal release runs
  let bodyUnder (c : LCtx) (obj : Option LIR.Addr) (x' : Option String) :
      LM (List LIR.Stmt × List String) := do
    let cb := match x, x', bt with
      | some n, some n', some t => bindLocal c n t false .kernel n'
      | _, _, _ => c
    let cb := pushConstruct { cb with rho := .release decl obj x :: cb.rho } .plain
    lowerStmts cb body
  match decl.arg, acq with
  | .place _, .acquire _ _ _ _ [.place p] =>
    let (pp, pr) ← lowerPlace c sp p
    let a ← match pr with
      | .mem a _ => pure a
      | _ => lerr "a lock is a place in a map value"
    let lk ← freshName "lk"
    let c ← takeMoves c
    let (body', mu) ← bodyUnder c (some (.var lk)) none
    return (pp ++ [.«let» sp lk .ptr (.addr a), .builtin sp none .lock [.addr (.var lk)],
                   .block sp body', .builtin sp none .unlock [.addr (.var lk)]],
            { c with mu })
  | .scope, _ =>
    let (body', mu) ← bodyUnder c none none
    return ([.builtin sp none (.enter r) [], .block sp body', .builtin sp none (.leave r) []],
            { c with mu })
  | .call, .acquire _ _ f t args =>
    let some n := x | lerr "a value-yielding acquisition binds a name"
    let x' ← nameFor n
    let (pre, acqStmt) ← if f == "reserve" then
        match t, args with
        | some t, [.map _ m] =>
          let sz ← sizeOfTy c t
          pure ([], LIR.Stmt.builtin sp (some x') (.reserve m sz) [])
        | _, _ => lerr "`reserve` takes a ring buffer and a record type"
      else
        match c.env.interface.call? f with
        | some decl =>
          match decl.sig with
          | .fn params _ =>
            let (pre, args') ← lowerArgs c sp params args
            pure (pre, LIR.Stmt.kernel sp (some x') f args')
          | .builtin => lerr s!"`{f}` has no signature"
        | none => lerr s!"unknown function `{f}`"
    let c ← takeMoves c
    let (body', mu) ← bodyUnder c (some (.var x')) (some x')
    let normal ← if mu.contains n then pure [] else
      pure [← releaseStmt c sp decl true (some (.var x'))]
    -- a refused reservation has no return code; the model's reason
    -- for it is `ENOMEM`, as Core's rule sets `errno`
    let (errDecl, ce) ← if decl.fails == some .failed_call then
        let err ← freshName "err"
        pure ([LIR.Stmt.«let» sp err .u32 (lit 32 (Machine.toNatMod (-12) 32))],
              { c with errno := some err })
      else pure ([], c)
    let (els', _) ← lowerStmts ce (els.getD [])
    return (pre ++ [acqStmt, .ite sp (zero64 x') (errDecl ++ els') (.block sp body' :: normal)],
            { c with mu := mu.filter (· != n) })
  | _, _ => lerr s!"`{Check.acqName acq}` does not fit the declaration of `{r}`"

end

/-! ### Functions, programs, units -/

/-- The context `synth` needs: a failing context with no facts, on
which every demand holds, since the checker has already decided
them. -/
def synthCtx : Ctx :=
  { mayFail := true, ret := .fn "" none, errnoOk := true,
    facts := Koit.Facts.Facts.empty.bot }

def resetNames : LM Unit := modify fun s => { s with used := [], counter := 0, moved := [] }

def lowerFn (env : Env) (fns : List Fn) (direct : List String) (d : Fn) : LM LIR.Fn := do
  resetNames
  let c0 : LCtx := { env := env.top, K := synthCtx, ret := .fn none false, kind := none,
                     direct, fns }
  let mut c := c0
  let mut params : List LIR.Param := []
  for p in d.params do
    let x' ← nameFor p.name
    match p.ty with
    | .ref _ t =>
      c := bindLocal c p.name p.ty false .param x'
      params := params ++ [{ name := x', ty := .ptr }]
      let _ := t
    | .view .. =>
      c := bindLocal c p.name p.ty false .pkt x'
      params := params ++ [{ name := x', ty := .ptr }]
    | t =>
      let ty := match p.pred with
        | some q => Ty.refined p.span p.name t q
        | none => t
      c := bindLocal c p.name ty false .stack x'
      params := params ++ [{ name := x', ty := ← lty c t }]
  let (ret, opt) ← match d.ret with
    | some (.opt _ t) => pure (some (← lty c t), true)
    | some (.refined _ _ base _) => pure (some (← lty c base), false)
    | some t => pure (some (← lty c t), false)
    | none => pure (none, false)
  let c1 := { c with ret := .fn ret opt }
  let (body, _) ← lowerStmts c1 d.body
  return { span := d.span, name := d.name, params, ret, opt, fails := d.fails, body,
           global := d.global }

def lowerProgram (env : Env) (fns : List Fn) (direct : List String) (p : Program) :
    LM LIR.Program := do
  let some decl := env.interface.kind? p.kind | lerr s!"unknown kind `{p.kind}`"
  resetNames
  let env := { env.top with kind := some decl }
  let c0 : LCtx := { env, K := synthCtx, ret := .program .u32, kind := some decl, direct, fns }
  let vt ← lty c0 decl.verdictTy
  let c := { c0 with ret := .program vt }
  let (body, _) ← lowerStmts c p.body
  let mut handlers : List LIR.Handler := []
  for h in p.handlers do
    resetNames
    let reason ← nameFor "reason"
    let ch := bindLocal { c with ret := .handler vt } "reason" Interface.tU32 false .stack reason
    let (hb, _) ← lowerStmts ch h.body
    handlers := handlers ++ [{ kind := h.kind, body := hb }]
  return { span := p.span, name := p.name, kind := p.kind, body, handlers }

def runLM (m : LM α) : Except String α := (m.run {}).map (·.1)

/-- A declaration's type with every array length a literal, for the
printers, which have no constants to evaluate. -/
partial def foldTy (env : Env) : Ty → Ty
  | .struct s fields =>
    .struct s (fields.map fun f => .mk f.span f.name (foldTy env f.ty) f.pred)
  | .array s elem n =>
    let n' := match env.evalConst n with
      | some v => Expr.lit n.span v.toNat (toString v.toNat)
      | none => n
    .array s (foldTy env elem) n'
  | .refined s v base p => .refined s v (foldTy env base) p
  | .ref s t => .ref s (foldTy env t)
  | .view s t => .view s (foldTy env t)
  | .own s t => .own s (foldTy env t)
  | .opt s t => .opt s (foldTy env t)
  | t => t

def foldMapDecl (env : Env) (d : MapDecl) : MapDecl :=
  let count (n : Expr) : Expr := match env.evalConst n with
    | some v => .lit n.span v.toNat (toString v.toNat)
    | none => n
  { d with kind := match d.kind with
      | .array n v => .array (count n) (foldTy env v)
      | .percpu n v => .percpu (count n) (foldTy env v)
      | .hash n k v => .hash (count n) (foldTy env k) (foldTy env v)
      | .ringbuf n => .ringbuf (count n)
      | .progArray n k => .progArray (count n) k }

/-- Pass B on a folded unit. -/
def lower (pre : Interface) (folded : Folded) : Except String LIR.CompUnit := do
  let u := folded.unit
  let env : Env := { interface := pre, license := u.license.map (·.2), types := u.types,
                     consts := u.consts, configs := u.configs, maps := u.maps,
                     fns := u.fns, contracts := u.contracts }
  let fns ← u.fns.mapM fun f => runLM (lowerFn env u.fns folded.direct f)
    |>.mapError (s!"lowering: " ++ ·)
  let programs ← u.programs.mapM fun p => runLM (lowerProgram env u.fns folded.direct p)
    |>.mapError (s!"lowering: " ++ ·)
  let types := (u.types ++ pre.types).map fun d => { d with ty := foldTy env d.ty }
  return { license := u.license.map (·.2), types, maps := u.maps.map (foldMapDecl env),
           direct := folded.direct, fns, programs }

end Koit.Compile
