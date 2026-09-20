import Koit.LIR.Wf
import Koit.BPF.Wf
import Koit.Check.Decl

/-!
Pass C, flattening: closed LIR to BIR. Structured control becomes
labels and jumps, one label stack for `block`, `loop`, and `br`; an
`if` becomes a conditional jump to its else label; `raise` moves the
reason into `v_reason` and jumps to the handler of its kind; `return`
moves the verdict into `v_ret` and jumps to the exit sequence.
Expressions become instruction sequences over virtual registers: an
operation is one instruction at the class its width selects, a narrow
result is normalized to the 32-bit normal form, a cast is one entry
of the cast table, a load folds its constant displacement into the
instruction. The registers are reused by LIR's block structure: a
temporary is free again at the end of its statement, and a local's
register at the end of its block, so that the count is the locals in
scope plus one statement's temporaries. Frame objects are packed
from the top of the frame at 8-byte alignment and zero-filled where
LIR allocates them; the pass reports a frame whose objects alone
exceed 512 bytes. Its theorem, `flatten_correct`, is stated in
`Rules.lean`.
-/

namespace Koit.Compile

open Koit (Span)
open Koit.Core (ArithOp CmpOp AtomicOp Kind Resource)
open Koit.BPF (Instr Src Cls AluOp Cmp VReg Label FrameObj RegClass Cpu BIR)
open Koit.Interface (KindRow CallRow)

/-! ### The translation state -/

/-- What the flattening carries: the code so far, the labels placed,
the register pool, the environment of locals, the constructs a `br`
may leave, the frame objects, and the program's fixed points. -/
structure FState where
  code       : Array (Instr VReg Label) := #[]
  labels     : List (Nat × Nat) := []
  nextLabel  : Nat := 0
  nextReg    : Nat := 0
  free       : List Nat := []
  classes    : List (Nat × RegClass) := []
  /-- The locals in scope, innermost first: the register and the type. -/
  env        : List (String × VReg × LIR.Ty) := []
  /-- The temporaries of the statement under translation. -/
  temps      : List VReg := []
  /-- The enclosing constructs, innermost first: the label a `br`
  to each jumps to. -/
  constructs : List Label := []
  objects    : List FrameObj := []
  /-- The next free offset from the frame's top, negative. -/
  top        : Int := 0
  handlers   : List (Kind × Label) := []
  exitLabel  : Label := ⟨0⟩
  cpu        : Cpu := .v3
  kind       : KindRow := default
  pre        : Interface := default
  deriving Inhabited

abbrev FM := StateT FState (Except String)

def ferr (msg : String) : FM α := throw msg

def emit (i : Instr VReg Label) : FM Unit :=
  modify fun s => { s with code := s.code.push i }

def newLabel : FM Label := do
  let s ← get
  set { s with nextLabel := s.nextLabel + 1 }
  return ⟨s.nextLabel⟩

/-- The label placed at the next instruction. -/
def place (l : Label) : FM Unit :=
  modify fun s => { s with labels := (l.id, s.code.size) :: s.labels }

def setClass (r : VReg) (c : RegClass) : FM Unit := do
  let .v n := r | return
  modify fun s =>
    let c' := match s.classes.lookup n with
      | some old => if old == c then c else .location
      | none => c
    { s with classes := (n, c') :: s.classes.filter (·.1 != n) }

/-- A register from the pool: a freed one, or the next. -/
def alloc (c : RegClass := .scalar) : FM VReg := do
  let s ← get
  let r ← match s.free with
    | n :: rest => do set { s with free := rest }; pure (VReg.v n)
    | [] => do set { s with nextReg := s.nextReg + 1 }; pure (VReg.v s.nextReg)
  setClass r c
  return r

def release (r : VReg) : FM Unit := do
  let .v n := r | return
  modify fun s => { s with free := n :: s.free }

/-- A temporary of the statement under translation. -/
def temp (c : RegClass := .scalar) : FM VReg := do
  let r ← alloc c
  modify fun s => { s with temps := r :: s.temps }
  return r

/-- A statement's translation: its temporaries are free after it. -/
def withTemps (k : FM α) : FM α := do
  let saved := (← get).temps
  modify fun s => { s with temps := [] }
  let a ← k
  let ts := (← get).temps
  for r in ts do release r
  modify fun s => { s with temps := saved }
  return a

def classOf : LIR.Ty → RegClass
  | .ptr => .location
  | .int .. => .scalar

def bind (x : String) (t : LIR.Ty) : FM VReg := do
  let r ← alloc (classOf t)
  modify fun s => { s with env := (x, r, t) :: s.env }
  return r

def lookup (x : String) : FM (VReg × LIR.Ty) := do
  match (← get).env.lookup x with
  | some rt => pure rt
  | none => ferr s!"`{x}` is not declared"

/-- A block's translation: the locals it declares are gone after it,
their registers free again. -/
def withScope (k : FM α) : FM α := do
  let saved := (← get).env
  let a ← k
  let s ← get
  let added := s.env.take (s.env.length - saved.length)
  for (_, r, _) in added do release r
  modify fun s => { s with env := saved }
  return a

/-- A construct entered: the label a `br` to it jumps to. -/
def withConstruct (l : Label) (k : FM α) : FM α := do
  modify fun s => { s with constructs := l :: s.constructs }
  let a ← k
  modify fun s => { s with constructs := s.constructs.drop 1 }
  return a

/-! ### Immediates, widths, normalization -/

/-- A literal usable as an immediate at the class: the kernel's
immediates are 32 bits, sign-extended at the 64-bit class and taken
as a pattern at the 32-bit class. -/
def immFor (cls : Cls) (k : Nat) : Option Int :=
  match cls with
  | .w64 => if k < 2 ^ 31 then some k else none
  | .w32 => if k < 2 ^ 31 then some k else if k < 2 ^ 32 then some ((k : Int) - 2 ^ 32) else none

def clsOf (w : Nat) : Cls := if w == 64 then .w64 else .w32

/-- The register pattern of a literal at its type: a narrow signed
value sign-extended to 32 bits. -/
def literalPattern (signed : Bool) (w : Nat) (k : Nat) : Nat :=
  if signed && w < 32 then Machine.toNatMod (Machine.wrap true w k) 32 else k

/-- A constant into a register: `mov_imm` at 64 bits when it is a
small immediate, at 32 bits when it is a 32-bit pattern, `lddw`
otherwise. -/
def constInto (d : VReg) (k : Nat) : FM Unit := do
  if let some i := immFor .w64 k then emit (.mov .w64 d (.imm i))
  else if let some i := immFor .w32 k then emit (.mov .w32 d (.imm i))
  else emit (.lddw d k)

/-- The normalization of a narrow result: the mask for unsigned, the
sign extension for signed, by `movsx` on v4 and the shift pair on v3. -/
def normalize (signed : Bool) (w : Nat) (d : VReg) : FM Unit := do
  unless w < 32 do return
  if signed then signExtend32 w d
  else emit (.alu .and .w32 d (.imm (2 ^ w - 1)))
where
  signExtend32 (w : Nat) (d : VReg) : FM Unit := do
    match (← get).cpu with
    | .v4 => emit (.movsx .w32 w d d)
    | .v3 =>
      emit (.alu .lsh .w32 d (.imm (32 - w)))
      emit (.alu .arsh .w32 d (.imm (32 - w)))

/-- The cast table: from `int(s,w)` to `int(s',w')` on the value in
`d`, in normal form. -/
def cast (s : Bool) (w : Nat) (s' : Bool) (w' : Nat) (d : VReg) : FM Unit := do
  if w' == 64 then
    -- from an unsigned source or a signed 64-bit one, nothing; from
    -- a signed 32-bit or narrow one, the sign extension from 32
    if s && w < 64 then
      match (← get).cpu with
      | .v4 => emit (.movsx .w64 32 d d)
      | .v3 =>
        emit (.alu .lsh .w64 d (.imm 32))
        emit (.alu .arsh .w64 d (.imm 32))
  else if w' == 32 then
    -- from 64 the low half; from a narrow or 32-bit source nothing
    if w == 64 then emit (.mov .w32 d (.reg d))
  else
    -- to a narrow width: the mask, or the sign extension from the
    -- low bits
    normalize s' w' d

/-! ### Expressions -/

/-- The static type of an expression, a literal unsigned at its width
unless the context says otherwise. -/
def typeOf (e : LIR.Expr) : FM LIR.Ty := do
  match e with
  | .lit w _ => return .int false w
  | .var x => return (← lookup x).2
  | .arith _ s w _ _ => return .int s w
  | .cast _ _ s' w' _ => return .int s' w'
  | .bswap w _ => return .int false w
  | .load s w _ => return .int s w
  | .ctx f =>
    match (← get).kind.ctx.find? (·.name == f) with
    | some cf => match cf.ty with
      | .int _ s w => return .int s w
      | _ => ferr s!"the context field `{f}` is not an integer"
    | none => ferr s!"the context has no field `{f}`"
  | .addr _ => return .ptr

/-- The offset and width of a context field. -/
def ctxField (f : String) : FM (Nat × Nat) := do
  match (← get).kind.ctx.find? (·.name == f) with
  | some cf => match cf.ty with
    | .int _ _ w => return (cf.offset, w)
    | _ => ferr s!"the context field `{f}` is not an integer"
  | none => ferr s!"the context has no field `{f}`"

/-- The offset of a packet bound's row. -/
def ctxBound (isEnd : Bool) : FM Nat := do
  match (← get).kind.ctxBounds.find? (·.isEnd == isEnd) with
  | some b => return b.offset
  | none => ferr "the kind has no packet"

def fitsOff (k : Int) : Bool := -32768 ≤ k && k < 32768

/-- The BPF operation of an LIR operator at a signedness; signed
division and modulo need v4. -/
def aluOf (op : ArithOp) (signed : Bool) : FM AluOp := do
  match op with
  | .add => return .add
  | .sub => return .sub
  | .mul => return .mul
  | .band => return .and
  | .bor => return .or
  | .bxor => return .xor
  | .shl => return .lsh
  | .shr => return (if signed then .arsh else .rsh)
  | .div | .mod =>
    if signed then
      unless (← get).cpu == .v4 do
        ferr "signed division and modulo need cpu v4; the target lacks them under v3"
      return (if op == .div then .sdiv else .smod)
    else return (if op == .div then .div else .mod)

mutual

/-- `e` computed into `d` at the type `t`. -/
partial def expr (e : LIR.Expr) (t : LIR.Ty) (d : VReg) : FM Unit := do
  match e with
  | .lit w k =>
    let (s, w') := match t with
      | .int s w' => (s, w')
      | .ptr => (false, w)
    constInto d (literalPattern s (if w' == 0 then w else w') k)
  | .var x =>
    let (r, _) ← lookup x
    unless r == d do emit (.mov .w64 d (.reg r))
  | .arith op s w l r =>
    expr l (.int s w) d
    let cls := clsOf w
    let bop ← aluOf op s
    let mut src ← operand r (.int s w) cls
    -- a narrow shift masks its amount to the width, where the
    -- instruction masks to 31
    if (op == .shl || op == .shr) && w < 32 then
      src ← match src with
        | .imm k => pure (Src.imm (k % w))
        | .reg rs =>
          let ts ← temp
          emit (.mov .w64 ts (.reg rs))
          emit (.alu .and .w32 ts (.imm (w - 1)))
          pure (Src.reg ts)
    emit (.alu bop cls d src)
    normalize s w d
  | .cast s w s' w' e =>
    expr e (.int s w) d
    cast s w s' w' d
  | .bswap w e =>
    expr e (.int false w) d
    emit (.«end» .be w d)
  | .load s w a =>
    let (b, off) ← addr a
    emit (.ldx w d b off)
    if s && w < 32 then normalize s w d
  | .ctx f =>
    let (off, w) ← ctxField f
    emit (.ldx w d .ctx off)
  | .addr a =>
    let (b, off) ← addr a
    unless b == d do emit (.mov .w64 d (.reg b))
    if off != 0 then emit (.alu .add .w64 d (.imm off))

/-- An operand: a literal that fits as an immediate, a local's
register, or a temporary holding the value. -/
partial def operand (e : LIR.Expr) (t : LIR.Ty) (cls : Cls) : FM (Src VReg) := do
  match e with
  | .lit w k =>
    let (s, w') := match t with
      | .int s w' => (s, w')
      | .ptr => (false, w)
    let pat := literalPattern s w' k
    match immFor cls pat with
    | some i => return .imm i
    | none =>
      let r ← temp
      constInto r pat
      return .reg r
  | .var x => return .reg (← lookup x).1
  | e =>
    let r ← temp (classOf t)
    expr e t r
    return .reg r

/-- An address as a base register and a constant displacement that
fits the instruction's offset field; the base is a local's register
or a temporary. -/
partial def addr (a : LIR.Addr) : FM (VReg × Int) := do
  match a with
  | .var x => return ((← lookup x).1, 0)
  | .plus a k =>
    let (b, off) ← addr a
    if fitsOff (off + k) then return (b, off + k)
    let t ← temp .location
    emit (.mov .w64 t (.reg b))
    emit (.alu .add .w64 t (.imm (off + k)))
    return (t, 0)
  | .index a e k =>
    let (b, off) ← addr a
    let ti ← temp
    expr e (← typeOf e) ti
    if k != 1 then emit (.alu .mul .w64 ti (.imm k))
    let t ← temp .location
    emit (.mov .w64 t (.reg b))
    emit (.alu .add .w64 t (.reg ti))
    return (t, off)
  | .pktData =>
    let t ← temp .location
    emit (.ldx 32 t .ctx (← ctxBound false))
    return (t, 0)
  | .pktEnd =>
    let t ← temp .location
    emit (.ldx 32 t .ctx (← ctxBound true))
    return (t, 0)
  | .mapval m k =>
    let t ← temp .location
    emit (.mapval t m 0)
    if fitsOff k then return (t, k)
    emit (.alu .add .w64 t (.imm k))
    return (t, 0)

end

/-- An expression into a fresh temporary. -/
def exprTemp (e : LIR.Expr) (t : LIR.Ty) : FM VReg := do
  match e with
  | .var x => return (← lookup x).1
  | e =>
    let r ← temp (classOf t)
    expr e t r
    return r

/-! ### Conditions -/

def cmpOf (op : CmpOp) (signed : Bool) : Cmp :=
  match op, signed with
  | .eq, _ => .eq
  | .ne, _ => .ne
  | .lt, false => .lt | .lt, true => .slt
  | .le, false => .le | .le, true => .sle
  | .gt, false => .gt | .gt, true => .sgt
  | .ge, false => .ge | .ge, true => .sge

def negate : CmpOp → CmpOp
  | .eq => .ne | .ne => .eq | .lt => .ge | .ge => .lt | .le => .gt | .gt => .le

def flip : CmpOp → CmpOp
  | .eq => .eq | .ne => .ne | .lt => .gt | .gt => .lt | .le => .ge | .ge => .le

/-- A jump to `target` when the condition's truth equals `when`. A
location against zero keeps the zero as the immediate, as the
machine requires. -/
def cond (c : LIR.Cond) (target : Label) (when : Bool) : FM Unit := do
  -- a literal on the left is moved to the right
  let (op, l, r) := match c.l with
    | .lit .. => (flip c.op, c.r, c.l)
    | _ => (c.op, c.l, c.r)
  let op := if when then op else negate op
  let t : LIR.Ty := .int c.signed c.w
  let cls := clsOf c.w
  let a ← exprTemp l (← match l with
    | .addr _ => pure LIR.Ty.ptr
    | _ => pure t)
  let b ← match r with
    | .addr _ => do
      let rb ← exprTemp r .ptr
      pure (Src.reg rb)
    | _ => operand r t cls
  emit (.jcond (cmpOf op c.signed) cls a b target)

/-! ### Statements -/

/-- Whether a block leaves by `return`, `raise`, or `br` on its last
statement, so that no jump over the else branch is needed. -/
def terminates : List LIR.Stmt → Bool
  | [] => false
  | ss => match ss.getLast! with
    | .ret .. | .raise .. | .br .. => true
    | _ => false

def roundUp8 (n : Nat) : Nat := (n + 7) / 8 * 8

/-- The store of `n` bytes at `[b + off]` from `[s + soff]`, by 8, 4,
2, and 1. -/
def copyBytes (b : VReg) (off : Int) (s : VReg) (soff : Int) (n : Nat) : FM Unit := do
  let t ← temp
  let mut i : Nat := 0
  for w in [64, 32, 16, 8] do
    while i + w / 8 ≤ n do
      emit (.ldx w t s (soff + i))
      emit (.stx w b (off + i) (.reg t))
      i := i + w / 8

/-- The fill of `n` bytes at `[b + off]` with a byte: a constant by
4, 2, and 1 as replicated immediates, a register byte by byte. -/
def fillBytes (b : VReg) (off : Int) (v : Src VReg) (n : Nat) : FM Unit := do
  match v with
  | .imm k =>
    let byte := Machine.toNatMod k 8
    let mut i : Nat := 0
    for w in [32, 16, 8] do
      let pat := (List.range (w / 8)).foldl (fun acc _ => acc * 256 + byte) 0
      let imm : Int := if pat ≥ 2 ^ 31 then (pat : Int) - 2 ^ 32 else pat
      while i + w / 8 ≤ n do
        emit (.stx w b (off + i) (.imm imm))
        i := i + w / 8
  | .reg r =>
    let t ← temp
    emit (.mov .w64 t (.reg r))
    emit (.alu .and .w32 t (.imm 255))
    for i in [0:n] do
      emit (.stx 8 b (off + i) (.reg t))

/-- The kernel's format for a koit one: each `{}` the conversion of
its argument's type, as `bpf_trace_printk` prints a 64-bit register. -/
def kernelFormat (fmt : String) (tys : List LIR.Ty) : String :=
  let parts := fmt.splitOn "{}"
  let conv : LIR.Ty → String
    | .int false 64 => "%llu"
    | .int false _ => "%u"
    | .int true 64 => "%lld"
    | .int true _ => "%d"
    | .ptr => "%llx"
  let rec go : List String → List LIR.Ty → String
    | [], _ => ""
    | [s], _ => s
    | s :: rest, t :: ts => s ++ conv t ++ go rest ts
    | s :: rest, [] => s ++ "{}" ++ go rest []
  go parts tys

/-- The bytes of the kernel's format stored into a fresh frame object
at the call site, four at a time, so that the allocation can pass
its location; the object's name and the format's size. -/
def formatObject (fmt : String) (tys : List LIR.Ty) : FM (String × Nat) := do
  let bytes := (kernelFormat fmt tys).toUTF8.toList ++ [0]
  let size := bytes.length
  let s ← get
  let name := s!"fmt_{s.objects.length}"
  let osize := roundUp8 size
  let base := s.top - osize
  let obj : FrameObj := { name, size, base }
  set { s with objects := s.objects ++ [obj], top := base }
  let t ← temp .location
  emit (.lea t name)
  for i in [0:osize / 4] do
    let chunk := ((bytes.drop (4 * i)).take 4) ++ List.replicate 4 0
    let pat := Machine.ofLe (chunk.take 4)
    let imm : Int := if pat ≥ 2 ^ 31 then (pat : Int) - 2 ^ 32 else pat
    emit (.stx 32 t (4 * i) (.imm imm))
  return (name, size)

/-- The label of the handler of a kind. -/
def handlerLabel (k : Kind) : FM Label := do
  match (← get).handlers.lookup k with
  | some l => pure l
  | none => ferr s!"no handler for `{k}`"

mutual

partial def stmts (ss : List LIR.Stmt) : FM Unit := do
  for s in ss do withTemps (stmt s)

partial def stmt (s : LIR.Stmt) : FM Unit := do
  match s with
  | .«let» _ x t e =>
    let r ← bind x t
    expr e t r
  | .assign _ x e =>
    let (r, t) ← lookup x
    let v ← exprTemp e t
    unless v == r do emit (.mov .w64 r (.reg v))
  | .store _ w a e =>
    let (b, off) ← addr a
    let v ← operand e (.int false w) (clsOf w)
    emit (.stx w b off v)
  | .ctxStore _ f e =>
    let (off, w) ← ctxField f
    let v ← operand e (.int false w) (clsOf w)
    emit (.stx w .ctx off v)
  | .frame _ x n _ =>
    let s ← get
    let size := roundUp8 (max n 1)
    let base := s.top - size
    let obj : FrameObj := { name := x, size := n, base }
    set { s with objects := s.objects ++ [obj], top := base }
    let r ← bind x .ptr
    emit (.lea r x)
    for i in [0:size / 8] do
      emit (.stx 64 r (8 * i) (.imm 0))
  | .ite _ c t e =>
    if e.isEmpty then
      let lEnd ← newLabel
      cond c lEnd false
      withScope (stmts t)
      place lEnd
    else if t.isEmpty then
      let lEnd ← newLabel
      cond c lEnd true
      withScope (stmts e)
      place lEnd
    else
      let lElse ← newLabel
      let lEnd ← newLabel
      cond c lElse false
      withScope (stmts t)
      unless terminates t do emit (.ja lEnd)
      place lElse
      withScope (stmts e)
      place lEnd
  | .block _ body =>
    let lExit ← newLabel
    withConstruct lExit (withScope (stmts body))
    place lExit
  | .loop _ body =>
    let lHead ← newLabel
    place lHead
    withConstruct lHead (withScope (stmts body))
    emit (.ja lHead)
  | .br _ n =>
    match (← get).constructs[n]? with
    | some l => emit (.ja l)
    | none => ferr s!"`br {n}` outside its constructs"
  | .ret _ (some e) =>
    let s ← get
    let t : LIR.Ty := match s.kind.verdictTy with
      | .int _ sg w => .int sg w
      | _ => .u32
    expr e t .ret
    emit (.ja s.exitLabel)
  | .ret _ none => ferr "a bare `return` outside a function"
  | .raise _ k e =>
    expr e .u32 .reason
    emit (.ja (← handlerLabel k))
  | .call _ _ f .. => ferr s!"a call to `{f}`: the flattening takes closed LIR"
  | .builtin _ x b args => builtin x b args
  | .kernel _ x h args =>
    let some row := (← get).pre.call? h | ferr s!"unknown kernel function `{h}`"
    let regs ← args.mapM fun a => do exprTemp a (← typeOf a)
    let dst ← match x with
      | some x => some <$> bind x (LIR.rowResult row)
      | none => pure none
    emit (.call (.kernel h) regs dst)

partial def builtin (x : Option String) (b : LIR.Builtin) (args : List LIR.Expr) : FM Unit := do
  let argRegs : FM (List VReg) := args.mapM fun a => do exprTemp a (← typeOf a)
  let bindResult (t : LIR.Ty) : FM (Option VReg) := do
    match x with
    | some x => some <$> bind x t
    | none => pure none
  let mapHandle (m : String) : FM VReg := do
    let h ← temp .handle
    emit (.mapref h m)
    return h
  match b, args with
  | .lookup m, [k] =>
    let h ← mapHandle m
    let rk ← exprTemp k .ptr
    emit (.call (.builtin .lookup) [h, rk] (← bindResult .ptr))
  | .update m, [k, v] =>
    let h ← mapHandle m
    let rk ← exprTemp k .ptr
    let rv ← exprTemp v .ptr
    emit (.call (.builtin .update) [h, rk, rv] (← bindResult .i64))
  | .delete m, [k] =>
    let h ← mapHandle m
    let rk ← exprTemp k .ptr
    emit (.call (.builtin .delete) [h, rk] (← bindResult .i64))
  | .reserve m n, [] =>
    let h ← mapHandle m
    emit (.call (.builtin (.reserve n)) [h] (← bindResult .ptr))
  | .submit, [r] => emit (.call (.builtin .submit) [← exprTemp r .ptr] none)
  | .discard, [r] => emit (.call (.builtin .discard) [← exprTemp r .ptr] none)
  | .lock, [a] => emit (.call (.builtin .lock) [← exprTemp a .ptr] none)
  | .unlock, [a] => emit (.call (.builtin .unlock) [← exprTemp a .ptr] none)
  | .enter r, [] => emit (.call (.builtin (.enter r)) [] none)
  | .leave r, [] => emit (.call (.builtin (.leave r)) [] none)
  | .copy n, [d, s] =>
    let (bd, od) ← addrOf d
    let (bs, os) ← addrOf s
    copyBytes bd od bs os n
  | .fill n, [d, v] =>
    let (bd, od) ← addrOf d
    let sv ← operand v .u8 .w32
    fillBytes bd od sv n
  | .printk fmt, vs =>
    let regs ← argRegs
    let tys ← vs.mapM typeOf
    let (obj, size) ← formatObject fmt tys
    emit (.call (.builtin (.printk fmt vs.length obj size)) regs none)
  | .atomic op s w fetch, a :: vs =>
    let (ba, oa) ← addrOf a
    let cls := clsOf w
    match op, vs with
    | .cmpxchg, [old, new] =>
      let rold ← exprTemp old (.int s w)
      let rnew ← exprTemp new (.int s w)
      let tnew ← temp
      emit (.mov .w64 tnew (.reg rnew))
      emit (.mov .w64 .ret (.reg rold))
      emit (.atomic .cmpxchg cls true ba oa tnew)
      if let some d ← bindResult (.int s w) then emit (.mov .w64 d (.reg .ret))
    | _, [v] =>
      let rv ← exprTemp v (.int s w)
      -- an exchange always fetches, as the kernel's does
      if fetch || x.isSome || op == .xchg then
        let tv ← temp
        emit (.mov .w64 tv (.reg rv))
        emit (.atomic op cls true ba oa tv)
        if let some d ← bindResult (.int s w) then emit (.mov .w64 d (.reg tv))
      else
        emit (.atomic op cls false ba oa rv)
    | _, _ => ferr "an atomic update with the wrong operands"
  | b, _ => ferr s!"`{b.print}` with the wrong operands"
where
  /-- An address argument as base and displacement; any other
  expression through a register. -/
  addrOf (e : LIR.Expr) : FM (VReg × Int) := do
    match e with
    | .addr a => addr a
    | e => return (← exprTemp e .ptr, 0)

end

/-! ### Programs -/

/-- The verdict a program's body falls off its end to: zero for a kind
without a packet, as LIR halts with; the kind's default failure
verdict otherwise, where LIR's rule is an error and the code is
dead, so that a violation stays visible. -/
def fallOffVerdict (kind : KindRow) : Nat :=
  if kind.hasPkt then
    match kind.defaultExit with
    | .verdict name => (kind.verdicts.lookup name).getD 0
    | .value v => Machine.toNatMod v 32
  else 0

/-- One LIR program flattened. -/
def flattenProgram (pre : Interface) (cpu : Cpu) (p : LIR.Program) : Except String BIR := do
  let some kind := pre.kind? p.kind | throw s!"unknown kind `{p.kind}`"
  let translate : FM Unit := do
    let exitLabel ← newLabel
    let mut handlers : List (Kind × Label) := []
    for h in p.handlers do
      handlers := handlers ++ [(h.kind, ← newLabel)]
    modify fun s => { s with exitLabel, handlers }
    withScope (stmts p.body)
    constInto .ret (fallOffVerdict kind)
    emit (.ja exitLabel)
    for h in p.handlers do
      place (← handlerLabel h.kind)
      withScope do
        modify fun s => { s with env := ("reason", VReg.reason, LIR.Ty.u32) :: s.env }
        stmts h.body
        modify fun s => { s with env := s.env.drop 1 }
      -- a handler ends in `return`; the jump covers a body the
      -- well-formedness check let through
      emit (.ja exitLabel)
    place exitLabel
    emit .exit
  let init : FState := { cpu, kind, pre }
  let ((), s) ← translate.run init |>.mapError (s!"in `{p.name}`: " ++ ·)
  let objBytes := (-s.top).toNat
  if objBytes > BPF.Frame.size then
    throw s!"the frame of `{p.name}` holds {objBytes} bytes of objects, above {BPF.Frame.size}"
  return { name := p.name, kind := p.kind, code := s.code, labels := s.labels,
           objects := s.objects,
           regs := s.classes.reverse.map fun (n, c) => (VReg.v n, c), cpu }

/-- Pass C on a closed LIR unit: one BIR program per program. -/
def flatten (pre : Interface) (cpu : Cpu) (u : LIR.CompUnit) : Except String (List BIR) := do
  unless u.fns.isEmpty do throw "the flattening takes closed LIR; inline first"
  u.programs.mapM (flattenProgram pre cpu)

/-- The machine's environment for a BIR program: the interface, the
kind's row, BIR's convention, and the checker's layout for the sizes
of the kernel functions' memory parameters. -/
def birEnv (pre : Interface) (env : Check.Env) (B : BIR) : Except String (BPF.Env VReg Label) := do
  let some kind := pre.kind? B.kind | throw s!"unknown kind `{B.kind}`"
  return { pre, kind, conv := BPF.birConv, prog := B,
           sizeOf := fun t => match env.layout t with
             | .ok (n, _) => some n
             | .error _ => none }

end Koit.Compile
