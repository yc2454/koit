import Koit.Syntax.Span

/-!
The surface abstract syntax: declarations, types, expressions,
statements, contracts, and configuration. Every node carries the span
of the source text it came from,
as its first field; the typing rules never read it, diagnostics and
printing do.

The tree is the source as written, not yet desugared: `check`,
`if let`, markers, `else` tails, and parentheses are nodes, because
`koitc print` reproduces them and the desugaring of session 2 reads
them. Primitive type names are resolved here. Every other contextual
name (program kinds, failure kinds, map kinds, `pkt`, `ctx`, `abort`)
is kept as the identifier written and resolved by the checker.
-/

namespace Koit.Syntax

/-- `!`, `-`, and `*`, the last for reading through a reference or a
view. -/
inductive UnOp where
  | not | neg | deref
  deriving Repr, BEq, DecidableEq, Inhabited

inductive BinOp where
  | mul | div | mod | add | sub | shl | shr | band | bxor | bor
  | eq | ne | lt | le | gt | ge | land | lor
  deriving Repr, BEq, DecidableEq, Inhabited

/-- `=` and the compound assignments. -/
inductive AssignOp where
  | set | add | sub | mul | band | bor | bxor | shl | shr
  deriving Repr, BEq, DecidableEq, Inhabited

/-- The verdict statements. `abort` is a contextual name in statement
position, not a keyword. -/
inductive Verdict where
  | pass | drop | tx | abort
  deriving Repr, BEq, DecidableEq, Inhabited

/-- The pattern of an iterator loop: one name, or a key and a value. -/
inductive Pattern where
  | one (span : Span) (name : String)
  | pair (span : Span) (key value : String)
  deriving Repr, Inhabited

mutual

/-- Types. -/
inductive Ty where
  | int (span : Span) (signed : Bool) (width : Nat)
  | be (span : Span) (width : Nat)
  | bool (span : Span)
  | named (span : Span) (name : String)
  | struct (span : Span) (fields : List Field)
  /-- `{ v: T | P }`. -/
  | refined (span : Span) (var : String) (base : Ty) (pred : Expr)
  | array (span : Span) (elem : Ty) (len : Expr)
  | ref (span : Span) (t : Ty)
  | view (span : Span) (t : Ty)
  /-- `T?`. -/
  | opt (span : Span) (t : Ty)
  | own (span : Span) (t : Ty)

inductive Field where
  | mk (span : Span) (name : String) (ty : Ty) (pred : Option Expr)

/-- Expressions. -/
inductive Expr where
  | int (span : Span) (value : Nat) (text : String)
  | char (span : Span) (value : UInt8)
  | str (span : Span) (value : String)
  | bool (span : Span) (value : Bool)
  | var (span : Span) (name : String)
  | paren (span : Span) (e : Expr)
  | unary (span : Span) (op : UnOp) (e : Expr)
  | move (span : Span) (name : String)
  | binary (span : Span) (op : BinOp) (l r : Expr)
  | cast (span : Span) (e : Expr) (ty : Ty)
  | field (span : Span) (e : Expr) (name : String)
  | index (span : Span) (e idx : Expr)
  | call (span : Span) (f : Expr) (args : List Expr)
  /-- `recv.name<T>(args)`: `pkt.view<T>(off)`, `rb.reserve<T>()`. -/
  | tcall (span : Span) (recv : Expr) (name : String) (ty : Ty)
      (args : List Expr)
  | structLit (span : Span) (fields : List FieldInit)

inductive FieldInit where
  | mk (span : Span) (name : String) (value : Expr)

end

deriving instance Repr, Inhabited for Ty, Field, Expr, FieldInit

def Ty.span : Ty → Span
  | .int s .. | .be s .. | .bool s | .named s ..
  | .struct s .. | .refined s .. | .array s .. | .ref s .. | .view s ..
  | .opt s .. | .own s .. => s

def Field.span : Field → Span
  | .mk s .. => s

def Field.name : Field → String
  | .mk _ n .. => n

def Expr.span : Expr → Span
  | .int s .. | .char s .. | .str s .. | .bool s .. | .var s .. | .paren s ..
  | .unary s .. | .move s .. | .binary s .. | .cast s .. | .field s ..
  | .index s .. | .call s .. | .tcall s .. | .structLit s .. => s

def FieldInit.span : FieldInit → Span
  | .mk s .. => s

def Pattern.span : Pattern → Span
  | .one s .. | .pair s .. => s

mutual

/-- Statements. -/
inductive Stmt where
  /-- `let` and `var`. -/
  | decl (span : Span) (mutable : Bool) (name : String) (ty : Option Ty)
      (pred : Option Expr) (init : Expr) (tail : Option Tail)
  | assign (span : Span) (target : Expr) (op : AssignOp) (value : Expr)
  /-- An `else if` is an else block holding one `if`. -/
  | ite (span : Span) (cond : Expr) (thn : Block) (els : Option Block)
  | iteLet (span : Span) (name : String) (init : Expr) (thn : Block)
      (els : Option Block)
  /-- `repeat n`. -/
  | loop (span : Span) (count : Expr) (body : Block)
  | forRange (span : Span) (var : String) (lo hi : Expr) (body : Block)
  /-- `for pat in it bounded n`, `marked` when `n?`. -/
  | forIter (span : Span) (pat : Pattern) (iter bound : Expr)
      (marked : Bool) (body : Block)
  | hold (span : Span) (name : Option String) (acq : Expr)
      (tail : Option Tail) (body : Block)
  | check (span : Span) (cond : Expr) (tail : Option Tail)
  /-- `tail m[i]`, a tail call through the program array `m`. -/
  | tail (span : Span) (map : String) (idx : Expr) (tail : Option Tail)
  | expr (span : Span) (e : Expr) (tail : Option Tail)
  | brk (span : Span)
  | cont (span : Span)
  | ret (span : Span) (value : Option Expr)
  | verdict (span : Span) (v : Verdict)
  | fail (span : Span) (reason : Option Expr)

/-- What follows a fallible operation: `?`, `else { block }`, or
`else exit`, where the statement is one of the exit forms. -/
inductive Tail where
  | mark (span : Span)
  | elseBlock (span : Span) (b : Block)
  | elseExit (span : Span) (s : Stmt)

inductive Block where
  | mk (span : Span) (stmts : List Stmt)

end

deriving instance Repr, Inhabited for Stmt, Tail, Block

def Stmt.span : Stmt → Span
  | .decl s .. | .assign s .. | .ite s .. | .iteLet s .. | .loop s ..
  | .forRange s .. | .forIter s .. | .hold s .. | .check s .. | .tail s .. | .expr s ..
  | .brk s | .cont s | .ret s .. | .verdict s .. | .fail s .. => s

def Tail.span : Tail → Span
  | .mark s | .elseBlock s .. | .elseExit s .. => s

def Block.span : Block → Span
  | .mk s _ => s

def Block.stmts : Block → List Stmt
  | .mk _ ss => ss

/-- The exit forms, which an `else` tail, a handler, and
the header's `fail` take. -/
def Stmt.isExit : Stmt → Bool
  | .fail .. | .verdict .. | .ret .. | .brk .. | .cont .. => true
  | _ => false

/-- The place forms: a variable, a field or element of a
place, or `*x`. -/
partial def Expr.isPlace : Expr → Bool
  | .var .. => true
  | .field _ e _ => e.isPlace
  | .index _ e _ => e.isPlace
  | .unary _ .deref (.var ..) => true
  | _ => false

/-! ### Declarations -/

structure Param where
  span : Span
  name : String
  ty   : Ty
  pred : Option Expr
  deriving Repr, Inhabited

/-- `-> T`, `-> T?` (as `Ty.opt`), or `-> r: T where P`. -/
inductive RetType where
  | ty (t : Ty)
  | refined (span : Span) (name : String) (t : Ty) (pred : Expr)
  deriving Repr, Inhabited

structure FnDecl where
  span   : Span
  name   : String
  params : List Param
  ret    : Option RetType
  fails  : Bool
  body   : Block
  /-- `global fn`: a subprogram the verifier checks once. -/
  global : Bool := false
  deriving Repr, Inhabited

inductive MapType where
  | array (span : Span) (n : Expr) (value : Ty)
  | percpuArray (span : Span) (n : Expr) (value : Ty)
  | hash (span : Span) (n : Expr) (key value : Ty)
  | ringbuf (span : Span) (n : Expr)
  /-- `prog_array[n] of K`: slots for programs of the kind. -/
  | progArray (span : Span) (n : Expr) (kind : String)
  /-- `sockmap[n]` and `sockhash[n] of K`: sockets by index or by
  key, never places. -/
  | sockmap (span : Span) (n : Expr)
  | sockhash (span : Span) (n : Expr) (key : Ty)
  deriving Repr, Inhabited

/-- A region of a `preserve` clause. -/
inductive Region where
  /-- `pkt`, or `pkt[a .. b)`. -/
  | pkt (span : Span) (range : Option (Expr × Expr))
  /-- `maps`, or `maps except m1, m2`. -/
  | maps (span : Span) (except : List String)
  | map (span : Span) (name : String)
  | ctxField (span : Span) (name : String)
  deriving Repr, Inhabited

inductive Clause where
  | verdicts (span : Span) (names : List String)
  | preserve (span : Span) (regions : List Region)
  deriving Repr, Inhabited

/-- `on k1, k2 { ... }`; `kinds = none` is `on _`. -/
structure Handler where
  span  : Span
  kinds : Option (List String)
  body  : Block
  deriving Repr, Inhabited

structure Contract where
  span    : Span
  name    : String
  kind    : String
  clauses : List Clause
  deriving Repr, Inhabited

structure Program where
  span       : Span
  name       : String
  kind       : String
  implements : Option String
  clauses    : List Clause
  handlers   : List Handler
  body       : Block
  deriving Repr, Inhabited

inductive Item where
  | const (span : Span) (name : String) (ty : Option Ty) (value : Expr)
  | config (span : Span) (name : String) (ty : Ty) (init : Option Expr)
  | type (span : Span) (name : String) (ty : Ty)
  | map (span : Span) (name : String) (mt : MapType) (access : MapAccess)
      (init : Option (List Expr))
  | fn (d : FnDecl)
  | contract (c : Contract)
  | program (p : Program)
  deriving Repr, Inhabited

def Item.span : Item → Span
  | .const s .. | .config s .. | .type s .. | .map s .. => s
  | .fn d => d.span
  | .contract c => c.span
  | .program p => p.span

/-- A compilation unit, one file. -/
structure CompUnit where
  license : Option (Span × String)
  items   : List Item
  deriving Repr, Inhabited

end Koit.Syntax
