import Koit.Core.Print
import Koit.Interface.Decls

/-!
LIR, the explicit intermediate language: Core after the checker, with
the facts spent. Every runtime test is an `if` on a comparison, one
exactly where the source had a marker; every failure, acquisition,
and release is a statement; widths and signedness are on every
literal and operator, so nothing below consults a type; control is
`block`, `loop`, `br n`, `if`, and `return`, and functions remain
until the inlining pass removes them. Expressions are pure: a call
is a statement, and the lowering hoists the calls inside a Core
expression into their own bindings in evaluation order.

This file is the syntax. `Print.lean` is the printer behind `koitc
lower`, `Wf.lean` the well-formedness check the lowering satisfies by
construction and the flattening assumes, `State.lean` and
`Semantics.lean` the dynamic semantics, `Interp.lean` its executable
form. Two small additions to the language as the design document
first stated it: a store to a context field, since a `tc` program
may write `mark`, and the signedness of an atomic update, so that the
previous value it yields has the place's type without a lookup.
-/

namespace Koit.LIR

open Koit (Span)
open Koit.Core (ArithOp CmpOp AtomicOp Kind Resource)

/-- The types: a fixed-width integer with its signedness, or a
location. A boolean is `int(u,8)`, 0 or 1. -/
inductive Ty where
  | int (signed : Bool) (w : Nat)
  | ptr
  deriving Repr, BEq, DecidableEq, Inhabited

namespace Ty

def print : Ty → String
  | .int s w => (if s then "i" else "u") ++ toString w
  | .ptr => "ptr"

def u8 : Ty := .int false 8
def u32 : Ty := .int false 32
def u64 : Ty := .int false 64
def i64 : Ty := .int true 64

def width : Ty → Nat
  | .int _ w => w
  | .ptr => 64

end Ty

mutual

/-- Expressions. A literal `k(w)` is the `w`-bit pattern `k`, of
either signedness; the operators carry the width and signedness they
apply at; a load carries the type it reads as, so that a signed byte
is sign-extended into its local. -/
inductive Expr where
  | lit (w : Nat) (k : Nat)
  | var (x : String)
  | arith (op : ArithOp) (signed : Bool) (w : Nat) (l r : Expr)
  /-- `cast(s,w -> s',w') e`: truncation, zero extension from
  unsigned, sign extension from signed. -/
  | cast (signed : Bool) (w : Nat) (signed' : Bool) (w' : Nat) (e : Expr)
  | bswap (w : Nat) (e : Expr)
  | load (signed : Bool) (w : Nat) (a : Addr)
  | ctx (f : String)
  | addr (a : Addr)

/-- Addresses: a `ptr` local, a constant or a scaled index added to
one, the packet's bounds, or the value of a map marked for direct
access. -/
inductive Addr where
  | var (x : String)
  | plus (a : Addr) (k : Nat)
  /-- `a + e * k`. -/
  | index (a : Addr) (e : Expr) (k : Nat)
  | pktData
  | pktEnd
  | mapval (m : String) (k : Nat)

end

deriving instance Repr, Inhabited for Expr, Addr

/-- A condition: two scalars compared at a width and signedness, two
addresses compared, or an address against `0(64)`. -/
structure Cond where
  op     : CmpOp
  signed : Bool
  w      : Nat
  l      : Expr
  r      : Expr
  deriving Repr, Inhabited

/-- The builtins: the map operations, the protocol operations of the
resource declarations whose kernel function is fixed, byte moves, `printk`,
and the atomic updates. -/
inductive Builtin where
  | lookup (m : String)
  | update (m : String)
  | delete (m : String)
  | reserve (m : String) (n : Nat)
  | submit
  | discard
  | lock
  | unlock
  | enter (r : Resource)
  | leave (r : Resource)
  | copy (n : Nat)
  | fill (n : Nat)
  | printk (fmt : String)
  /-- `bpf_tail_call` through the program array: the index; taken, it
  never returns. -/
  | tail (m : String)
  | atomic (op : AtomicOp) (signed : Bool) (w : Nat) (fetch : Bool)
  deriving Repr, Inhabited

/-- Statements. A block is a list; `skip` is the empty list. Every
statement carries the span of the Core statement it came from. -/
inductive Stmt where
  | «let» (span : Span) (x : String) (ty : Ty) (e : Expr)
  | assign (span : Span) (x : String) (e : Expr)
  | store (span : Span) (w : Nat) (a : Addr) (e : Expr)
  | ctxStore (span : Span) (f : String) (e : Expr)
  /-- `frame x : n [as S]`: `n` zeroed bytes of stack, 8-aligned,
  `x` bound to their location; `S` names the source type for the
  printers. -/
  | frame (span : Span) (x : String) (n : Nat) (src : Option Core.Ty)
  | ite (span : Span) (c : Cond) (thn els : List Stmt)
  | block (span : Span) (body : List Stmt)
  | loop (span : Span) (body : List Stmt)
  /-- Leaves `n + 1` enclosing `block` or `loop` constructs: a `loop`
  reached restarts, a `block` reached is left. -/
  | br (span : Span) (n : Nat)
  | ret (span : Span) (e : Option Expr)
  | raise (span : Span) (k : Kind) (e : Expr)
  /-- `[x =] call f(args) [unwind s] [absent s]`. -/
  | call (span : Span) (x : Option String) (f : String) (args : List Expr)
      (unwind : Option (List Stmt)) (absent : Option (List Stmt))
  | builtin (span : Span) (x : Option String) (b : Builtin) (args : List Expr)
  /-- A kernel function, by the name of its declaration. -/
  | kernel (span : Span) (x : Option String) (h : String) (args : List Expr)
  deriving Repr, Inhabited

def Stmt.span : Stmt → Span
  | .«let» s .. | .assign s .. | .store s .. | .ctxStore s .. | .frame s ..
  | .ite s .. | .block s .. | .loop s .. | .br s .. | .ret s .. | .raise s ..
  | .call s .. | .builtin s .. | .kernel s .. => s

structure Param where
  name : String
  ty   : Ty
  deriving Repr, Inhabited

/-- `fn f (x : T, ...) [-> T [?]] [fails] { s }`. -/
structure Fn where
  span   : Span
  name   : String
  params : List Param
  ret    : Option Ty
  /-- `-> T ?`: the function may return without a value. -/
  opt    : Bool
  fails  : Bool
  body   : List Stmt
  /-- A subprogram the verifier checks once; never inlined. -/
  global : Bool := false
  deriving Repr, Inhabited

/-- `on k => s`; the body sees the local `reason : u32`. -/
structure Handler where
  kind : Kind
  body : List Stmt
  deriving Repr, Inhabited

structure Program where
  span     : Span
  name     : String
  kind     : String
  body     : List Stmt
  handlers : List Handler
  deriving Repr, Inhabited

/-- A unit: the declarations the printers and the machine need, the
maps marked for direct value access, the functions, the programs. -/
structure CompUnit where
  license  : Option String
  types    : List Core.TypeDecl
  maps     : List Core.MapDecl
  direct   : List String
  fns      : List Fn
  programs : List Program
  deriving Inhabited

end Koit.LIR
