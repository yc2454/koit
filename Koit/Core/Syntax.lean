import Koit.Syntax.Span

/-!
Core, the one typed language, per spec/language.md section 18.1 and
the decision of spec/ISSUES.md entry 8.

The surface desugars to Core syntactically; the typing judgment and
the theorems are stated on Core. Every node carries the span of the
surface construct it came from, as its first field, so a diagnostic
about a Core node names the source line the programmer wrote.

Three surface forms stay in Core because handling them needs types:
functions with their signatures, `if` on a constant condition, and
`for i in a..b`. Four representation points that 18.1 leaves open are
decided here and recorded in spec/ISSUES.md, entry 11: a binding's
declared type, the argument forms of a call, `try` remembering whether
its `else` came from a tail or from `if let`, and the `invalid` node,
which keeps desugaring total on ill-formed surface programs by
carrying the diagnostic the checker will report.
-/

namespace Koit.Core

open Koit (Span)

/-- The six failure kinds of section 10.1. -/
inductive Kind where
  | short_packet | missing | invariant | bound | helper | program
  deriving Repr, BEq, DecidableEq, Inhabited

namespace Kind

def spelling : Kind → String
  | .short_packet => "short_packet" | .missing => "missing"
  | .invariant => "invariant"       | .bound => "bound"
  | .helper => "helper"             | .program => "program"

/-- Every kind, in the order of the table of section 10.1. -/
def all : List Kind :=
  [.short_packet, .missing, .invariant, .bound, .helper, .program]

def ofString? (s : String) : Option Kind := all.find? (·.spelling == s)

instance : ToString Kind := ⟨spelling⟩

end Kind

/-- The resources `R` of section 18.1, one per row of the table of
section 11.2, plus `iter` for the iterator loops of section 9, whose
row this draft does not define (spec/ISSUES.md, entry 12). -/
inductive Resource where
  | spinlock | rcu | preempt | irq | ringbuf | sockref | iter
  deriving Repr, BEq, DecidableEq, Inhabited

namespace Resource

def spelling : Resource → String
  | .spinlock => "spinlock" | .rcu => "rcu"         | .preempt => "preempt"
  | .irq => "irq"           | .ringbuf => "ringbuf" | .sockref => "sockref"
  | .iter => "iter"

instance : ToString Resource := ⟨spelling⟩

end Resource

/-- The guards `g` of section 12: the packet's layout token, or a held
resource. -/
inductive Guard where
  | layout
  | held (r : Resource)
  deriving Repr, BEq, Inhabited

/-- The arithmetic and bitwise operators, `op` of section 18.1. -/
inductive ArithOp where
  | add | sub | mul | div | mod | band | bor | bxor | shl | shr
  deriving Repr, BEq, DecidableEq, Inhabited

def ArithOp.spelling : ArithOp → String
  | .add => "+" | .sub => "-" | .mul => "*" | .div => "/" | .mod => "%"
  | .band => "&" | .bor => "|" | .bxor => "^" | .shl => "<<" | .shr => ">>"

/-- The comparisons, `cmp` of section 18.1. -/
inductive CmpOp where
  | eq | ne | lt | le | gt | ge
  deriving Repr, BEq, DecidableEq, Inhabited

def CmpOp.spelling : CmpOp → String
  | .eq => "==" | .ne => "!=" | .lt => "<" | .le => "<=" | .gt => ">"
  | .ge => ">="

/-- The atomic updates of section 8.5. -/
inductive AtomicOp where
  | add | band | bor | bxor | xchg | cmpxchg
  deriving Repr, BEq, DecidableEq, Inhabited

def AtomicOp.spelling : AtomicOp → String
  | .add => "atomic_add" | .band => "atomic_and" | .bor => "atomic_or"
  | .bxor => "atomic_xor" | .xchg => "atomic_xchg"
  | .cmpxchg => "atomic_cmpxchg"

def AtomicOp.ofString? : String → Option AtomicOp
  | "atomic_add" => some .add   | "atomic_and" => some .band
  | "atomic_or" => some .bor    | "atomic_xor" => some .bxor
  | "atomic_xchg" => some .xchg | "atomic_cmpxchg" => some .cmpxchg
  | _ => none

mutual

/-- Types `T` of section 18.1, with the refinement and optional forms
of section 7 that declarations, coercions, and signatures use. A
`named` type is resolved through the unit's declarations by the
checker; `struct` is an inline struct type, as a map value or a
literal has. -/
inductive Ty where
  | int (span : Span) (signed : Bool) (width : Nat)
  | be (span : Span) (width : Nat)
  | bool (span : Span)
  | spinlock (span : Span)
  | named (span : Span) (name : String)
  | struct (span : Span) (fields : List Field)
  | array (span : Span) (elem : Ty) (len : Expr)
  | ref (span : Span) (t : Ty)
  | view (span : Span) (t : Ty)
  | own (span : Span) (t : Ty)
  /-- `{ v: T | P }`. -/
  | refined (span : Span) (var : String) (base : Ty) (pred : Expr)
  /-- `T?`, the result type of a fallible function. -/
  | opt (span : Span) (t : Ty)

inductive Field where
  | mk (span : Span) (name : String) (ty : Ty) (pred : Option Expr)

/-- Expressions `e` of section 18.1. Literals keep their text so that
printed Core shows `0x10` as written. -/
inductive Expr where
  | lit (span : Span) (value : Nat) (text : String)
  /-- A character literal, which denotes a `u8`. -/
  | char (span : Span) (value : UInt8)
  | bool (span : Span) (value : Bool)
  /-- The format argument of `printk`. -/
  | str (span : Span) (value : String)
  /-- A variable, a constant, a configuration constant, or a verdict
  name; `x` of 18.1. -/
  | var (span : Span) (name : String)
  | arith (span : Span) (op : ArithOp) (l r : Expr)
  | cmp (span : Span) (op : CmpOp) (l r : Expr)
  | not (span : Span) (e : Expr)
  | and (span : Span) (l r : Expr)
  | or (span : Span) (l r : Expr)
  | cast (span : Span) (e : Expr) (ty : Ty)
  | hton (span : Span) (e : Expr)
  | ntoh (span : Span) (e : Expr)
  /-- `rd p`, the load of a scalar place. -/
  | read (span : Span) (p : Place)
  /-- `size T`, the padded size of a type. -/
  | size (span : Span) (ty : Ty)
  | move (span : Span) (name : String)
  | call (span : Span) (f : String) (args : List Arg)
  /-- The negative return of the helper whose `try` failed; the
  default reason of the `helper` kind (section 10.5). -/
  | errno (span : Span)
  /-- A surface form with no meaning where it stands, such as a
  fallible operation outside the positions of section 10.2. The
  message is the diagnostic; typing has no rule for this node. -/
  | invalid (span : Span) (msg : String)

/-- Places `p` of section 18.1. -/
inductive Place where
  | var (span : Span) (name : String)
  | field (span : Span) (p : Place) (name : String)
  | index (span : Span) (p : Place) (idx : Expr)
  /-- `m[e]`, a slot of an array-kind map. -/
  | slot (span : Span) (map : String) (idx : Expr)
  /-- `deref x`; the operand is an expression so that `*` applied to
  something other than a name desugars, and typing then rejects it. -/
  | deref (span : Span) (e : Expr)
  | invalid (span : Span) (msg : String)

/-- An argument of a call. Whether a place argument is read or passed
by reference depends on the parameter's type, so the desugaring keeps
every place-shaped argument a place. A map is an argument only of the
map operations. -/
inductive Arg where
  | val (e : Expr)
  | place (p : Place)
  | map (span : Span) (name : String)

/-- The fallible operations `F` of section 18.1. Each has the failure
kind section 8.3 fixes for it; `acquire` takes its kind from the
resource table. -/
inductive Fallible where
  | view (span : Span) (off : Expr) (ty : Ty)
  | lookup (span : Span) (map : String) (key : Place)
  | loadw (span : Span) (p : Place)
  | call (span : Span) (f : String) (args : List Arg)
  /-- `acquire R f<T>(a...)`: the resource, the acquiring function or
  constructor, its type argument, and its arguments. -/
  | acquire (span : Span) (res : Resource) (f : String) (tyArg : Option Ty)
      (args : List Arg)
  | callopt (span : Span) (f : String) (args : List Arg)
  | coerce (span : Span) (e : Expr) (ty : Ty)

end

deriving instance Repr, Inhabited for Ty, Field, Expr, Place, Arg, Fallible

def Ty.span : Ty → Span
  | .int s .. | .be s .. | .bool s | .spinlock s | .named s .. | .struct s ..
  | .array s .. | .ref s .. | .view s .. | .own s .. | .refined s ..
  | .opt s .. => s

def Field.span : Field → Span
  | .mk s .. => s

def Field.name : Field → String
  | .mk _ n .. => n

def Field.ty : Field → Ty
  | .mk _ _ t _ => t

def Field.pred : Field → Option Expr
  | .mk _ _ _ p => p

def Expr.span : Expr → Span
  | .lit s .. | .char s .. | .bool s .. | .str s .. | .var s .. | .arith s ..
  | .cmp s .. | .not s .. | .and s .. | .or s .. | .cast s .. | .hton s ..
  | .ntoh s .. | .read s .. | .size s .. | .move s .. | .call s ..
  | .errno s | .invalid s .. => s

def Place.span : Place → Span
  | .var s .. | .field s .. | .index s .. | .slot s .. | .deref s ..
  | .invalid s .. => s

def Arg.span : Arg → Span
  | .val e => e.span
  | .place p => p.span
  | .map s _ => s

def Fallible.span : Fallible → Span
  | .view s .. | .lookup s .. | .loadw s .. | .call s .. | .acquire s ..
  | .callopt s .. | .coerce s .. => s

/-- The failure kind of a fallible operation other than `acquire`,
whose kind is a column of the resource table (section 11.2). -/
def Fallible.kind? : Fallible → Option Kind
  | .view .. => some .short_packet
  | .lookup .. => some .missing
  | .loadw .. => some .invariant
  | .call .. => some .helper
  | .callopt .. => some .missing
  | .coerce .. => some .bound
  | .acquire .. => none

/-- A field initializer of a struct literal. -/
structure FieldInit where
  span  : Span
  name  : String
  value : Expr
  deriving Repr, Inhabited

/-- The right side of a binding. Whether a place is read into the name
or named by it depends on its type, so the desugaring keeps the place
(spec/ISSUES.md, entry 11). A struct literal names a new stack place
(section 8.2). -/
inductive Init where
  | expr (e : Expr)
  | place (p : Place)
  | lit (span : Span) (fields : List FieldInit)
  deriving Repr, Inhabited

def Init.span : Init → Span
  | .expr e => e.span
  | .place p => p.span
  | .lit s _ => s

/-- Statements `s` of section 18.1. A block is a list; `skip` is the
empty list and `s ; s` is concatenation. -/
inductive Stmt where
  /-- `let x = e` and `var x = e`, with the declared type when the
  source gave one. `_` binds nothing and takes a call's result. -/
  | «let» (span : Span) (mutable : Bool) (name : String) (ty : Option Ty)
      (init : Init)
  | assign (span : Span) (target : Place) (value : Expr)
  | ite (span : Span) (cond : Expr) (thn els : List Stmt)
  | loop (span : Span) (count : Expr) (body : List Stmt)
  | «for» (span : Span) (var : String) (lo hi : Expr) (body : List Stmt)
  | brk (span : Span)
  | cont (span : Span)
  | ret (span : Span) (value : Option Expr)
  | raise (span : Span) (kind : Kind) (reason : Expr)
  /-- `try x = F then s else s`. `elseExits` records that the `else`
  came from a tail, which must exit (section 10.3), and not from
  `if let`, which need not. -/
  | «try» (span : Span) (name : String) (op : Fallible) (thn els : List Stmt)
      (elseExits : Bool)
  /-- `hold R x = acquire ... then body else els`; `els` is absent for
  an acquisition that cannot fail. -/
  | hold (span : Span) (res : Resource) (name : Option String)
      (acq : Fallible) (body : List Stmt) (els : Option (List Stmt))
  /-- `x = atomic op p (e...)`, the atomic updates of section 8.5. -/
  | atomic (span : Span) (name : Option String) (op : AtomicOp)
      (target : Place) (args : List Expr)
  | invalid (span : Span) (msg : String)
  deriving Repr, Inhabited

def Stmt.span : Stmt → Span
  | .«let» s .. | .assign s .. | .ite s .. | .loop s .. | .«for» s ..
  | .brk s | .cont s | .ret s .. | .raise s .. | .«try» s .. | .hold s ..
  | .atomic s .. | .invalid s .. => s

/-! ### Declarations -/

/-- A region `r` of section 18.1, as a preserved region `W` names it;
`maps except ...` is kept so that the checker can resolve the names. -/
inductive Region where
  | pkt (span : Span) (range : Option (Expr × Expr))
  | map (span : Span) (name : String)
  | mapsExcept (span : Span) (names : List String)
  | ctx (span : Span) (field : String)
  deriving Repr, Inhabited

def Region.span : Region → Span
  | .pkt s .. | .map s .. | .mapsExcept s .. | .ctx s .. => s

/-- The effects of section 12. -/
inductive Effect where
  | call | resize | sleep | fail
  | write (r : Region)
  deriving Repr, Inhabited

structure Param where
  span : Span
  name : String
  ty   : Ty
  pred : Option Expr
  deriving Repr, Inhabited

/-- A function, kept in Core with its signature (section 16). The
result is `refined` for `-> r: T where P` and `opt` for `-> T?`. -/
structure Fn where
  span   : Span
  name   : String
  params : List Param
  ret    : Option Ty
  fails  : Bool
  body   : List Stmt
  deriving Repr, Inhabited

inductive MapKind where
  | array (n : Expr) (value : Ty)
  | percpu (n : Expr) (value : Ty)
  | hash (n : Expr) (key value : Ty)
  | ringbuf (n : Expr)
  deriving Repr, Inhabited

structure MapDecl where
  span : Span
  name : String
  kind : MapKind
  deriving Repr, Inhabited

/-- `const x = e` takes its type from each use when `ty` is absent
(section 6). -/
structure ConstDecl where
  span  : Span
  name  : String
  ty    : Option Ty
  value : Expr
  deriving Repr, Inhabited

structure ConfigDecl where
  span : Span
  name : String
  ty   : Ty
  init : Option Expr
  deriving Repr, Inhabited

structure TypeDecl where
  span : Span
  name : String
  ty   : Ty
  deriving Repr, Inhabited

/-- A named contract (section 14.2). -/
structure Contract where
  span      : Span
  name      : String
  kind      : String
  verdicts  : Option (List (Span × String))
  preserved : List Region
  deriving Repr, Inhabited

/-- One row of a program's handler table `H`. -/
structure Handler where
  span : Span
  kind : Kind
  body : List Stmt
  deriving Repr, Inhabited

/-- `program(S, W, H, s)` of section 18.1. `verdicts` is `S` after the
implemented contract's clause is merged in, or `none` for no clause;
`preserved` is `W`; `handlers` is `H`, total over the six kinds. -/
structure Program where
  span       : Span
  name       : String
  kind       : String
  implements : Option (Span × String)
  verdicts   : Option (List (Span × String))
  preserved  : List Region
  handlers   : List Handler
  body       : List Stmt
  deriving Repr, Inhabited

/-- A desugared compilation unit. -/
structure CompUnit where
  license   : Option (Span × String)
  types     : List TypeDecl
  consts    : List ConstDecl
  configs   : List ConfigDecl
  maps      : List MapDecl
  fns       : List Fn
  contracts : List Contract
  programs  : List Program
  deriving Repr, Inhabited

end Koit.Core
