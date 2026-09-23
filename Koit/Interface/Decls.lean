import Koit.Core.Syntax
import Koit.Interface.Kernel

/-!
The interface's declaration types: what a kernel version declares to
the core, which the checker, the interpreter, and the lowering all
read: program kinds with their verdicts, default failure, packet
access, and sleepability; context fields per kind; calls with
signatures, effects, availability, and license; resources with their
acquisition and its argument form, release, forbidden effects, and
nesting; region kinds; slot types with their layout and homes.

Two layers. The joined declarations below (`KindDecl`, `CallDecl`, ...) are
what the compiler reads, complete with the kernel's numbers and
offsets. They are computed, never written: `Join.lean` fills them
from the koit side, the hand-written `Spec` at the end of this file,
which decides how each kernel operation is typed and names the
kernel function it corresponds to, and from the kernel side
(`Kernel.lean`), transcribed from the kernel's sources. The join
checks the two against each other, so a hand-written correspondence
that disagrees with the kernel's own prototype is a build error.
-/

namespace Koit.Interface

open Koit (Span)
open Koit.Core
/-- The span every interface node carries: a interface declaration has no source
position, and a diagnostic about one names the call site instead. -/
def noSpan : Span := Span.point Koit.Pos.origin

/-! ### Type shorthands -/

def tU8  : Ty := .int noSpan false 8
def tU16 : Ty := .int noSpan false 16
def tU32 : Ty := .int noSpan false 32
def tU64 : Ty := .int noSpan false 64
def tI32 : Ty := .int noSpan true 32
def tBe16 : Ty := .be noSpan 16
def tBe32 : Ty := .be noSpan 32

def field (name : String) (ty : Ty) : Field := .mk noSpan name ty none

def param (name : String) (ty : Ty) (pred : Option Expr := none) : Param :=
  { span := noSpan, name, ty, pred }

/-! ### The program kinds -/

/-- What a program returns on a failure of a kind it has no handler
for. -/
inductive DefaultExit where
  | verdict (name : String)
  | value (v : Int)
  deriving Repr, Inhabited

/-- A context field the source can name: `ctx.f`. -/
structure CtxField where
  name     : String
  ty       : Ty
  /-- The field's offset in the kernel's context struct, in bytes,
  which the lowering emits and the target machine checks; no
  source-level surface shows it. The width is the type's. -/
  offset   : Nat
  writable : Bool
  deriving Repr, Inhabited

/-- The other fields of a packet kind's context: `data` and
`data_end`, which the kernel converts to packet pointers when a
program loads them. They are fields of the same context by offset, so
that the machine admits the load, but the source never names them;
it reaches the packet through views. -/
structure CtxBound where
  name   : String
  offset : Nat
  /-- The end of the packet rather than its start. -/
  isEnd  : Bool
  deriving Repr, Inhabited

structure KindDecl where
  name    : String
  /-- The kernel's program type, `BPF_PROG_TYPE_XDP`, the key into
  the kernel side. -/
  progType : String := ""
  /-- The libbpf section name the lowering emits. -/
  section_ : String
  /-- Whether the packet region exists, so `pkt` is in scope. -/
  hasPkt  : Bool
  /-- The verdict type: `u32` restricted to `verdicts` for packet
  kinds, `i32` for `syscall`. -/
  verdictTy : Ty
  /-- The named verdicts with the values the kernel gives them. -/
  verdicts : List (String × Nat)
  /-- The verdict statements `pass`, `drop`, `tx`, `abort` as names
  in `verdicts`; a statement with no declaration is not available. -/
  sugar : List (String × String)
  defaultExit : DefaultExit
  /-- Whether views into the packet may be written, for kinds that
  have one: the kernel's per-type packet writability. -/
  pktWritable : Bool := false
  sleep : Bool
  ctx : List CtxField
  /-- The location-yielding declarations of a packet kind's context. -/
  ctxBounds : List CtxBound := []
  deriving Repr, Inhabited

/-! ### The calls -/

/-- How a call is typed: by a signature, or by a rule of the checker
keyed by the name, for the generic builtins whose
types depend on their arguments. -/
inductive Sig where
  | fn (params : List Param) (ret : Option Ty)
  | builtin
  deriving Repr, Inhabited

/-- One argument of a kernel function as the kernel takes it: the
`i`-th argument of the koit declaration, the program's context, a constant,
the byte size of the `i`-th argument's place, or the format of
`printk`. -/
inductive AbiArg where
  | arg (i : Nat)
  | ctx
  | const (k : Int)
  | argSize (i : Nat)
  | fmt
  deriving Repr, BEq, DecidableEq, Inhabited

/-- How a declaration reaches the kernel: a helper by its number with the
layout of its arguments, a kfunc by name with the layout, or an
inline sequence of instructions with no call at all. -/
inductive Impl where
  | helper (id : Nat) (abi : List AbiArg)
  | kfunc (name : String) (abi : List AbiArg)
  | inline
  deriving Repr, Inhabited

def Impl.abi : Impl → List AbiArg
  | .helper _ abi | .kfunc _ abi => abi
  | .inline => []

structure CallDecl where
  name : String
  sig  : Sig
  /-- The effects; the write effects of `copy`, `fill`,
  `insert`, `delete`, and the atomics are those of their place or map
  argument and are computed at the call. -/
  effects : List Effect
  /-- Whether the kernel admits the call while a spin lock is held:
  `bpf_spin_unlock`, `bpf_kptr_xchg`, and the kfuncs the verifier
  lists, `KF_SPINLOCK_SAFE` where the kernel has the flag. -/
  lockSafe : Bool := false
  /-- The resources that must be held where the call runs, as the
  kernel requires an RCU section around `KF_RCU_PROTECTED` kfuncs. -/
  requires : List Resource := []
  /-- The parameter the result is a second name for: a socket cast
  yields a name derived from its argument, bound inside that name's
  scope, guarded by it, and never an owner. -/
  derivedFrom : Option String := none
  /-- The failure kind when the call is fallible. -/
  fails : Option Kind
  /-- The resource the result must be bound to with `hold`. -/
  acquires : Option Resource
  /-- The program kinds where the call is available; empty means all. -/
  kinds : List String
  /-- `gpl_only` in the helper's `bpf_func_proto`. -/
  gplOnly : Bool
  /-- The kernel helper, kfunc, or instruction behind the call. -/
  kernel : String
  /-- How the call reaches the kernel: the helper's number and the
  layout of its arguments, which the allocation materializes and the
  encoder writes; no source-level surface shows it. -/
  impl : Impl := .inline
  /-- The implementation in a kind where it differs from `impl`, as
  the resizes' helpers do between `xdp` and `tc`. -/
  implByKind : List (String × Impl) := []
  deriving Repr, Inhabited

def callDecl (name : String) (sig : Sig) (effects : List Effect)
    (kernel : String) (fails : Option Kind := none)
    (acquires : Option Resource := none) (kinds : List String := [])
    (gplOnly : Bool := false) (impl : Impl := .inline)
    (implByKind : List (String × Impl) := []) : CallDecl :=
  { name, sig, effects, fails, acquires, kinds, gplOnly, kernel, impl, implByKind }

/-- The implementation of a declaration in a kind. -/
def CallDecl.implIn (decl : CallDecl) (kind : String) : Impl :=
  (decl.implByKind.lookup kind).getD decl.impl

/-- Whether the declaration is computed inline, with no kernel call. -/
def CallDecl.isInline (decl : CallDecl) : Bool :=
  match decl.impl with
  | .inline => true
  | _ => false

/-! ### The resources -/

inductive Nesting where
  | no | counted | lifo | yes
  deriving Repr, BEq, Inhabited

/-- What an acquisition takes: a place of a slot type (`lock(p)`),
nothing (`rcu`), or the parameters of the acquiring kernel function
(`sk_lookup_tcp(t)`, `rb.reserve<T>()`). -/
inductive AcqArg where
  | place (slot : String)
  | scope
  | call
  deriving Repr, BEq, DecidableEq, Inhabited

structure ResourceDecl where
  res : Resource
  /-- The resource as a message names it: "a spin lock". -/
  describe : String
  /-- The surface spellings that acquire it after `hold`. -/
  acquirers : List String
  arg : AcqArg
  /-- Whether the acquisition binds a name of type `own T`. -/
  yields : Bool
  fails : Option Kind
  normalExit : String
  abnormalExit : String
  /-- Effects forbidden while held; `sleep` is forbidden under every
  declaration. -/
  forbidden : List Effect
  /-- Whether the kernel admits the acquisition while a spin lock is
  held. -/
  lockSafe : Bool := false
  /-- The resources that must be held where the acquisition runs. -/
  requires : List Resource := []
  /-- The parameter the bound name is derived from, a dynptr clone. -/
  derivedFrom : Option String := none
  /-- The kernel keeps the reference even when the constructor fails,
  a reserved dynptr: the acquisition then cannot fail at the source. -/
  holdsOnFailure : Bool := false
  /-- Whether another instance of the same resource may be held. -/
  nesting : Nesting
  guards : String
  /-- The kernel function a scope declaration's acquisition calls, a kfunc,
  for the encoder. -/
  acquireKernel : Option String := none
  deriving Repr, Inhabited

/-! ### The region kinds -/

structure RegionDecl where
  name : String
  /-- Whether places in it are obtained statically or through views. -/
  dynamic : Bool
  /-- Whether places in it may be stored to; the packet's writability
  is per kind, `KindDecl.pktWritable`. -/
  writable : Bool
  /-- Whether a place is defined before its first read: locals at
  declaration, map values zero-filled, context and packet by the
  kernel. -/
  initialized : Bool
  guard : Option Guard
  /-- For a region of dynamic extent, the largest offset a view may
  lie under: the verifier bounds a pointer's variable offset before
  it sees the test that follows, so an offset the facts do not bound
  is a program that does not load. The packet's is the kernel's
  maximum packet offset. -/
  maxOffset : Option Nat := none
  note : String
  deriving Repr, Inhabited

/-! ### The slot types -/

/-- Where a field of a slot type may live. -/
inductive Home where
  | mapValue | global | object
  deriving Repr, BEq, DecidableEq, Inhabited

def Home.describe : Home → String
  | .mapValue => "a map value" | .global => "global data"
  | .object => "an allocated object"

/-- One slot type: an opaque field type the kernel recognizes in a map
value, global data, or an allocated object, with its layout, its
homes, whether a value holds at most one, and what names it. -/
structure SlotDecl where
  name    : String
  /-- The BTF type name the kernel recognizes. -/
  kernel  : String
  size    : Nat
  align   : Nat
  unique  : Bool
  homes   : List Home
  /-- The acquisition, sink, or program kind that uses the slot, for
  diagnostics: "`lock(p)`". -/
  namedBy : String
  deriving Repr, Inhabited

/-- An enumeration type: a scalar whose values are the named
constants of its declaration and no others. The same shape as a
slot, an opaque type the interface names, differing on one clause: a
slot is not data and an enumeration is. A kind's verdict type is one
of these. -/
structure EnumDecl where
  name      : String
  /-- The enumeration the kernel declares, `enum xdp_action`, or the
  family its constants belong to when the kernel spells them as
  macros. -/
  kernel    : String
  /-- The width its values occupy. -/
  width     : Nat
  /-- The named values, each with its number. -/
  constants : List (String × Nat)
  deriving Repr, Inhabited

/-- The kernel's limit on special fields in one value, `BTF_FIELDS_MAX`. -/
def maxSlots : Nat := 11

end Koit.Interface

open Koit.Interface Koit.Core in
/-- What one kernel version declares, with its constants and
types. -/
structure Koit.Interface where
  /-- The kernel tag, `v6.8`. -/
  kernel    : String
  kinds     : List KindDecl
  calls     : List CallDecl
  resources : List ResourceDecl
  regions   : List RegionDecl
  slots     : List SlotDecl
  enums     : List EnumDecl
  consts    : List ConstDecl
  types     : List TypeDecl
  /-- The kernel side the declarations were joined with. -/
  side      : Kernel.Side
  /-- Declarations of the koit side this kernel lacks, with the reason, for
  the diagnostic that names the kernel. -/
  missing   : List (String × String) := []
  deriving Inhabited

namespace Koit.Interface

open Koit.Core

def enum? (p : Interface) (name : String) : Option EnumDecl :=
  p.enums.find? (·.name == name)

/-- The value a constant of an enumeration names, with its declaration. -/
def enumConst? (p : Interface) (n : String) : Option (EnumDecl × Nat) :=
  p.enums.findSome? fun decl =>
    (decl.constants.lookup n).map fun v => (decl, v)

def kind? (p : Interface) (name : String) : Option KindDecl :=
  p.kinds.find? (·.name == name)

def call? (p : Interface) (name : String) : Option CallDecl :=
  p.calls.find? (·.name == name)

def resource? (p : Interface) (r : Resource) : Option ResourceDecl :=
  p.resources.find? (·.res == r)

/-- The resource a surface acquirer such as `lock` or `sk_lookup_tcp`
denotes. -/
def acquirer? (p : Interface) (name : String) : Option ResourceDecl :=
  p.resources.find? (·.acquirers.contains name)

def const? (p : Interface) (name : String) : Option ConstDecl :=
  p.consts.find? (·.name == name)

def type? (p : Interface) (name : String) : Option TypeDecl :=
  p.types.find? (·.name == name)

def slot? (p : Interface) (name : String) : Option SlotDecl :=
  p.slots.find? (·.name == name)

def region? (p : Interface) (name : String) : Option RegionDecl :=
  p.regions.find? (·.name == name)

/-- Why a name the koit side knows is absent on this kernel. -/
def missing? (p : Interface) (name : String) : Option String :=
  p.missing.lookup name

/-- A helper's number on this kernel, by its name without `bpf_`. -/
def helperId? (p : Interface) (name : String) : Option Nat :=
  (p.side.helper? name).map (·.id)

/-! ### The koit side

The hand-written half of every declaration: what is decided, with the name
of the kernel object it corresponds to and nothing the kernel's
sources state. `Join.lean` turns a `Spec` and a `Kernel.Side` into an
`Interface`. -/

/-- A context field as koit sees it: the kernel side supplies the
offset. -/
structure CtxSpec where
  name     : String
  ty       : Ty
  writable : Bool
  deriving Repr, Inhabited

/-- The koit side of an enumeration declaration: the constants are not
repeated here, since the kind's `verdicts` already state them and the
kernel side supplies their numbers. -/
structure EnumSpec where
  name   : String
  kernel : String
  width  : Nat
  deriving Repr, Inhabited

/-- A program kind: the kernel's program type it corresponds to, the
section name chosen among those libbpf maps to that type, and the
verdicts as pairs of koit's name and the kernel's value name, whose
numbers the kernel side supplies. -/
structure KindSpec where
  name      : String
  progType  : String
  section_  : String
  hasPkt    : Bool
  verdictTy : Ty
  verdicts  : List (String × String)
  /-- The enumeration the verdicts form, when the kind has named
  ones; `syscall`, whose result is a bare `i32`, has none. -/
  verdictEnum : Option EnumSpec := none
  sugar     : List (String × String)
  defaultExit : DefaultExit
  pktWritable : Bool := false
  sleep     : Bool
  ctx       : List CtxSpec
  /-- The location-yielding context declarations by field name, with whether
  the declaration is the packet's end. -/
  ctxBounds : List (String × Bool) := []
  deriving Repr, Inhabited

/-- How a call corresponds to the kernel: a helper by its name
without `bpf_` with the layout of the kernel's arguments in terms of
koit's, a kfunc by name with the layout, or an inline sequence with
no call. The helper's number is the kernel side's. -/
inductive Link where
  | helper (name : String) (abi : List AbiArg)
  | kfunc (name : String) (abi : List AbiArg)
  | inline
  deriving Repr, Inhabited

structure CallSpec where
  name     : String
  sig      : Sig
  effects  : List Effect
  fails    : Option Kind := none
  acquires : Option Resource := none
  /-- The kinds koit offers the call in; empty means every kind the
  kernel does. Checked to be within the kernel's availability. -/
  kinds    : List String := []
  /-- What the declaration is, for the printout: "byte swap". -/
  note     : String := ""
  link     : Link := .inline
  linkByKind : List (String × Link) := []
  /-- The two clauses the kernel marks with a flag where it has one:
  admitted under a spin lock, and the resources it requires held. -/
  lockSafe : Bool := false
  requires : List Resource := []
  derivedFrom : Option String := none
  deriving Repr, Inhabited

/-- A constant by the kernel's name for its value, byte-swapped when
the source uses it in network order. -/
structure ConstSpec where
  name   : String
  kernel : String
  hton   : Bool := false
  deriving Repr, Inhabited

/-- The koit side of the interface. -/
structure Spec where
  kinds     : List KindSpec
  calls     : List CallSpec
  resources : List ResourceDecl
  regions   : List RegionDecl
  slots     : List SlotDecl
  enums     : List EnumDecl
  consts    : List ConstSpec
  types     : List TypeDecl
  deriving Inhabited

end Koit.Interface

