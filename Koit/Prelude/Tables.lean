import Koit.Core.Syntax

/-!
The prelude's row types: the six tables a kernel version supplies to
the core, which the checker, the interpreter, and the lowering all
read. Program kinds with their verdicts, default failure, packet
access, and sleepability; context fields per kind; calls with
signatures, effects, availability, and license; resources with their
acquisition and its argument form, release, forbidden effects, and
nesting; region kinds; slot types with their layout and homes. The
hand-written value for stage 1 is `Stage1.lean`; a generator will later
emit a value of the same type from the kernel's own sources.
-/

namespace Koit.Prelude

open Koit (Span)
open Koit.Core
/-- The span every prelude node carries: a prelude row has no source
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

/-! ### Table 1, program kinds -/

/-- What a program returns on a failure of a kind it has no handler
for. -/
inductive DefaultExit where
  | verdict (name : String)
  | value (v : Int)
  deriving Repr, Inhabited

/-- Table 2, one context field. -/
structure CtxField where
  name     : String
  ty       : Ty
  writable : Bool
  deriving Repr, Inhabited

structure KindRow where
  name    : String
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
  in `verdicts`; a statement with no row is not available. -/
  sugar : List (String × String)
  defaultExit : DefaultExit
  /-- Whether views into the packet may be written, for kinds that
  have one: the kernel's per-type packet writability. -/
  pktWritable : Bool := false
  sleep : Bool
  ctx : List CtxField
  deriving Repr, Inhabited

/-! ### Table 3, calls -/

/-- How a call is typed: by a signature, or by a rule of the checker
keyed by the name, for the generic builtins whose
types depend on their arguments. -/
inductive Sig where
  | fn (params : List Param) (ret : Option Ty)
  | builtin
  deriving Repr, Inhabited

structure CallRow where
  name : String
  sig  : Sig
  /-- The effects; the write effects of `copy`, `fill`,
  `insert`, `delete`, and the atomics are those of their place or map
  argument and are computed at the call. -/
  effects : List Effect
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
  deriving Repr, Inhabited

def callRow (name : String) (sig : Sig) (effects : List Effect)
    (kernel : String) (fails : Option Kind := none)
    (acquires : Option Resource := none) (kinds : List String := [])
    (gplOnly : Bool := false) : CallRow :=
  { name, sig, effects, fails, acquires, kinds, gplOnly, kernel }

/-! ### Table 4, resources -/

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

structure ResourceRow where
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
  row. -/
  forbidden : List Effect
  /-- Whether another instance of the same resource may be held. -/
  nesting : Nesting
  guards : String
  deriving Repr, Inhabited

/-! ### Table 5, region kinds -/

structure RegionRow where
  name : String
  /-- Whether places in it are obtained statically or through views. -/
  dynamic : Bool
  /-- Whether places in it may be stored to; the packet's writability
  is per kind, `KindRow.pktWritable`. -/
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

/-! ### Table 6, slot types -/

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
structure SlotRow where
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

/-- The kernel's limit on special fields in one value, `BTF_FIELDS_MAX`. -/
def maxSlots : Nat := 11

end Koit.Prelude

open Koit.Prelude Koit.Core in
/-- The six tables of one kernel version, with its constants and
types. -/
structure Koit.Prelude where
  kernel    : String
  kinds     : List KindRow
  calls     : List CallRow
  resources : List ResourceRow
  regions   : List RegionRow
  slots     : List SlotRow
  consts    : List ConstDecl
  types     : List TypeDecl
  deriving Inhabited

namespace Koit.Prelude

open Koit.Core

def kind? (p : Prelude) (name : String) : Option KindRow :=
  p.kinds.find? (·.name == name)

def call? (p : Prelude) (name : String) : Option CallRow :=
  p.calls.find? (·.name == name)

def resource? (p : Prelude) (r : Resource) : Option ResourceRow :=
  p.resources.find? (·.res == r)

/-- The resource a surface acquirer such as `lock` or `sk_lookup_tcp`
denotes. -/
def acquirer? (p : Prelude) (name : String) : Option ResourceRow :=
  p.resources.find? (·.acquirers.contains name)

def const? (p : Prelude) (name : String) : Option ConstDecl :=
  p.consts.find? (·.name == name)

def type? (p : Prelude) (name : String) : Option TypeDecl :=
  p.types.find? (·.name == name)

def slot? (p : Prelude) (name : String) : Option SlotRow :=
  p.slots.find? (·.name == name)

def region? (p : Prelude) (name : String) : Option RegionRow :=
  p.regions.find? (·.name == name)

end Koit.Prelude

