import Koit.Core.Syntax

/-!
The prelude's row types: the five tables a kernel version supplies to
the core, which the checker, the interpreter, and the lowering all
read. Program kinds with their verdicts, default failure, and
sleepability; context fields per kind; calls with signatures, effects,
availability, and license; resources with their acquisition, release,
forbidden effects, and nesting; region kinds. The hand-written value
for stage 1 is `Stage1.lean`; a generator will later emit a value of
the same type from the kernel's own sources.
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

structure ResourceRow where
  res : Resource
  /-- The surface spellings that acquire it after `hold`. -/
  acquirers : List String
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
  guard : Option Guard
  note : String
  deriving Repr, Inhabited

end Koit.Prelude

open Koit.Prelude Koit.Core in
/-- The five tables of one kernel version. -/
structure Koit.Prelude where
  kernel    : String
  kinds     : List KindRow
  calls     : List CallRow
  resources : List ResourceRow
  regions   : List RegionRow
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

end Koit.Prelude

