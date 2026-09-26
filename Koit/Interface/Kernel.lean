/-!
The kernel side of the interface: what one kernel version says of
itself, transcribed from its sources by `tools/transcribe` into a
file per tag under `Koit/Interface/Kernel/`, never edited by hand.
Nothing here is a decision. The helpers with their numbers and C
prototypes, the verifier's own view of each helper's arguments from
its `bpf_func_proto`, the availability switches per program type as
the source writes them, the kfunc sets and their flags, the program
and map types, the context structs with their offsets, and the
constants the corpus names. The koit side of the interface
(`Declarations.lean`, `KoitSide.lean`) is joined to this by `Join.lean`.
-/

namespace Koit.Interface.Kernel

/-- One helper of `enum bpf_func_id`: its name without the `bpf_`
prefix, its number, and the C prototype of the uapi header's
documentation, the return type and the arguments as text. A variadic
helper ends its arguments with `("...", "")`. -/
structure Helper where
  name : String
  id   : Nat
  ret  : String
  args : List (String × String)
  deriving Repr, BEq, Inhabited

/-- One `bpf_func_proto`: the verifier's view of a helper. The name of
the struct, the C function it calls, `gpl_only`, the return kind, and
the argument kinds `arg1_type` to `arg5_type` as the source spells
them, modifiers included. -/
structure Proto where
  name    : String
  func    : String
  gplOnly : Bool
  ret     : String
  args    : List String
  deriving Repr, BEq, Inhabited

/-- One `get_func_proto` function: for each helper it names, the proto
it returns, and the function its `default` case falls back to, so that
availability is read the way the verifier reads it. -/
structure ProtoFn where
  name     : String
  cases    : List (String × String)
  fallback : Option String
  deriving Repr, BEq, Inhabited

/-- One program type: its enum name and number, the `get_func_proto`
function its verifier ops name, the uapi context struct, the section
names libbpf maps to it, and the kfunc sets registered for it. -/
structure ProgType where
  name     : String
  id       : Nat
  protoFn  : Option String
  ctx      : Option String
  /-- The section names libbpf maps to the type, each with the
  expected attach type the loader passes for it, when the type has
  one: `("cgroup/connect4", some "BPF_CGROUP_INET4_CONNECT")`. -/
  sections : List (String × Option String)
  kfuncSets : List String
  deriving Repr, BEq, Inhabited

/-- Whether libbpf maps the section to the type. -/
def ProgType.hasSection (pt : ProgType) (sec : String) : Bool :=
  pt.sections.any (·.1 == sec)

/-- The attach type libbpf gives the section, when it has one. -/
def ProgType.attachOf (pt : ProgType) (sec : String) : Option String :=
  (pt.sections.find? (·.1 == sec)).bind (·.2)

/-- One kfunc of a `BTF_ID_FLAGS` set, with its flags and the C
prototype of its definition where one was found. -/
structure Kfunc where
  name  : String
  set   : String
  flags : List String
  ret   : String
  args  : List (String × String)
  deriving Repr, BEq, Inhabited

/-- One field of a uapi context struct: name, byte offset, byte size;
an unnamed bit-field pads with an empty name. -/
structure CtxField where
  name   : String
  offset : Nat
  size   : Nat
  deriving Repr, BEq, Inhabited

structure CtxStruct where
  name   : String
  size   : Nat
  fields : List CtxField
  deriving Repr, BEq, Inhabited

/-- The kernel side of one tag. -/
structure Side where
  tag      : String
  tree     : String
  commit   : String
  helpers  : List Helper
  protos   : List Proto
  protoFns : List ProtoFn
  progTypes : List ProgType
  mapTypes : List (String × Nat)
  kfuncs   : List Kfunc
  ctx      : List CtxStruct
  /-- Named values: verdicts, protocol and ethertype numbers, flags. -/
  values   : List (String × Int)
  /-- The C functions `bpf_helper_changes_pkt_data` lists. -/
  changesPkt : List String
  spinLockSize : Nat
  deriving Inhabited

def Side.helper? (k : Side) (name : String) : Option Helper :=
  k.helpers.find? (·.name == name)

def Side.proto? (k : Side) (name : String) : Option Proto :=
  k.protos.find? (·.name == name)

def Side.progType? (k : Side) (name : String) : Option ProgType :=
  k.progTypes.find? (·.name == name)

def Side.value? (k : Side) (name : String) : Option Int :=
  k.values.lookup name

def Side.ctx? (k : Side) (name : String) : Option CtxStruct :=
  k.ctx.find? (·.name == name)

/-- The proto a program type's `get_func_proto` returns for a helper,
following the fallback chain as the verifier does; `none` when no
function on the chain names the helper. The chain is finite, so the
walk is bounded by the number of functions. -/
def Side.protoFor (k : Side) (pt : String) (helper : String) : Option Proto := do
  let t ← k.progType? pt
  let mut fn ← t.protoFn
  for _ in k.protoFns do
    let some f := k.protoFns.find? (·.name == fn) | none
    match f.cases.lookup helper with
    | some p => return ← k.proto? p
    | none =>
      match f.fallback with
      | some g => fn := g
      | none => none
  none

/-- Whether a program type may call a helper at all. -/
def Side.available (k : Side) (pt : String) (helper : String) : Bool :=
  (k.protoFor pt helper).isSome

/-- The kfuncs a program type may call: those of its own sets and of
the sets registered for every type. -/
def Side.kfuncsFor (k : Side) (pt : String) : List Kfunc :=
  let sets := ((k.progType? pt).map (·.kfuncSets)).getD [] ++
    ((k.progType? "BPF_PROG_TYPE_UNSPEC").map (·.kfuncSets)).getD []
  k.kfuncs.filter (sets.contains ·.set)

def Side.kfunc? (k : Side) (name : String) : Option Kfunc :=
  k.kfuncs.find? (·.name == name)

/-- Whether any kfunc of the tag carries the flag, which says the
kernel has it at all. -/
def Side.hasFlag (k : Side) (flag : String) : Bool :=
  k.kfuncs.any (·.flags.contains flag)

end Koit.Interface.Kernel
