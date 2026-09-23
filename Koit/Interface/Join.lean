import Koit.Interface.Decls
import Koit.Core.Print

/-!
The join of the interface's two sides. From the hand-written koit
side, a `Spec`, and a transcribed kernel side, a `Kernel.Side`, the
declarations the compiler reads, with the kernel's numbers and offsets filled
in, or the list of disagreements between the two, which the build
reports as an error. A declaration the kernel simply lacks, a helper or kfunc
it does not have yet, is not a disagreement: the declaration is dropped and
remembered with its reason, so that a program naming it gets a
diagnostic that names the kernel.

What is checked, per call: the kernel function exists; the program
type may call it, following the verifier's own fallback chain; the
layout has the prototype's arity, or at least it for a variadic
helper; each layout entry has the shape the verifier's argument kind
asks for, the context for a context pointer, a size for a constant
size, a place for a pointer, a scalar for anything; the `resize`
effect is claimed exactly when the kernel lists the helper as
changing the packet. Per kind: the program type exists, the section
name is one libbpf maps to it, every context field exists in the
kernel's struct with the width koit gives it, every verdict has a
value. Per resource and constant: the names resolve. The machine's
own builtins are checked the same way.
-/

namespace Koit.Interface

open Koit.Core

/-- Whether an effect set has the `resize` effect. -/
def hasResize (es : List Effect) : Bool :=
  es.any fun e => match e with | .resize => true | _ => false

/-- The width in bytes of a context field's koit type. -/
def ctxBytes : Ty → Option Nat
  | .int _ _ w | .be _ w => some (w / 8)
  | _ => none

/-- Whether a koit parameter passes a scalar rather than a place. -/
partial def scalarTy : Ty → Bool
  | .int .. | .be .. | .bool .. => true
  | .refined _ _ t _ => scalarTy t
  | _ => false

/-- The shape the verifier's argument kind asks for, from the prefix
of the kind's name as `bpf_func_proto` spells it. -/
inductive ArgShape where
  | ctx | size | map | ptr | scalar
  deriving BEq, Repr

def ArgShape.describe : ArgShape → String
  | .ctx => "the context" | .size => "a size" | .map => "a map"
  | .ptr => "a pointer" | .scalar => "a scalar"

def argShape (kind : String) : ArgShape :=
  if kind.startsWith "ARG_PTR_TO_CTX" then .ctx
  else if kind.startsWith "ARG_CONST_SIZE" then .size
  else if kind.startsWith "ARG_CONST_MAP_PTR" then .map
  else if kind.startsWith "ARG_ANYTHING" || kind.startsWith "ARG_CONST_ALLOC_SIZE" then .scalar
  else .ptr

/-- Whether a layout entry may fill an argument of the shape; koit's
parameters, when the declaration has a signature, say whether an argument is
a scalar or a place. -/
def entryFits (params : Option (List Param)) : AbiArg → ArgShape → Bool
  | .ctx, s => s == .ctx
  | .argSize _, s => s == .size
  | .const _, s => s == .scalar || s == .size
  | .fmt, s => s == .ptr
  | .arg i, s =>
    match params with
    | none => s != .ctx && s != .size
    | some ps =>
      match ps[i]? with
      | some p => if scalarTy p.ty then s == .scalar else s == .ptr || s == .map
      | none => false

/-- The disagreements between a layout and the kernel's prototype. -/
def checkLayout (what : String) (params : Option (List Param)) (abi : List AbiArg)
    (proto : Kernel.Proto) (variadic : Bool) : List String :=
  let arity :=
    if variadic then
      if abi.length < proto.args.length then
        [s!"{what}: the layout has {abi.length} arguments; {proto.name} takes at least {proto.args.length}"]
      else []
    else if abi.length != proto.args.length then
      [s!"{what}: the layout has {abi.length} arguments; {proto.name} takes {proto.args.length}"]
    else []
  let shapes := (abi.zip proto.args).filterMap fun (e, kind) =>
    if entryFits params e (argShape kind) then none
    else some s!"{what}: layout entry `{repr e}` where {proto.name} asks for {(argShape kind).describe} ({kind})"
  arity ++ shapes

/-- A kernel value as a `u32`, the kernel's `-1` as `0xFFFFFFFF`. -/
def valueU32 (v : Int) : Nat :=
  if v < 0 then (2 ^ 32 + v).toNat % 2 ^ 32 else v.toNat % 2 ^ 32

def constDecl (name : String) (value : Expr) : ConstDecl :=
  { span := noSpan, name, ty := none, value }

def lit (n : Nat) : Expr := .lit noSpan n (toString n)

def hexLit (n : Nat) : Expr :=
  .lit noSpan n ("0x" ++ String.ofList ((Nat.toDigits 16 n).map Char.toUpper))

/-- Whether a kernel function name, `bpf_spin_unlock`, is a helper or
a kfunc of the tag. -/
def Kernel.Side.hasFunction (k : Kernel.Side) (name : String) : Bool :=
  (k.kfunc? name).isSome ||
    (name.startsWith "bpf_" && (k.helper? (name.drop 4).toString).isSome)

/-- The join, or the disagreements. `builtins` are the machine's own
layouts by helper name, checked against every kind of the spec. -/
def join (spec : Spec) (k : Kernel.Side) (builtins : List (String × List AbiArg)) :
    Except String Interface := do
  let mut problems : List String := []
  let mut missing : List (String × String) := []
  let problem (s : String) : List String := [s]

  -- kinds
  let mut kinds : List KindDecl := []
  let mut enums : List EnumDecl := []
  for ks in spec.kinds do
    match k.progType? ks.progType with
    | none => problems := problems ++ problem s!"kind `{ks.name}`: {k.tag} has no {ks.progType}"
    | some pt =>
      unless pt.sections.contains ks.section_ do
        problems := problems ++ problem
          s!"kind `{ks.name}`: section \"{ks.section_}\" is not one libbpf maps to {pt.name}, which has {pt.sections}"
      let cs? := pt.ctx.bind k.ctx?
      let mut fields : List CtxField := []
      for f in ks.ctx do
        match cs? with
        | none => problems := problems ++ problem s!"kind `{ks.name}`: {pt.name} has no context struct for `ctx.{f.name}`"
        | some cs =>
          match cs.fields.find? (·.name == f.name) with
          | none => problems := problems ++ problem s!"kind `{ks.name}`: {cs.name} has no field `{f.name}`"
          | some kf =>
            unless ctxBytes f.ty == some kf.size do
              problems := problems ++ problem
                s!"kind `{ks.name}`: `ctx.{f.name}` is {kf.size} bytes in {cs.name}, typed `{f.ty.print}`"
            fields := fields ++ [{ name := f.name, ty := f.ty, offset := kf.offset, writable := f.writable }]
      let mut bounds : List CtxBound := []
      for (b, isEnd) in ks.ctxBounds do
        match cs?.bind fun cs => cs.fields.find? (·.name == b) with
        | none => problems := problems ++ problem s!"kind `{ks.name}`: no context field `{b}` for the packet bound"
        | some kf => bounds := bounds ++ [{ name := b, offset := kf.offset, isEnd }]
      let mut verdicts : List (String × Nat) := []
      for (v, kv) in ks.verdicts do
        match k.value? kv with
        | none => problems := problems ++ problem s!"kind `{ks.name}`: {k.tag} has no value {kv} for verdict `{v}`"
        | some n => verdicts := verdicts ++ [(v, valueU32 n)]
      match ks.defaultExit with
      | .verdict v =>
        unless verdicts.any (·.1 == v) do
          problems := problems ++ problem s!"kind `{ks.name}`: the default exit `{v}` is not a verdict"
      | .value _ => pure ()
      kinds := kinds ++ [{ name := ks.name, progType := ks.progType, section_ := ks.section_,
                           hasPkt := ks.hasPkt,
                           verdictTy := ks.verdictTy, verdicts, sugar := ks.sugar,
                           defaultExit := ks.defaultExit, pktWritable := ks.pktWritable,
                           sleep := ks.sleep, ctx := fields, ctxBounds := bounds }]
      -- the kind's enumeration, its constants the verdicts just joined
      if let some es := ks.verdictEnum then
        enums := enums ++ [{ name := es.name, kernel := es.kernel,
                             width := es.width, constants := verdicts }]

  -- calls
  let allKinds := spec.kinds.map (·.name)
  let progTypeOf (kind : String) : String :=
    ((spec.kinds.find? (·.name == kind)).map (·.progType)).getD ""
  let mut calls : List CallDecl := []
  for cs in spec.calls do
    let wanted := if cs.kinds.isEmpty then allKinds else cs.kinds
    let params : Option (List Param) := match cs.sig with
      | .fn ps _ => some ps
      | .builtin => none
    let mut avail : List String := []
    let mut gpl := false
    let mut implBy : List (String × Impl) := []
    let mut reasons : List String := []
    let mut kernelName := cs.note
    for kind in wanted do
      -- a builtin declaration names its helper in the note; its layout is the
      -- machine's, checked here under the same rules
      let link := match (cs.linkByKind.lookup kind).getD cs.link, cs.sig with
        | .inline, .builtin =>
          if cs.note.startsWith "bpf_" then
            match builtins.lookup (cs.note.drop 4).toString with
            | some abi => Link.helper (cs.note.drop 4).toString abi
            | none => .inline
          else .inline
        | l, _ => l
      let pt := progTypeOf kind
      match link with
      | .inline => avail := avail ++ [kind]
      | .kfunc name abi =>
        kernelName := name
        match k.kfunc? name with
        | none => reasons := reasons ++ [s!"{k.tag} has no kfunc {name}"]
        | some kf =>
          if !(k.kfuncsFor pt).any (·.name == name) then
            reasons := reasons ++ [s!"{name} is not registered for {kind} on {k.tag}"]
          else
            if kf.ret != "" && abi.length != kf.args.length then
              problems := problems ++ problem
                s!"`{cs.name}` in {kind}: the layout has {abi.length} arguments; {name} takes {kf.args.length}"
            -- the clauses the kernel marks with a flag: a required RCU
            -- section on every tag, lock safety only where the flag
            -- exists
            let rcu := kf.flags.contains "KF_RCU_PROTECTED"
            let needsRcu := cs.requires.any (·.name == "rcu")
            if rcu && !needsRcu then
              problems := problems ++ problem
                s!"`{cs.name}`: {k.tag} marks {name} KF_RCU_PROTECTED, but the declaration does not require `rcu`"
            if needsRcu && !rcu then
              problems := problems ++ problem
                s!"`{cs.name}`: the declaration requires `rcu`, but {k.tag} does not mark {name} KF_RCU_PROTECTED"
            if k.hasFlag "KF_SPINLOCK_SAFE" then
              let safe := kf.flags.contains "KF_SPINLOCK_SAFE"
              if safe != cs.lockSafe then
                problems := problems ++ problem
                  s!"`{cs.name}`: {k.tag} {if safe then "marks" else "does not mark"} {name} KF_SPINLOCK_SAFE, but the declaration {if cs.lockSafe then "is" else "is not"} lock-safe"
            avail := avail ++ [kind]
            implBy := implBy ++ [(kind, .kfunc name abi)]
      | .helper name abi =>
        kernelName := "bpf_" ++ name
        match k.helper? name with
        | none => reasons := reasons ++ [s!"{k.tag} has no helper bpf_{name}"]
        | some h =>
          match k.protoFor pt name with
          | none =>
            -- the helper exists, so a claim of availability is koit's error
            problems := problems ++ problem
              s!"`{cs.name}`: bpf_{name} is not available to {kind} ({pt}) on {k.tag}"
          | some proto =>
            let variadic := h.args.any (·.1 == "...")
            problems := problems ++ checkLayout s!"`{cs.name}` in {kind}" params abi proto variadic
            gpl := gpl || proto.gplOnly
            let changes := k.changesPkt.contains name
            if changes && !hasResize cs.effects then
              problems := problems ++ problem
                s!"`{cs.name}`: {k.tag} lists bpf_{name} as changing the packet, but the declaration has no `resize` effect"
            if !changes && hasResize cs.effects then
              problems := problems ++ problem
                s!"`{cs.name}`: the declaration has the `resize` effect, but {k.tag} does not list bpf_{name} as changing the packet"
            avail := avail ++ [kind]
            implBy := implBy ++ [(kind, .helper h.id abi)]
    if avail.isEmpty then
      missing := missing ++ [(cs.name, "; ".intercalate reasons.eraseDups)]
    else
      let restricted := !cs.kinds.isEmpty || avail.length != allKinds.length
      calls := calls ++ [{ name := cs.name, sig := cs.sig, effects := cs.effects, fails := cs.fails,
                           acquires := cs.acquires, kinds := if restricted then avail else [],
                           gplOnly := gpl, kernel := kernelName,
                           lockSafe := cs.lockSafe, requires := cs.requires,
                           impl := match cs.sig with
                             | .builtin => .inline
                             | .fn .. => ((implBy.head?).map (·.2)).getD .inline,
                           implByKind := match cs.sig with
                             | .builtin => []
                             | .fn .. => implBy }]

  -- the machine's builtins, in every kind
  for (name, abi) in builtins do
    match k.helper? name with
    | none => problems := problems ++ problem s!"builtin: {k.tag} has no helper bpf_{name}"
    | some h =>
      for ks in spec.kinds do
        match k.protoFor ks.progType name with
        | none => problems := problems ++ problem s!"builtin: bpf_{name} is not available to {ks.name} on {k.tag}"
        | some proto =>
          problems := problems ++ checkLayout s!"builtin bpf_{name} in {ks.name}" none abi proto
            (h.args.any (·.1 == "..."))

  -- resources: every kernel function named must exist
  let mut resources : List ResourceDecl := []
  for r in spec.resources do
    let names := (r.acquireKernel.toList ++ [r.normalExit, r.abnormalExit]).filter (· != "")
    match names.find? (!k.hasFunction ·) with
    | some n =>
      let why := s!"{k.tag} has no {n}"
      missing := missing ++ [(r.res.name, why)] ++ r.acquirers.map (·, why)
    | none => resources := resources ++ [r]

  -- slots
  for s in spec.slots do
    if s.kernel == "bpf_spin_lock" && s.size != k.spinLockSize then
      problems := problems ++ problem s!"slot `{s.name}`: struct bpf_spin_lock is {k.spinLockSize} bytes on {k.tag}, not {s.size}"

  -- constants
  let mut consts : List ConstDecl := []
  for c in spec.consts do
    match k.value? c.kernel with
    | none => missing := missing ++ [(c.name, s!"{k.tag} has no {c.kernel}")]
    | some v =>
      if v < 0 then
        problems := problems ++ problem s!"constant `{c.name}`: {c.kernel} is {v}, which no literal spells"
      else
        consts := consts ++ [constDecl c.name (if c.hton then .hton noSpan (hexLit v.toNat) else lit v.toNat)]

  unless problems.isEmpty do
    throw ("the koit side of the interface disagrees with " ++ k.tag ++ ":\n  " ++
      "\n  ".intercalate problems)
  return { kernel := k.tag, kinds, calls, resources, regions := spec.regions, slots := spec.slots,
           enums, consts, types := spec.types, side := k, missing }

end Koit.Interface
