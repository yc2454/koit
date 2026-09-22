import Koit.Check.Types

/-!
Expression, place, call, and fallible-operation typing: the executable
form of the expression and place rules and of the operation premises
of the statement rules, with their demands `F |= P` decided by
entailment over the facts in `K`: the index bound of an array or an
array map, and the refinement a value is checked against, which is a
parameter's precondition at a call. Every rule here is one of (Var),
(Lit), (LitDef), (Arith), (Cmp), (CmpBe), (Cast), (Hton), (Ntoh),
(Sub), (Read), (PVar), (PDeref), (PField), (PIndex), (PArr), (Move),
the call rule of functions, and the result types of the fallible
operations; `Rules.lean` states each as a proposition.

`placeTy` types a place and never demands, since the facts consult it
to learn where a place lives; `placeTyUse` is what a use of a place
goes through, and it demands the bound of every index on the way.

Bidirectional: `synth` gives an expression its type, `check` checks it
against one. A literal, an untyped constant, and `size T` take their
type from the context, so a binary operator types
the operand that has a type of its own first and checks the other
against it, defaulting to `u64` (LitDef) when neither has one.
-/

namespace Koit.Check

open Koit (Span)
open Koit.Core
open Koit.Interface (CallRow Home tU32 tU64)
open Koit.Facts (Origin Facts Scope Shape)

/-- The type of a place, whether it may be written, and where it
lives. -/
structure PlaceInfo where
  ty      : Ty
  mutable : Bool
  origin  : Origin
  deriving Inhabited

/-- What a fallible operation binds: a type, or nothing for an
operation used for its effect or a scope-only resource. -/
structure Bound where
  ty     : Option Ty
  origin : Origin := .stack
  deriving Inhabited

/-- `an xdp`, `a tc`, `a syscall`: the article a kind name takes when
read aloud, letter by letter for `xdp`. -/
def article (k : String) : String :=
  match k.toList with
  | c :: _ => if "aeioux".contains c then "an" else "a"
  | [] => "a"

/-- (Lit): `c` representable in `int(s,w)`. -/
def representable (v : Nat) (signed : Bool) (w : Nat) : Bool :=
  if signed then v < 2 ^ (w - 1) else v < 2 ^ w

/-- Whether an expression takes its type from the context, like a
literal. -/
partial def Env.isPoly (env : Env) : Expr → Bool
  | .lit .. | .size .. => true
  | .var _ n =>
    (env.local? n).isNone &&
      (match env.const? n with
       | some d => d.ty.isNone
       | none => false)
  | .arith _ _ l r => env.isPoly l && env.isPoly r
  | .hton _ e => env.isPoly e
  | _ => false

/-- The environment an untyped constant's value is typed in: the
unit's scope, with the constant marked as being expanded. -/
def constEnv (env : Env) (n : String) (span : Span) : M Env := do
  if env.visiting.contains n then
    err span s!"constant `{n}` is defined in terms of itself"
  return { env.top with visiting := n :: env.visiting }

/-- A type mismatch, with the hint the mismatch calls for. -/
def mismatch (env : Env) (span : Span) (expected found : Ty) : M α := do
  let e := (← env.norm expected)
  let f := (← env.norm found)
  let hint :=
    if f.isPlaceTy then
      ": places are never stored, returned, or compared"
    else if e.isIntTy && f.isIntTy then
      ": no implicit conversions (P4); convert with `as`"
    else
      match e, f with
      | .be .., .int .. =>
        ": a byte-order value is made with `hton`"
      | .int .., .be .. =>
        ": a host-order value is made with `ntoh`"
      | _, _ => ""
  err span s!"expected `{expected.print}`, found `{found.print}`{hint}"

/-- What a name denotes. -/
inductive NameRef where
  | local (l : Local)
  | const (d : ConstDecl)
  | config (d : ConfigDecl)
  | verdict (ty : Ty)

/-- Name resolution in value position: locals, the unit's constants
and configuration, the kind's verdicts, the interface's constants. -/
def resolveName (env : Env) (span : Span) (n : String) : M NameRef := do
  if n == "pkt" then err span "`pkt` is read through views"
  if n == "ctx" then
    err span "`ctx` is read through its fields, `ctx.f`"
  if let some l := env.local? n then return .local l
  if let some d := env.consts.find? (·.name == n) then return .const d
  if let some d := env.config? n then return .config d
  if let some t := env.verdict? n then return .verdict t
  if let some d := env.interface.const? n then return .const d
  if (env.map? n).isSome then
    err span s!"`{n}` is a map: index it with `{n}[i]`, or look it up with \
      `{n}[k]?`"
  if (env.fn? n).isSome then err span s!"`{n}` is a function; call it"
  if (env.type? n).isSome then err span s!"`{n}` is a type, not a value"
  if env.interface.kinds.any (·.verdicts.any (·.1 == n)) then
    match env.kind with
    | some row =>
      err span s!"`{n}` is not a verdict of {article row.name} `{row.name}` \
        program"
    | none =>
      err span s!"`{n}` is a verdict name, available only in a program body \
       "
  err span s!"unknown name `{n}`"

/-- (Arith) applies to integers only; the other types name the rule
they break. -/
def arithOk (span : Span) (tn : Ty) : M Unit :=
  match tn with
  | .int .. => pure ()
  | .be _ w =>
    err span s!"a `be{w}` supports `==`, `!=`, loads, and stores, and \
      nothing else; convert it with `ntoh`"
  | .bool _ =>
    err span "arithmetic takes integers; `bool` values are combined with \
      `&&`, `||`, and `!`"
  | t =>
    if t.isPlaceTy then
      err span s!"arithmetic takes integers; `{t.print}` names a place"
    else err span s!"arithmetic takes integers, found `{t.print}`"

/-- The refinement at the head of a type, through named types: the
refined name, the base, and the predicate. -/
partial def Env.refinement? (env : Env) (t : Ty) (fuel : Nat := 64) :
    M (Option (String × Ty × Expr)) := do
  if fuel == 0 then return none
  match t with
  | .refined _ v base pred => return some (v, base, pred)
  | .named _ n =>
    match env.type? n with
    | some d => env.refinement? d.ty (fuel - 1)
    | none => return none
  | _ => return none

/-- The shape of a head-normal type for the domain. -/
def shapeOf (env : Env) : Ty → Shape
  | .int _ s w => .int s w
  | .bool _ => .bool
  -- an enumeration is an unsigned integer of its row's width for the
  -- domain, which is why admitting its constants adds no theory
  | .enum _ n =>
    match env.interface.enum? n with
    | some row => .int false row.width
    | none => .other
  | _ => .other

/-- What a failed demand says: the site, the predicate, and the two
ways to establish it. -/
def demandMsg (site : String) (P : Expr) : String :=
  s!"{site} demands `{P.printPred}`; the facts here do not entail it: \
    establish it with `check`, or read the value with a marked load"

/-- The bound a view's window must lie under: `e + size(T) <= max`,
with `max` the packet region's largest offset, when the row has one.
The verifier bounds a packet pointer's variable offset before it
reads the comparison that follows, so an offset the facts do not
bound is a program that does not load; a constant offset is entailed
trivially, and a loop-carried one needs a `check` at the head of the
body. -/
def viewOffsetBound (env : Env) (span : Span) (off : Expr) (sz : Nat) :
    Option Expr :=
  (env.interface.region? "pkt").bind fun row => row.maxOffset.map fun mx =>
    .cmp span .le (.arith span .add off (.lit span sz (toString sz)))
      (.lit span mx (toString mx))

/-- `pkt` exists in the packet kinds only. -/
def requirePkt (env : Env) (span : Span) : M Unit :=
  match env.kind with
  | some row =>
    unless row.hasPkt do
      err span s!"`pkt` is available only in a program of a packet kind; \
        {article row.name} `{row.name}` program has no packet"
  | none =>
    err span "`pkt` is available only in a program body of a packet kind \
     "

/-- The diagnostic for a function name nothing declares: the row the
target kernel lacks, with what it lacks; the kernel's own function
koit has no row for yet, by its kernel name with or without `bpf_`;
or simply unknown. -/
def unknownFunction (env : Env) (span : Span) (f : String) : M α := do
  if let some why := env.interface.missing? f then
    err span s!"`{f}` is not on kernel {env.interface.kernel}: {why}"
  let bare := if f.startsWith "bpf_" then (f.drop 4).toString else f
  if (env.interface.side.helper? bare).isSome then
    err span s!"`{f}` is the kernel's helper bpf_{bare}, which koit has no row for \
      yet; the calls koit offers are listed by `koitc interface`"
  if (env.interface.side.kfunc? f).isSome || (env.interface.side.kfunc? ("bpf_" ++ bare)).isSome then
    err span s!"`{f}` is a kfunc of the kernel, which koit has no row for yet; \
      the calls koit offers are listed by `koitc interface`"
  err span s!"unknown function `{f}`"

mutual

partial def synth (env : Env) (K : Ctx) (e : Expr) : M Ty := do
  match e with
  | .lit s v t =>
    if v < 2 ^ 64 then return tU64
    err s s!"`{t}` does not fit in 64 bits"
  | .char s _ => return .int s false 8
  | .bool s _ => return .bool s
  | .str s _ =>
    err s "a string literal appears only as the format argument of \
      `printk`"
  | .var s n =>
    match ← resolveName env s n with
    | .local l => return l.ty
    | .const d =>
      match d.ty with
      | some t => return t
      | none => synth (← constEnv env n s) K d.value
    | .config d => return d.ty
    | .verdict t => return t
  | .arith s _ l r =>
    let t ← if !env.isPoly l then synth env K l
      else if !env.isPoly r then synth env K r
      else pure tU64
    let tn ← env.norm t
    arithOk s tn
    check env K l tn
    check env K r tn
    return tn
  | .cmp s op l r =>
    let t ← if !env.isPoly l then synth env K l
      else if !env.isPoly r then synth env K r
      else pure tU64
    let tn ← env.norm t
    match tn with
    | .int .. => pure ()
    | .be _ w =>
      unless op == .eq || op == .ne do
        err s s!"a `be{w}` compares only with `==` and `!=`"
    | .enum _ n =>
      unless op == .eq || op == .ne do
        err s s!"`{n}` is an enumeration: its values compare only with \
          `==` and `!=`, since they are named and not ordered"
    | .bool _ =>
      err s "comparison takes two integers; `bool` values are combined \
        with `&&`, `||`, and `!`"
    | t' =>
      if t'.isPlaceTy then
        err s s!"`{op.spelling}` compares integers; found a `{t.print}`, and \
          places are never compared"
      err s s!"comparison takes two integers, found `{t.print}`"
    check env K l tn
    check env K r tn
    return .bool s
  | .not s e =>
    check env K e (.bool s)
    return .bool s
  | .and s l r | .or s l r =>
    check env K l (.bool s)
    check env K r (.bool s)
    return .bool s
  | .cast s e t =>
    let tn ← env.norm t
    unless tn.isIntTy do
      err s s!"`as` converts between integer types; `{t.print}` is not one \
       "
    if env.isPoly e then
      check env K e tU64
      return t
    let src ← synth env K e
    match ← env.norm src with
    | .int .. => return t
    | .bool _ =>
      match tn with
      | .int _ false _ => return t
      | _ =>
        err s "`bool as uN` is 0 or 1; the target is unsigned"
    | .be _ w =>
      err s s!"a `be{w}` supports `==`, `!=`, loads, and stores, and \
        nothing else; convert it with `ntoh` first"
    | _ =>
      err s s!"`as` converts between integer types; `{src.print}` is not one \
       "
  | .hton s e =>
    if env.isPoly e then
      err s "the width of `hton` is not determined here; write \
        `hton(e as u16)` or give the context a type"
    let t ← synth env K e
    match ← env.norm t with
    | .int _ false w =>
      if w == 16 || w == 32 || w == 64 then return .be s w
      err s "`hton` takes a `u16`, `u32`, or `u64`"
    | _ => err s s!"`hton` takes an unsigned integer, found `{t.print}`"
  | .ntoh s e =>
    let t ← synth env K e
    match ← env.norm t with
    | .be _ w => return .int s false w
    | _ => err s s!"`ntoh` takes a byte-order value, found `{t.print}`"
  | .read s p =>
    let info ← placeTyUse env K p
    let tn ← env.norm info.ty
    match tn with
    | .int .. | .be .. | .bool .. => return tn
    | .slot _ n =>
      err s s!"a `{n}` is a slot: it is not read; it is named by \
        {env.slotUse n}"
    | _ =>
      err s s!"`{p.print}` is an aggregate of type `{info.ty.print}`: name it \
        with `let`, or read one of its fields (P3)"
  | .size _ t =>
    let _ ← env.layout t
    return tU64
  | .move s x =>
    err s s!"`move {x}` appears only as the argument of a consuming call, a \
      kernel function whose parameter is `own`"
  | .call s f args =>
    match ← synthCall env K s f args false with
    | some t => return t
    | none =>
      err s s!"`{f}` returns nothing; a call without a result is a statement"
  | .errno s =>
    if K.errnoOk then return tU32
    err s "`errno` is the reason of a failed helper call; it is defined only \
      in the `else` of such a call"
  | .invalid s m => err s m

partial def check (env : Env) (K : Ctx) (e : Expr) (t : Ty) : M Unit := do
  -- (Sub) against a refinement: the base, then the predicate of the
  -- value as a demand
  if let some (v, base, pred) ← env.refinement? t then
    check env K e base
    demand env K e.span "the value" (pred.subst v e)
    return ()
  let tn ← env.norm t
  match e with
  | .lit s v text =>
    match tn with
    | .int _ signed w =>
      unless representable v signed w do
        err s s!"`{text}` does not fit in `{tn.print}`"
    | .be _ w =>
      err s s!"a `be{w}` takes only a byte-order value: it compares only with \
        a byte-order value and is stored from one; write `hton({text})` \
       "
    | .bool _ => err s "expected `bool`, found an integer literal"
    | _ => mismatch env s t tU64
  | .char s _ =>
    match tn with
    | .int _ false 8 => pure ()
    | _ => err s s!"a character literal is a `u8`; expected `{t.print}` \
       "
  | .var s n =>
    match ← resolveName env s n with
    | .const d =>
      match d.ty with
      | none => check (← constEnv env n s) K d.value t
      | some ct => unless ← env.eqv ct t do mismatch env s t ct
    | _ =>
      let t' ← synth env K e
      unless ← env.eqv t' t do mismatch env s t t'
  | .arith s _ l r =>
    arithOk s tn
    check env K l tn
    check env K r tn
  | .hton s e' =>
    match tn with
    | .be _ w => check env K e' (.int s false w)
    | _ => err s s!"`hton` yields a byte-order value; expected `{t.print}`"
  | .size s t' =>
    let _ ← env.layout t'
    match tn with
    | .int .. => pure ()
    | _ => err s s!"`size` is an integer; expected `{t.print}`"
  | _ =>
    let t' ← synth env K e
    unless ← env.eqv t' t do mismatch env e.span t t'

/-- (PIndex), (PArr): the index is an unsigned integer. -/
partial def checkIndex (env : Env) (K : Ctx) (i : Expr) : M Unit := do
  if env.isPoly i then
    check env K i tU64
    return ()
  let t ← synth env K i
  match ← env.norm t with
  | .int _ false _ => pure ()
  | _ => err i.span s!"an index must be unsigned; `{i.print}` is `{t.print}` \
     "

/-- A capacity, an array length, or a loop count: a constant expression
of any unsigned type, evaluated in that type. -/
partial def checkCount (env : Env) (K : Ctx) (what : String) (n : Expr) :
    M Unit := do
  unless env.isConstExpr n do
    err n.span s!"{what} must be a constant expression"
  if env.isPoly n then
    check env K n tU64
    return ()
  let t ← synth env K n
  match ← env.norm t with
  | .int _ false _ => pure ()
  | _ => err n.span s!"{what} is an unsigned integer; `{n.print}` is \
      `{t.print}`"

partial def placeTy (env : Env) (K : Ctx) (p : Place) : M PlaceInfo := do
  match p with
  | .var s "ctx" =>
    err s "`ctx` is read through its fields, `ctx.f`"
  | .var s "pkt" => err s "`pkt` is read through views"
  | .var s x =>
    match env.local? x with
    | some l =>
      match l.ty with
      | .ref _ t => return { ty := t, mutable := true, origin := l.origin }
      | .view _ t => return { ty := t, mutable := true, origin := .pkt }
      -- an owned reference names a place of its type
      | .own _ t => return { ty := t, mutable := true, origin := .kernel }
      | t => return { ty := t, mutable := l.mutable, origin := l.origin }
    | none =>
      if (env.map? x).isSome then
        err s s!"`{x}` is a map: index it with `{x}[i]`, or look it up with \
          `{x}[k]?`"
      if (env.const? x).isSome || (env.config? x).isSome then
        err s s!"`{x}` is a constant, not a place"
      if (env.verdict? x).isSome then err s s!"`{x}` is a verdict, not a place"
      err s s!"unknown name `{x}`"
  | .field s (.var _ "ctx") f =>
    match env.kind with
    | none => err s "`ctx` is available only in a program body"
    | some row =>
      match row.ctx.find? (·.name == f) with
      | some cf =>
        return { ty := cf.ty, mutable := cf.writable, origin := .ctx }
      | none =>
        if row.ctx.isEmpty then
          err s s!"the context of {article row.name} `{row.name}` program is \
            opaque"
        err s s!"the context of {article row.name} `{row.name}` program has no \
          field `{f}`; the fields are \
          {", ".intercalate (row.ctx.map (·.name))}"
  | .field s q f =>
    let info ← placeTy env K q
    match ← env.norm info.ty with
    | .struct _ fields =>
      match fields.find? (·.name == f) with
      | some fd =>
        return { ty := fd.ty, mutable := info.mutable, origin := info.origin }
      | none =>
        err s s!"`{q.print}` has no field `{f}`; its type `{info.ty.print}` \
          has {", ".intercalate (fields.map (·.name))}"
    | _ => err s s!"`{q.print}` is a `{info.ty.print}`, which has no fields"
  | .index s q i =>
    let info ← placeTy env K q
    match ← env.norm info.ty with
    | .array _ elem _ =>
      checkIndex env K i
      return { ty := elem, mutable := info.mutable, origin := info.origin }
    | _ => err s s!"`{q.print}` is a `{info.ty.print}`, not an array"
  | .slot s m i =>
    match env.map? m with
    | some d =>
      match d.kind with
      | .array _ v | .percpu _ v =>
        checkIndex env K i
        return { ty := v, mutable := true, origin := .map m }
      | .hash .. =>
        err s s!"the lookup in the hash map `{m}` can fail (kind `missing`): \
          bind it with `?`, `else`, or `if let`"
      | .ringbuf _ =>
        err s s!"`{m}` is a ring buffer, which has no slots; reserve a record \
          with `hold ev = {m}.reserve<T>()`"
    | none => err s s!"unknown map `{m}`"
  | .deref s e =>
    match e with
    | .var vs x =>
      match env.local? x with
      | some l =>
        let (t, origin) ← match l.ty with
          | .ref _ t => pure (t, l.origin)
          | .view _ t => pure (t, Origin.pkt)
          | .own _ t => pure (t, Origin.kernel)
          | t => err vs s!"`*` applies to a reference or view; `{x}` is a \
              `{t.print}`"
        let tn ← env.norm t
        unless tn.isScalar do
          err s s!"`*{x}` reads a scalar; `{x}` names a `{t.print}`, whose \
            fields are read as `{x}.f`"
        return { ty := t, mutable := true, origin }
      | none => err vs s!"unknown name `{x}`"
    | _ => err s "`*` applies to a reference or view name"
  | .invalid s m => err s m

/-- What the facts may ask about names here: the origin and shape of
a place, through `placeTy` without its demands, the value of a
constant, a configuration constant with a default, or a verdict name,
the shape a type denotes, and the size of a type. -/
partial def scope (env : Env) (K : Ctx) : Scope :=
  { place := fun p =>
      match placeTy env K p with
      | .ok info =>
        match env.norm info.ty with
        | .ok tn => some (info.origin, shapeOf env tn)
        | .error _ => some (info.origin, .other)
      | .error _ => none,
    const := fun n =>
      if (env.local? n).isSome then none
      else match env.verdict? n with
        | some _ =>
          env.kind.bind fun row => (row.verdicts.lookup n).map Int.ofNat
        | none => env.evalConst (.var Koit.Facts.noSpan n),
    sort := fun t => (env.norm t).toOption.map (shapeOf env),
    size := fun t => (env.layout t).toOption.map (·.1),
    smt := env.smt }

/-- A demand `F |= P` at `site`. -/
partial def demand (env : Env) (K : Ctx) (span : Span) (site : String)
    (P : Expr) : M Unit := do
  unless Koit.Facts.entails (scope env K) K.facts P do
    err span (demandMsg site P)

/-- (View): the window of `size(T)` bytes at `off` lies under the
packet's maximum offset. -/
partial def viewOffsetDemand (env : Env) (K : Ctx) (span : Span) (off : Expr)
    (sz : Nat) : M Unit := do
  if let some P := viewOffsetBound env span off sz then
    demand env K span "the view offset" P

/-- The index demands along a place: `i < n` for every `p[i]` and
`m[i]`, from the innermost place out. -/
partial def placeDemands (env : Env) (K : Ctx) (p : Place) : M Unit := do
  match p with
  | .field _ q _ => placeDemands env K q
  | .index s q i =>
    placeDemands env K q
    let info ← placeTy env K q
    match ← env.norm info.ty with
    | .array _ _ n => demand env K s "the index" (.cmp s .lt i n)
    | _ => pure ()
  | .slot s m i =>
    match env.map? m with
    | some d =>
      match d.kind with
      | .array n _ | .percpu n _ => demand env K s "the index" (.cmp s .lt i n)
      | _ => pure ()
    | none => pure ()
  | .deref _ e =>
    match e with
    | .read _ q => placeDemands env K q
    | _ => pure ()
  | _ => pure ()

/-- A place at a use: typed, with its index bounds demanded. -/
partial def placeTyUse (env : Env) (K : Ctx) (p : Place) : M PlaceInfo := do
  let info ← placeTy env K p
  placeDemands env K p
  return info

/-- An argument against a parameter. A `const` parameter of a interface
signature takes a constant expression; a refined parameter's
predicate is a precondition, demanded of the argument. -/
partial def checkArg (env : Env) (K : Ctx) (fname : String) (p : Param)
    (arg : Arg) : M Unit := do
  let pname := p.name
  let pty := p.ty
  if p.isConst then
    match arg with
    | .val e =>
      unless env.isConstExpr e do
        err arg.span s!"`{fname}` takes `{pname}` as a constant expression; \
          `{e.print}` is not one"
    | _ =>
      err arg.span s!"`{fname}` takes `{pname}` as a constant expression"
  let pn ← env.norm pty
  match pn, arg with
  | .ref _ t, .place p =>
    let info ← placeTyUse env K p
    if info.origin == .pkt then
      err arg.span s!"`{fname}` takes `{pname}: {pty.print}`, a stack or map \
        place; `{p.print}` is in the packet, so the parameter would be a \
        `view`"
    unless ← env.eqv info.ty t do
      err arg.span s!"`{fname}` takes `{pname}: {pty.print}`; `{p.print}` is a \
        `{info.ty.print}`"
  | .ref .., _ =>
    err arg.span s!"`{fname}` takes `{pname}: {pty.print}`, a place; \
      `{arg.print}` is not one"
  | .view _ t, .place p =>
    let info ← placeTyUse env K p
    unless info.origin == .pkt do
      err arg.span s!"`{fname}` takes `{pname}: {pty.print}`, a place in the \
        packet; `{p.print}` is not one"
    unless ← env.eqv info.ty t do
      err arg.span s!"`{fname}` takes `{pname}: {pty.print}`; `{p.print}` is a \
        view of `{info.ty.print}`"
  | .view .., _ =>
    err arg.span s!"`{fname}` takes `{pname}: {pty.print}`, a view; \
      `{arg.print}` is not one"
  | .own _ t, .val (.move s x) =>
    match env.local? x with
    | some l =>
      match l.ty with
      | .own _ t' =>
        unless ← env.eqv t t' do
          err s s!"`{fname}` consumes `{pname}: {pty.print}`; `{x}` is a \
            `{l.ty.print}`"
      | _ =>
        err s s!"only a name bound by a value-yielding `hold` can be moved; \
          `{x}` is a `{l.ty.print}`"
    | none => err s s!"unknown name `{x}`"
  | .own .., _ =>
    err arg.span s!"`{fname}` consumes its argument `{pname}`: write `move x` \
      for a name bound by `hold`"
  | _, .val e =>
    check env K e pty
    if let some q := p.pred then
      demand env K arg.span s!"the parameter `{pname}` of `{fname}`"
        (q.subst pname e)
  | _, .place p' =>
    let info ← placeTyUse env K p'
    let tn ← env.norm info.ty
    unless tn.isScalar do
      err arg.span s!"`{fname}` takes `{pname}: {pty.print}`, a scalar; \
        `{p'.print}` is an aggregate of type `{info.ty.print}` (P3)"
    unless ← env.eqv tn pn do mismatch env arg.span pty info.ty
    if let some q := p.pred then
      demand env K arg.span s!"the parameter `{pname}` of `{fname}`"
        (q.subst pname (.read p'.span p'))
  | _, .map s m =>
    err s s!"`{fname}` takes `{pname}: {pty.print}`; `{m}` is a map"

/-- A interface call with a signature: availability, license, arity,
arguments. -/
partial def interfaceFn (env : Env) (K : Ctx) (span : Span) (row : CallRow)
    (args : List Arg) : M (Option Ty) := do
  if row.name.startsWith "pkt." then requirePkt env span
  if let some k := env.kind then
    if !row.kinds.isEmpty && !row.kinds.contains k.name then
      err span s!"`{row.name}` is not available in {article k.name} `{k.name}` \
        program on kernel {env.interface.kernel}; it is available in \
        {", ".intercalate (row.kinds.map fun k => s!"`{k}`")}"
  if row.gplOnly && !env.gplCompatible then
    err span s!"`{row.name}` is GPL-only; declare `license \"GPL\"` or another \
      GPL-compatible license"
  match row.sig with
  | .fn params ret =>
    unless args.length == params.length do
      err span s!"`{row.name}` takes {params.length} arguments, {args.length} \
        given"
    for (p, a) in params.zip args do
      checkArg env K row.name p a
    return ret
  | .builtin => builtinCall env K span row.name args

/-- The generic builtins, typed by their arguments. -/
partial def builtinCall (env : Env) (K : Ctx) (span : Span) (f : String)
    (args : List Arg) : M (Option Ty) := do
  match f, args with
  | "printk", .val (.str ..) :: rest =>
    if rest.length > 3 then
      err span "`printk` takes at most three arguments after the format \
       "
    for a in rest do
      let t ← match a with
        | .val e => synth env K e
        | .place p => pure (← placeTy env K p).ty
        | .map s m => err s s!"`printk` prints scalars; `{m}` is a map"
      unless (← env.norm t).isScalar do
        err a.span s!"`printk` prints scalars; `{a.print}` is a `{t.print}`"
    return none
  | "printk", _ =>
    err span "`printk` takes a string literal as its format"
  | "copy", [.place dst, .place src] =>
    let d ← placeTyUse env K dst
    let s ← placeTyUse env K src
    if d.origin == .pkt then
      err dst.span "`copy` writes a stack or map place; the packet is written \
        through a view's fields"
    unless d.mutable do err dst.span s!"`{dst.print}` is immutable"
    unless ← env.eqv d.ty s.ty do
      err span s!"`copy` takes two places of one type; `{dst.print}` is a \
        `{d.ty.print}` and `{src.print}` a `{s.ty.print}`"
    return none
  | "copy", _ => err span "`copy(dst, src)` takes two places"
  | "fill", [.place dst, .val b] =>
    let d ← placeTyUse env K dst
    if d.origin == .pkt then
      err dst.span "`fill` writes a stack or map place"
    unless d.mutable do err dst.span s!"`{dst.print}` is immutable"
    check env K b (.int span false 8)
    return none
  | "fill", _ =>
    err span "`fill(dst, byte)` takes a place and a byte"
  | "insert", [.map ms m, .place k, .place v] =>
    let (kt, vt) ← hashTypes env ms m
    let ki ← placeTyUse env K k
    unless ← env.eqv ki.ty kt do
      err k.span s!"the key of `{m}` is a `{kt.print}`; `{k.print}` is a \
        `{ki.ty.print}`"
    let vi ← placeTyUse env K v
    unless ← env.eqv vi.ty vt do
      err v.span s!"the value of `{m}` is a `{vt.print}`; `{v.print}` is a \
        `{vi.ty.print}`"
    return none
  | "insert", _ =>
    err span "`m.insert(k, v)` takes a key place and a value place \
     "
  | "delete", [.map ms m, .place k] =>
    let (kt, _) ← hashTypes env ms m
    let ki ← placeTyUse env K k
    unless ← env.eqv ki.ty kt do
      err k.span s!"the key of `{m}` is a `{kt.print}`; `{k.print}` is a \
        `{ki.ty.print}`"
    return none
  | "delete", _ => err span "`m.delete(k)` takes a key place"
  | "reserve", _ =>
    err span "`rb.reserve<T>()` yields a resource; bind it with \
      `hold ev = rb.reserve<T>()`"
  | "hton", _ | "ntoh", _ => err span s!"`{f}` takes one argument"
  | _, _ =>
    if (AtomicOp.ofString? f).isSome then
      err span s!"`{f}` appears only as the initializer of a binding or as a \
        statement"
    err span s!"`{f}` has no typing rule"

/-- The key and value types of a hash map. -/
partial def hashTypes (env : Env) (span : Span) (m : String) :
    M (Ty × Ty) := do
  match env.map? m with
  | some d =>
    match d.kind with
    | .hash _ kt vt => return (kt, vt)
    | _ =>
      err span s!"`insert`, `delete`, and `m[k]` are the operations of a hash \
        map; `{m}` is not one"
  | none => err span s!"unknown map `{m}`"

/-- A call, in a plain position or, with `fallible`, in a `try`:
a function of the unit, or a interface call. Returns the result type. -/
partial def synthCall (env : Env) (K : Ctx) (span : Span) (f : String)
    (args : List Arg) (fallible : Bool) : M (Option Ty) := do
  if let some d := env.fn? f then
    if fallible then
      err span s!"`{f}` is a function of the unit; only a function returning \
        `T?` is a fallible operation, and its failures otherwise go to the \
        handler"
    unless args.length == d.params.length do
      err span s!"`{f}` takes {d.params.length} arguments, {args.length} given"
    for (p, a) in d.params.zip args do
      checkArg env K f p a
    if d.fails && !K.mayFail then
      err span s!"`{f}` may fail; a call to it is allowed only in a failing \
        context, a program or a function marked `fails`"
    match d.ret with
    | some (.opt ..) =>
      err span s!"`{f}` returns an optional; call it with `?`, `else`, or \
        `if let`"
    | r => return r
  if let some row := env.interface.call? f then
    if row.acquires.isSome then
      err span s!"`{f}` yields a resource; bind it with `hold x = {f}(...)` \
       "
    match row.fails, fallible with
    | some k, false =>
      err span s!"`{f}` can fail (kind `{k}`): call it with `?` or `else` \
       "
    | none, true => err span s!"`{f}` cannot fail, so it takes no `?` or `else`"
    | _, _ => pure ()
    return ← interfaceFn env K span row args
  if (env.local? f).isSome || (env.const? f).isSome ||
      (env.config? f).isSome then
    err span s!"`{f}` is not a function"
  if (env.map? f).isSome then
    err span s!"`{f}` is a map; its operations are `{f}[k]`, \
      `{f}.insert(k, v)`, and `{f}.delete(k)`"
  unknownFunction env span f

end

/-- A predicate over the bound names is a boolean of the form section
17 allows. -/
def checkPred (env : Env) (bound : List Local) (p : Expr) : M Unit := do
  unless isPredicateForm p do
    err p.span "a predicate is a quantifier-free formula over integers: \
      literals, constants, the refined name, sibling fields or parameters, \
      arithmetic, comparisons, `&&`, `||`, `!`; no calls, no map or packet \
      access, no byte-order casts"
  -- the kind stays, so that a predicate may name the constants of an
  -- enumeration and the `verdict` alias
  let env' := { env.top with locals := bound, kind := env.kind }
  check env' { mayFail := false, ret := .fn "" none } p (.bool p.span)

/-- The kind a `try` on `f` raises. -/
def fallibleKind (env : Env) : Fallible → Kind
  | .acquire _ r .. =>
    match env.interface.resource? r with
    | some row => row.fails.getD .failed_call
    | none => .failed_call
  | f => f.kind?.getD .failed_call

/-- The type a fallible operation binds, and the checks
on its arguments. -/
def fallibleTy (env : Env) (K : Ctx) (f : Fallible) : M Bound := do
  match f with
  | .view s off t =>
    requirePkt env s
    check env K off tU64
    if let some why ← env.notRepresentable t false then
      err s s!"`{t.print}` is not packet-representable: it contains {why} \
       "
    let (sz, _) ← env.layout t
    viewOffsetDemand env K s off sz
    return { ty := some (.view s t), origin := .pkt }
  | .lookup s m k =>
    let (kt, vt) ← hashTypes env s m
    let ki ← placeTyUse env K k
    unless ← env.eqv ki.ty kt do
      err k.span s!"the key of `{m}` is a `{kt.print}`; `{k.print}` is a \
        `{ki.ty.print}`"
    return { ty := some (.ref s vt), origin := .map m }
  | .loadw s p =>
    match p with
    | .field _ q fname =>
      let info ← placeTyUse env K q
      match ← env.norm info.ty with
      | .struct _ fields =>
        match fields.find? (·.name == fname) with
        | some fd =>
          match fd.pred with
          | some pred => return { ty := some (.refined s fname fd.ty pred) }
          | none =>
            err s s!"`{p.print}` cannot fail: the field `{fname}` has no \
              `where` clause, so read it without the marker"
        | none => err s s!"`{q.print}` has no field `{fname}`"
      | _ => err s s!"`{q.print}` is a `{info.ty.print}`, which has no fields"
    | _ => err s "a marked load reads a field"
  | .call s fn args => return { ty := ← synthCall env K s fn args true }
  | .acquire s r fn tyArg args =>
    -- the acquisition's argument form is a column of its row
    let row ← match env.interface.resource? r with
      | some row => pure row
      | none =>
        if r == .iter then
          err s "iterator loops are not in this draft's resource table \
            (an open design point)"
        err s s!"`{r}` has no row in the resource table"
    match row.arg with
    | .place slot =>
      match args with
      | [.place p] =>
        let info ← placeTyUse env K p
        match ← env.norm info.ty with
        | .slot _ n =>
          unless n == slot do
            err p.span s!"`{fn}` takes a `{slot}` place; `{p.print}` is a \
              `{n}`"
        | _ =>
          err p.span s!"`{fn}` takes a `{slot}` place; `{p.print}` is a \
            `{info.ty.print}`"
        let homes := ((env.interface.slot? slot).map (·.homes)).getD []
        let homesText := ", ".intercalate (homes.map Home.describe)
        match info.origin with
        | .map _ =>
          unless homes.contains .mapValue do
            err p.span s!"a `{slot}` lives in {homesText}"
        | _ => err p.span s!"a `{slot}` lives in {homesText}"
        return { ty := none }
      | _ => err s s!"`{fn}(p)` takes one `{slot}` place"
    | .scope =>
      unless args.isEmpty do err s s!"`{fn}` takes no arguments"
      return { ty := none }
    | .call =>
      match env.interface.call? fn with
      | some crow =>
        match crow.sig with
        | .fn .. =>
          return { ty := ← interfaceFn env K s crow args, origin := .kernel }
        | .builtin =>
          -- `rb.reserve<T>()`, the one acquiring builtin, typed by rule
          unless fn == "reserve" do err s s!"`{fn}` has no typing rule"
          match args, tyArg with
          | [.map ms m], some t =>
            match env.map? m with
            | some d =>
              match d.kind with
              | .ringbuf _ =>
                if let some why ← env.notRepresentable t false then
                  err s s!"a ring-buffer record holds data; `{t.print}` \
                    contains {why}"
                let _ ← env.layout t
                return { ty := some (.own s t), origin := .kernel }
              | _ => err ms s!"`{m}` is not a ring buffer"
            | none => err ms s!"unknown map `{m}`"
          | _, _ =>
            err s "`rb.reserve<T>()` takes a ring buffer and a record type"
      | none => unknownFunction env s fn
  | .callopt s fn args =>
    match env.fn? fn with
    | some d =>
      unless args.length == d.params.length do
        err s s!"`{fn}` takes {d.params.length} arguments, {args.length} given"
      for (p, a) in d.params.zip args do
        checkArg env K fn p a
      if d.fails && !K.mayFail then
        err s s!"`{fn}` may fail; a call to it is allowed only in a failing \
          context, a program or a function marked `fails`"
      match d.ret with
      | some (.opt _ t) => return { ty := some t }
      | _ =>
        err s s!"`{fn}` does not return an optional, so it cannot fail here; \
          call it without `?` or `else`"
    | none =>
      if fn == "next" then
        err s "iterator loops are not in this draft's resource table \
          (an open design point)"
      err s s!"unknown function `{fn}`"
  | .coerce s e t =>
    match t with
    | .refined _ v base pred =>
      let bn ← env.norm base
      unless bn.isScalar do
        err s "a coercion refines a scalar"
      -- An enumeration is reached from an integer of its width: the
      -- coercion is where a number becomes a named value.
      match bn with
      | .enum _ n =>
        match env.interface.enum? n with
        | some row => check env K e (.int s false row.width)
        | none => err s s!"unknown enumeration `{n}`"
      | _ => check env K e base
      checkPred env
        [{ name := v, ty := base, mutable := false, origin := .stack }] pred
      return { ty := some t }
    | _ =>
      err s "the target of `as ...?` is a refinement type `{v: T | P}`, \
        or an enumeration"

end Koit.Check
