import Koit.Check.Stmt

/-!
Declarations, functions, contracts, and programs: the well-formedness
of types, constants, configuration, and maps; a function against its
signature; the call graph; a program's kind, contract, clauses,
handlers, and body. `checkUnit` is the entry point: it checks the
declarations in the order of a unit's template and stops at the first
error, whose span is the surface construct's; it yields the cap of
every `for` loop, by span, for the lowering.

Two demands live here: the predicate on an array map's value must
hold of the all-zero value, since such a map is zero-filled at
creation, and a function's parameter refinements are the facts its
body starts from.
-/

namespace Koit.Check

open Koit (Span)
open Koit.Core
open Koit.Interface (KindDecl tU32 tU64)
open Koit.Facts (Facts Fact Caps Scope)
open Koit.Effects (Effs)


/-- A context for declaration-level expressions: no failure, no loop,
no return. -/
def K0 : Ctx := { mayFail := false, ret := .fn "" none }

/-- A data type: what a `type` declaration, a map, a view,
and a struct field may have. -/
partial def checkDataTy (env : Env) (t : Ty) (fuel : Nat := 64) : M Unit := do
  if fuel == 0 then err t.span "type nesting too deep"
  match t with
  | .int .. | .be .. | .bool .. | .slot .. => pure ()
  -- A stored enumeration would be read without a test, and what the
  -- environment wrote is untrusted: store the integer and coerce.
  | .enum s n =>
    err s s!"`{n}` is an enumeration, which this draft holds in a local, a \
      parameter, or a result, and not in a map, a view, or a struct; store \
      the integer and read it back with `as {n}?`"
  | .named s n =>
    match env.type? n with
    | some _ =>
      let _ ← env.norm t
    | none => err s s!"unknown type `{n}`"
  | .struct s fields =>
    let mut seen : List String := []
    for f in fields do
      if seen.contains f.name then
        err f.span s!"field `{f.name}` is declared twice"
      seen := seen ++ [f.name]
      match f.ty with
      | .ref .. | .view .. | .own .. | .opt .. =>
        err f.span s!"field `{f.name}` may not have type `{f.ty.print}`: a \
          struct holds data, and places are never stored"
      | _ => checkDataTy env f.ty (fuel - 1)
      if let some p := f.pred then
        let tn ← env.norm f.ty
        unless tn.isScalar do
          err p.span s!"a `where` clause refines a scalar field; `{f.name}` is \
            a `{f.ty.print}`"
        let sibs : List Local := fields.map fun g =>
          { name := g.name, ty := g.ty, mutable := false, origin := .stack }
        checkPred env sibs p
    env.checkSlots s "the struct" t
  | .array _ elem n =>
    checkDataTy env elem (fuel - 1)
    checkCount env.top K0 "an array length" n
  | .refined s v base pred =>
    let bn ← env.norm base
    unless bn.isScalar do err s "a refinement type refines a scalar"
    checkPred env
      [{ name := v, ty := base, mutable := false, origin := .stack }] pred
  | .ref .. | .view .. | .own .. | .opt .. =>
    err t.span s!"`{t.print}` is not a data type: it names a place, and a \
      declaration names data"

def checkTypeDecl (env : Env) (d : TypeDecl) : M Unit := checkDataTy env d.ty

/-- The names a constant's value may use, followed
through the constants it names, so that a cycle is an error at the
declaration. `visiting` is the chain of constants being expanded. -/
partial def constNamesOk (env : Env) (visiting : List String) : Expr → M Unit
  | .lit .. | .char .. | .bool .. => pure ()
  | .var s n => do
    if visiting.contains n then
      err s s!"constant `{n}` is defined in terms of itself"
    if let some d := env.const? n then
      constNamesOk env (n :: visiting) d.value
    else if (env.config? n).isSome then pure ()
    else err s s!"unknown name `{n}` in a constant expression"
  | .arith _ _ l r | .cmp _ _ l r | .and _ l r | .or _ l r => do
    constNamesOk env visiting l
    constNamesOk env visiting r
  | .not _ e | .hton _ e => constNamesOk env visiting e
  | .cast s e t => do
    unless (← env.norm t).isIntTy do
      err s "`as` converts between integer types"
    constNamesOk env visiting e
  | .size _ t => do let _ ← env.layout t
  | e => err e.span "the value of a constant is a constant expression: \
      literals, constants, `size`, `hton`, and arithmetic"

def checkConst (env : Env) (d : ConstDecl) : M Unit := do
  match d.ty with
  | some t =>
    let tn ← env.norm t
    unless tn.isScalar do
      err t.span s!"a constant is a scalar; `{t.print}` is not one"
    unless env.isConstExpr d.value do
      err d.value.span "the value of a constant is a constant expression \
       "
    constNamesOk env [d.name] d.value
    check env.top K0 d.value t
  | none =>
    unless env.isConstExpr d.value do
      err d.value.span "the value of a constant is a constant expression \
       "
    constNamesOk env [d.name] d.value

def checkConfig (env : Env) (d : ConfigDecl) : M Unit := do
  match ← env.norm d.ty with
  | .int .. | .bool _ => pure ()
  | _ =>
    err d.ty.span s!"a configuration constant is an integer or a `bool`; \
      `{d.ty.print}` is neither"
  match d.init with
  | some i =>
    unless env.isConstExpr i do
      err i.span "the default of a configuration constant is a constant \
        expression"
    check env.top K0 i d.ty
  | none =>
    -- the facts use the build's value, and no build supplies one yet
    err d.span s!"`{d.name}` has no value for this build: give it a default \
      "

/-- Every field predicate in a data type must hold of the all-zero
value: the value of an array map starts as zeros. -/
partial def checkZeroValue (env : Env) (mapName : String) (t : Ty)
    (fuel : Nat := 64) : M Unit := do
  if fuel == 0 then return ()
  match ← env.norm t with
  | .struct _ fields =>
    for f in fields do
      if let some pred := f.pred then
        let zero : Expr := .lit pred.span 0 "0"
        let P := fields.foldl (fun P g => P.subst g.name zero) pred
        unless Koit.Facts.entails (scope env.top K0) {} P do
          err pred.span s!"the predicate `{pred.printPred}` on the value of \
            `{mapName}` must hold of the all-zero value: an array map is \
            zero-filled at creation"
      checkZeroValue env mapName f.ty (fuel - 1)
  | .array _ elem _ => checkZeroValue env mapName elem (fuel - 1)
  | _ => pure ()

/-- A map's capacity and its key and value types. -/
def checkMap (env : Env) (d : MapDecl) : M Unit := do
  let capacity (n : Expr) : M Unit :=
    checkCount env.top K0 "a map capacity" n
  let value (v : Ty) : M Unit := do
    env.checkSlots v.span s!"the value type of map `{d.name}`" v
      (some .mapValue)
    checkDataTy env v
    if let some why ← env.notRepresentable v true then
      err v.span s!"the value type of map `{d.name}` may not contain {why}: \
        map keys and values are packet-representable, and a value may hold \
        slot types per their declarations"
    let _ ← env.layout v
  -- the access word applies to maps the program reads or writes as
  -- values; a ring buffer is neither, and a socket map holds sockets
  if d.access != .rw then
    if let .ringbuf _ := d.kind then
      err d.span s!"`{d.name}` is a ring buffer, which has no access word"
    if d.kind.isSocket then
      err d.span s!"`{d.name}` holds sockets, not places, and has no access word"
  -- the initializer: one constant of the value type per entry of an
  -- array map, scalars in this draft
  unless d.init.isEmpty do
    match d.kind with
    | .progArray .. => pure ()
    | .array n v =>
      let vn ← env.norm v
      unless vn.isScalar do
        err d.span s!"the initializer of `{d.name}` needs a scalar value \
          type in this draft; `{v.print}` is an aggregate"
      match env.evalConst n with
      | some cnt =>
        unless d.init.length == cnt do
          err d.span s!"`{d.name}` has {cnt} entries and {d.init.length} \
            initializers"
      | none => pure ()
      for e in d.init do
        unless env.isConstExpr e do
          err e.span s!"the initializer of `{d.name}` takes constant \
            expressions; `{e.print}` is not one"
        check env.top K0 e vn
    | _ => err d.span s!"only an `array[n]` map takes an initializer"
  match d.kind with
  | .progArray n k =>
    capacity n
    -- the kind, and the entries as programs of it, at most one per slot
    unless (env.interface.kind? k).isSome do
      err d.span s!"`{d.name}` holds programs of an unknown kind `{k}`"
    match env.evalConst n with
    | some cnt =>
      if d.init.length > cnt then
        err d.span s!"`{d.name}` has {cnt} slots and {d.init.length} entries"
    | none => pure ()
    for e in d.init do
      match e with
      | .var s p =>
        match env.programs.find? (·.1 == p) with
        | some (_, pk, _) =>
          unless pk == k do
            err s s!"`{p}` is {article pk} `{pk}` program; `{d.name}` holds `{k}` \
              programs"
        | none => err s s!"`{p}` is not a program of this unit"
      | _ => err e.span s!"an entry of `{d.name}` names a program"
  | .array n v | .percpu n v =>
    capacity n
    value v
    checkZeroValue env d.name v
  | .hash n k v =>
    capacity n
    checkDataTy env k
    if let some why ← env.notRepresentable k false then
      err k.span s!"the key type of map `{d.name}` may not contain {why}: map \
        keys and values are packet-representable"
    let _ ← env.layout k
    value v
  | .ringbuf n => capacity n
  | .sockmap n => capacity n
  | .sockhash n k =>
    capacity n
    checkDataTy env k
    if let some why ← env.notRepresentable k false then
      err k.span s!"the key type of map `{d.name}` may not contain {why}: map \
        keys and values are packet-representable"
    let _ ← env.layout k

/-- A function against its signature: the caps of its loops. -/
def checkFn (env : Env) (f : Fn) : M (Caps × Effs) := do
  let mut locals : List Local := []
  let mut seen : List String := []
  for p in f.params do
    if seen.contains p.name then
      err p.span s!"parameter `{p.name}` is declared twice"
    seen := seen ++ [p.name]
    match p.ty with
    | .own .. =>
      err p.span s!"parameter `{p.name}` of `{f.name}`: user functions take \
        `ref` and `view` parameters and never `own`"
    | .opt .. => err p.span "an optional is not a parameter type"
    | .ref _ t =>
      checkDataTy env t
      locals := { name := p.name, ty := p.ty, mutable := false,
                  origin := .param } :: locals
    | .view _ t =>
      checkDataTy env t
      if let some why ← env.notRepresentable t false then
        err p.span s!"`{t.print}` is not packet-representable: it contains \
          {why}"
      locals := { name := p.name, ty := p.ty, mutable := false,
                  origin := .pkt } :: locals
    | t =>
      checkDataTy env t
      let tn ← env.norm t
      unless tn.isScalar do
        err p.span s!"aggregates are passed by reference: declare \
          `{p.name}: ref {t.print}`"
      let ty := match p.pred with
        | some q => Ty.refined p.span p.name t q
        | none => t
      locals := { name := p.name, ty, mutable := false, origin := .stack }
        :: locals
  let scalars := locals.reverse.filter fun l => !l.ty.isPlaceTy
  for p in f.params do
    if let some q := p.pred then
      checkPred env scalars q
  -- a global function: nothing crosses the call but types, and its
  -- prototype is what the kernel's can say
  if f.global then
    for p in f.params do
      if p.pred.isSome then
        err p.span s!"`{f.name}` is global, so the verifier will not know \
          `{p.name}`'s refinement across the call; drop it and test what the \
          body needs with `check` or `if`"
      if let .view .. := p.ty then
        err p.span s!"`{f.name}` is global, and the verifier has no packet \
          parameter: `{p.name}` cannot be a view"
    match f.ret with
    | some (.refined s ..) =>
      err s s!"`{f.name}` is global, so the verifier will not know its \
        result's refinement across the call; drop it"
    | some (.opt s ..) =>
      err s s!"`{f.name}` is global, and the kernel's convention returns one \
        scalar; an optional result waits for a convention of its own"
    | some t =>
      match ← env.norm t with
      | .enum .. =>
        err t.span s!"`{f.name}` is global, and the verifier sees its result \
          as an unknown scalar, not a `{t.print}`; return the scalar and let \
          the caller coerce"
      | _ => pure ()
    | none => pure ()
    if f.fails then
      err f.span s!"`{f.name}` is global, and a failure has no handler to \
        reach across a subprogram boundary; it cannot `fails`"
  -- the result: a scalar, an optional scalar, or a refined scalar
  let resultScalar (t : Ty) : M Unit := do
    match t with
    | .ref .. | .view .. | .own .. =>
      err t.span s!"the result type of `{f.name}` must be a scalar: places \
        are never returned"
    | _ => pure ()
    checkDataTy env t
    unless (← env.norm t).isScalar do
      err t.span s!"the result type of `{f.name}` must be a scalar: \
        aggregates are places (P3)"
  match f.ret with
  | some (.opt _ t) => resultScalar t
  | some (.refined s r base pred) =>
    resultScalar base
    checkPred env (scalars ++ [{ name := r, ty := base, mutable := false,
                                  origin := .stack }]) pred
    let _ := s
  | some t => resultScalar t
  | none => pure ()
  -- the body starts from the parameters' refinements
  let fenv := { env.top with locals }
  let F0 : Facts := (refinementFacts fenv).foldl Facts.add {}
  let K : Ctx := { mayFail := f.fails, ret := .fn f.name f.ret,
                   fnName := some f.name, facts := F0 }
  let (F, E) ← checkStmts fenv K f.body
  if f.ret.isSome && !exits f.body then
    err f.span s!"`{f.name}` has a result type, so its body must end in \
      `return` or an expression"
  return (F.caps, E)

/-! ### The call graph -/

mutual

partial def calleesExpr : Expr → List String
  | .call _ f args => f :: calleesArgs args
  | .arith _ _ l r | .cmp _ _ l r | .and _ l r | .or _ l r =>
    calleesExpr l ++ calleesExpr r
  | .not _ e | .cast _ e _ | .hton _ e | .ntoh _ e => calleesExpr e
  | .read _ p => calleesPlace p
  | _ => []

partial def calleesPlace : Place → List String
  | .field _ p _ => calleesPlace p
  | .index _ p i => calleesPlace p ++ calleesExpr i
  | .slot _ _ i => calleesExpr i
  | .deref _ e => calleesExpr e
  | _ => []

partial def calleesArgs (args : List Arg) : List String :=
  args.flatMap fun
    | .val e => calleesExpr e
    | .place p => calleesPlace p
    | .map .. => []

partial def calleesFallible : Fallible → List String
  | .view _ off _ => calleesExpr off
  | .lookup _ _ k => calleesPlace k
  | .loadw _ p => calleesPlace p
  | .call _ f args | .callopt _ f args => f :: calleesArgs args
  | .acquire _ _ f _ args => f :: calleesArgs args
  | .coerce _ e _ => calleesExpr e
  | .tail _ _ i => calleesExpr i

partial def calleesStmts (ss : List Stmt) : List String :=
  ss.flatMap fun
    | .«let» _ _ _ _ (.expr e) => calleesExpr e
    | .«let» _ _ _ _ (.place p) => calleesPlace p
    | .«let» _ _ _ _ (.lit _ fs) => fs.flatMap fun f => calleesExpr f.value
    | .assign _ p e => calleesPlace p ++ calleesExpr e
    | .ite _ c t e => calleesExpr c ++ calleesStmts t ++ calleesStmts e
    | .loop _ n b => calleesExpr n ++ calleesStmts b
    | .«for» _ _ lo hi b => calleesExpr lo ++ calleesExpr hi ++ calleesStmts b
    | .ret _ (some e) => calleesExpr e
    | .raise _ _ e => calleesExpr e
    | .«try» _ _ f t e _ =>
      calleesFallible f ++ calleesStmts t ++ calleesStmts e
    | .hold _ _ _ acq b e =>
      calleesFallible acq ++ calleesStmts b ++ (e.map calleesStmts).getD []
    | .atomic _ _ _ p args => calleesPlace p ++ args.flatMap calleesExpr
    | _ => []

end

/-- A depth-first search along the unit's calls: an error at the
function that closes a cycle. -/
partial def visitCalls (fns : List Fn) (edges : List (String × List String))
    (path : List String) (g : String) : M Unit := do
  if path.contains g then
    let f := path.getLast!
    let d := (fns.find? (·.name == f)).get!
    err d.span s!"`{f}` calls itself, through \
      {" -> ".intercalate (path ++ [g])}; the call graph must be acyclic \
     "
  for h in (edges.lookup g).getD [] do
    visitCalls fns edges (path ++ [g]) h

/-- The unit's calls between its own functions. -/
def callEdges (env : Env) (fns : List Fn) : List (String × List String) :=
  fns.map fun f =>
    (f.name, (calleesStmts f.body).filter fun g => (env.fn? g).isSome)

/-- The call graph must be acyclic. -/
def checkCallGraph (env : Env) (fns : List Fn) : M Unit := do
  let edges := callEdges env fns
  for f in fns do
    visitCalls fns edges [] f.name

/-- The functions with every callee before its callers, so that a
function's effect summary is known at each call to it; the call graph
is acyclic by the time this runs, and any remainder is kept in
declaration order. -/
def calleesFirst (env : Env) (fns : List Fn) : List Fn :=
  let edges := callEdges env fns
  let rec go (done pending : List Fn) : Nat → List Fn
    | 0 => done ++ pending
    | fuel + 1 =>
      let ready := pending.filter fun f =>
        ((edges.lookup f.name).getD []).all fun g =>
          g == f.name || done.any (·.name == g)
      if ready.isEmpty then done ++ pending
      else go (done ++ ready)
        (pending.filter fun f => !ready.any (·.name == f.name)) fuel
  go [] fns fns.length

/-- The verdict names and regions of a contract or a program header. -/
def checkClauses (env : Env) (decl : KindDecl)
    (verdicts : Option (List (Span × String))) (preserved : List Region) :
    M Unit := do
  if let some vs := verdicts then
    for (s, n) in vs do
      unless decl.verdicts.any (·.1 == n) do
        err s s!"`{n}` is not a verdict of {article decl.name} `{decl.name}` \
          program"
  for r in preserved do
    match r with
    | .pkt s range =>
      unless decl.hasPkt do
        err s s!"{article decl.name} `{decl.name}` program has no packet \
         "
      if let some (lo, hi) := range then
        for e in [lo, hi] do
          unless env.isConstExpr e do
            err e.span "the bounds of `pkt[a .. b)` are constant expressions \
             "
          check env.top K0 e tU64
    | .map s m =>
      unless (env.map? m).isSome do err s s!"unknown map `{m}` in `preserve`"
    | .mapsExcept s names =>
      for m in names do
        unless (env.map? m).isSome do
          err s s!"unknown map `{m}` in `preserve maps except`"
    | .ctx s f =>
      unless decl.ctx.any (·.name == f) do
        err s s!"the context of {article decl.name} `{decl.name}` program has no \
          field `{f}`"

def kindDecl (env : Env) (span : Span) (kind : String) : M KindDecl := do
  match env.interface.kind? kind with
  | some decl => return decl
  | none =>
    err span s!"unknown program kind `{kind}`; the kinds are \
      {", ".intercalate (env.interface.kinds.map (·.name))}"

/-- The failure kinds a body can raise: those its `raise` statements
carry, and those of every function it calls, through the acyclic call
graph. A marker and an `else` desugar to a `raise`, so the walk sees
every site. -/
partial def raisableIn (env : Env) (seen : List String) :
    List Stmt → List Kind
  | [] => []
  | s :: rest =>
    let here : List Kind := match s with
      | .raise _ k _ => [k]
      | .ite _ _ t e => raisableIn env seen t ++ raisableIn env seen e
      | .loop _ _ b | .«for» _ _ _ _ b => raisableIn env seen b
      | .«try» _ _ _ t e _ => raisableIn env seen t ++ raisableIn env seen e
      | .hold _ _ _ _ b e =>
        raisableIn env seen b ++ raisableIn env seen (e.getD [])
      | _ => []
    -- a call to a `fails` function raises what that function raises
    let called : List Kind :=
      (calleesStmts [s]).flatMap fun f =>
        if seen.contains f then []
        else match env.fns.find? (·.name == f) with
          | some d => raisableIn env (f :: seen) d.body
          | none => []
    here ++ called ++ raisableIn env seen rest

/-- (Handler-live): a handler names a kind the program can raise. The
total table the desugaring builds fills every kind from the program's
default, so a handler nobody can reach is dead code and a false
statement about the program; `default` is exempt, since it is also
what 14.1 checks the program's verdict set against. -/
def checkNamedHandlers (env : Env) (p : Program) : M Unit := do
  let raisable := raisableIn env [] p.body
  for (span, k) in p.named do
    unless raisable.contains k do
      err span s!"nothing in `{p.name}` raises `{k}`, so this handler \
        cannot run; remove it, or mark the operation that should raise it"

def checkContract (env : Env) (c : Contract) : M Unit := do
  let decl ← kindDecl env c.span c.kind
  checkClauses env decl c.verdicts c.preserved

/-- (Program) and (Handler): the kind, the contract, the clauses,
every handler exiting in a non-failing context, and the body, each
`return` demanded to lie in the verdict set and every statement's
effects checked against the preserved regions. Yields the caps of
the loops and the program's effects. -/
def checkProgram (env : Env) (p : Program) : M (Caps × Effs) := do
  let decl ← kindDecl env p.span p.kind
  checkNamedHandlers env p
  if let some (s, c) := p.implements then
    match env.contracts.find? (·.name == c) with
    | some k =>
      unless k.kind == p.kind do
        err s s!"contract `{c}` is for `{k.kind}` programs; `{p.name}` is \
          {article p.kind} `{p.kind}` program"
    | none => err s s!"unknown contract `{c}`"
  checkClauses env decl p.verdicts p.preserved
  let env := { env with kind := some decl }
  let vset := p.verdicts.map (·.map (·.2))
  let mut caps : Caps := []
  let mut E : Effs := {}
  for h in p.handlers do
    let hEnv := env.bind { name := "reason", ty := tU32, mutable := false,
                           origin := .stack }
    let K : Ctx := { mayFail := false, ret := .handler decl.verdictTy,
                     inHandler := true, verdictSet := vset,
                     preserved := p.preserved }
    let (F, Eh) ← checkStmts hEnv K h.body
    caps := caps ++ F.caps
    E := E.union Eh
    unless exits h.body do
      err h.span s!"the handler for `{h.kind}` must end in an exit \
       "
  let K : Ctx := { mayFail := true, ret := .program decl.verdictTy,
                   verdictSet := vset, preserved := p.preserved }
  let (F, Eb) ← checkStmts env K p.body
  -- a body that falls off its end returns 0, which only a kind with a
  -- bare integer result admits: a named verdict must be returned
  if !decl.verdicts.isEmpty && !exits p.body then
    err p.span s!"the body of {article decl.name} `{decl.name}` program must end \
      in an exit"
  let all := E.union Eb
  -- the packet of a kind whose `pkt` clause is `ro` is never written,
  -- through a function's view parameter or a builtin either
  if decl.hasPkt && !decl.pktWritable then
    if all.effs.any (fun e => match e with
        | .pkt .. | .pktAll | .resize => true
        | _ => false) then
      err p.span s!"`{p.name}` writes the packet, and the packet of \
        {article decl.name} `{decl.name}` program may only be read"
  return (caps ++ F.caps, all)

/-- Unit-level names: types in one namespace, values in another,
programs and contracts in a third. -/
def checkNames (u : CompUnit) : M Unit := do
  let dup (what : String) (names : List (Span × String)) : M Unit := do
    let mut seen : List String := []
    for (s, n) in names do
      if seen.contains n then err s s!"{what} `{n}` is declared twice"
      seen := seen ++ [n]
  dup "type" (u.types.map fun d => (d.span, d.name))
  dup "name" (u.consts.map (fun d => (d.span, d.name)) ++
    u.configs.map (fun d => (d.span, d.name)) ++
    u.maps.map (fun d => (d.span, d.name)) ++
    u.fns.map fun d => (d.span, d.name))
  dup "program or contract" (u.contracts.map (fun c => (c.span, c.name)) ++
    u.programs.map fun p => (p.span, p.name))

/-- What checking a unit yields for the later stages: the cap of
every loop, and the effect set of every function, stated over its
parameters, and of every program. -/
structure Checked where
  caps     : Caps := []
  fns      : List (String × Effs) := []
  programs : List (String × Effs) := []
  deriving Inhabited

/-- The checker's entry point: every declaration of the unit, in the
order of a unit's template, with functions after the call graph is
known to be acyclic and callees before callers. With `smt`, each
accepted entailment is traced as a solver query. -/
def checkUnit (pre : Interface) (u : CompUnit) (smt : Bool := false) :
    M Checked := do
  checkNames u
  let env : Env := { interface := pre, license := u.license.map (·.2),
                     types := u.types, consts := u.consts,
                     configs := u.configs, maps := u.maps, fns := u.fns,
                     contracts := u.contracts, smt }
  for d in u.types do checkTypeDecl env d
  for d in u.consts do checkConst env d
  for d in u.configs do checkConfig env d
  -- the programs' verdict sets, for the tail calls and the program
  -- arrays that name them: a program's own clause, or its contract's
  let env := { env with programs := u.programs.map fun p =>
    let own := p.verdicts.map (·.map (·.2))
    let fromContract := p.implements.bind fun (_, c) =>
      (u.contracts.find? (·.name == c)).bind fun k => k.verdicts.map (·.map (·.2))
    (p.name, p.kind, own <|> fromContract) }
  for d in u.maps do checkMap env d
  checkCallGraph env u.fns
  let mut env := env
  let mut out : Checked := {}
  for f in calleesFirst env u.fns do
    let (caps, E) ← checkFn env f
    env := { env with fnEffects := env.fnEffects ++ [(f.name, E)] }
    out := { out with caps := out.caps ++ caps, fns := out.fns ++ [(f.name, E)] }
  for c in u.contracts do checkContract env c
  for p in u.programs do
    let (caps, E) ← checkProgram env p
    out := { out with caps := out.caps ++ caps,
                      programs := out.programs ++ [(p.name, E)] }
  return out

end Koit.Check
