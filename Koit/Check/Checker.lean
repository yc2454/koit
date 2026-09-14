import Koit.Check.Typing

/-!
The checker: statements, declarations, functions, contracts, and
programs, the base half of spec/language.md section 18.4 and the shape
rules of sections 7 to 10, 13, 14, 16, and 17. No facts, held sets,
or effects yet; those premises are sessions 3 and 4, and the
comments name each rule they will complete.

`checkUnit` is the entry point: it checks the declarations in the
order of section 23.1 and stops at the first error, whose span is the
surface construct's.
-/

namespace Koit.Check

open Koit (Span)
open Koit.Core

/-- Whether a block ends in an exit (sections 10.3, 10.6, 13): its
last statement exits on every path through it. -/
partial def exits : List Stmt → Bool
  | [] => false
  | ss =>
    match ss.getLast! with
    | .ret .. | .raise .. | .brk .. | .cont .. => true
    | .ite _ _ t e => exits t && exits e
    | .«try» _ _ _ t e _ => exits t && exits e
    | .hold _ _ _ _ body els => exits body && (els.map exits).getD true
    | _ => false

def exitForms : String := "a verdict, `fail`, `return`, `break`, or `continue`"

/-- The struct type a literal has (section 8.2; spec/ISSUES.md 11 k):
the binding's declared type, or the one declared type with exactly
its field names in its order. -/
def structForLiteral (env : Env) (span : Span) (declared : Option Ty)
    (fields : List FieldInit) : M Ty := do
  let names := fields.map (·.name)
  match declared with
  | some t =>
    match ← env.norm t with
    | .struct .. => return t
    | _ =>
      err span s!"a struct literal has a struct type; `{t.print}` is not one \
        (section 8.2)"
  | none =>
    let mut found : List TypeDecl := []
    for d in env.types ++ env.prelude.types do
      match ← env.norm d.ty with
      | .struct _ fs =>
        if fs.map (·.name) == names then found := found ++ [d]
      | _ => pure ()
    match found with
    | [d] => return .named span d.name
    | [] =>
      err span s!"no declared struct type has the fields \
        `{", ".intercalate names}`; annotate the binding with the type \
        (section 8.2)"
    | ds =>
      err span s!"the fields `{", ".intercalate names}` belong to several \
        declared types ({", ".intercalate (ds.map (·.name))}); annotate the \
        binding with the type (section 8.2)"

/-- A binding: the local it introduces (sections 8.2, 9, 18.4). -/
def bindInit (env : Env) (K : Ctx) (span : Span) (mutable : Bool) (x : String)
    (ty : Option Ty) (init : Init) : M Local := do
  match init with
  | .expr e =>
    let t ← match ty with
      | some t =>
        check env K e t
        pure t
      | none => synth env K e
    let tn ← env.norm t
    unless tn.isScalar do
      err span s!"`{x}` would be a `{t.print}`; a binding whose right side is \
        not a place takes a scalar (P3)"
    return { name := x, ty := t, mutable, origin := .stack }
  | .place p =>
    let info ← placeTy env K p
    let tn ← env.norm info.ty
    -- (Read): a scalar place is read into the name, at its base type
    if tn.isScalar then
      match ty with
      | some t =>
        unless ← env.eqv t tn do mismatch env p.span t info.ty
        return { name := x, ty := t, mutable, origin := .stack }
      | none => return { name := x, ty := tn, mutable, origin := .stack }
    match tn with
    | .spinlock _ =>
      err span "a `spinlock` is not bound; it is held with `hold lock(p)` \
        (section 11)"
    | _ => pure ()
    -- (P3): an aggregate place is named
    if mutable then
      err span "`var` binds a scalar; an aggregate place is named with `let` \
        (section 8.2)"
    if let some t := ty then
      unless ← env.eqv t info.ty do mismatch env p.span t info.ty
    let pty := if info.origin == .pkt then Ty.view span info.ty
      else Ty.ref span info.ty
    return { name := x, ty := pty, mutable := false, origin := info.origin }
  | .lit ls fields =>
    if mutable then
      err span "`var` binds a scalar; a struct literal is a place, named with \
        `let` (section 8.2)"
    let st ← structForLiteral env ls ty fields
    let fs ← match ← env.norm st with
      | .struct _ fs => pure fs
      | _ => err ls "a struct literal has a struct type (section 8.2)"
    unless fs.map (·.name) == fields.map (·.name) do
      err ls s!"a struct literal gives every field of `{st.print}` in order: \
        {", ".intercalate (fs.map (·.name))} (section 8.2)"
    for (fd, fi) in fs.zip fields do
      let ftn ← env.norm fd.ty
      unless ftn.isScalar do
        err fi.span s!"field `{fd.name}` of `{st.print}` is a `{fd.ty.print}`; \
          struct literals have scalar fields only (section 8.2)"
      -- the predicate of the field is a demand of session 3
      check env K fi.value fd.ty
    return { name := x, ty := .ref span st, mutable := false, origin := .stack }

/-- `return` against what the context returns to (sections 13, 16). -/
def checkRet (env : Env) (K : Ctx) (span : Span) (v : Option Expr) :
    M Unit := do
  match K.ret, v with
  | .program ty, some e | .handler ty, some e =>
    check env K e ty
    -- a verdict constant against the verdict set (section 14.1); a
    -- computed verdict is a demand of session 4
    match e, K.verdictSet with
    | .var vs n, some vset =>
      if (env.verdict? n).isSome && !vset.contains n then
        err vs s!"`{n}` is not in the verdict set (section 14.1)"
    | _, _ => pure ()
  | .program _, none | .handler _, none =>
    err span "a program returns a verdict (section 13)"
  | .fn _ none, none => pure ()
  | .fn f none, some _ => err span s!"`{f}` returns nothing"
  | .fn _ (some (.opt _ t)), none =>
    err span s!"a bare `return` in a function returning `{t.print}?` is not \
      decided (spec/ISSUES.md, entry 9)"
  | .fn _ (some (.opt _ t)), some e => check env K e t
  | .fn f (some t), none =>
    err span s!"`return` needs a value: `{f}` returns `{t.print}`"
  | .fn _ (some t), some e => check env K e t

/-- The acquiring function of a `hold`, for messages. -/
def acqName : Fallible → String
  | .acquire _ _ f .. => f
  | f => f.print

partial def checkStmts (env : Env) (K : Ctx) : List Stmt → M Unit
  | [] => pure ()
  | s :: rest => do
    match s with
    | .«let» span mutable x ty init =>
      if x == "_" then
        -- section 9: a bare expression statement is a call
        match init with
        | .expr (.call s' f args) =>
          let _ ← synthCall env K s' f args false
        | .expr (.invalid s' m) => err s' m
        | _ => err span "a bare expression statement must be a call (section 9)"
        checkStmts env K rest
      else
        let l ← bindInit env K span mutable x ty init
        checkStmts (env.bind l) K rest
    | .assign span p e =>
      -- (Assign); the store demand of (AssignW) is session 3
      let info ← placeTy env K p
      unless info.mutable do
        match p, info.origin with
        | .field _ _ f, .ctx =>
          err span s!"the context field `{f}` is not writable in \
            {article (env.kind.map (·.name)).get!} \
            `{(env.kind.map (·.name)).get!}` program (section 13)"
        | _, _ =>
          err span s!"`{p.print}` is immutable; declare it with `var` to \
            assign to it (section 9)"
      let tn ← env.norm info.ty
      match tn with
      | .spinlock _ => err span "a `spinlock` is not assigned (section 11)"
      | _ => pure ()
      unless tn.isScalar do
        err span s!"`{p.print}` is an aggregate of type `{info.ty.print}`; \
          assign its fields, or use `copy` (P3)"
      check env K e tn
      checkStmts env K rest
    | .ite _ c t e =>
      -- (IfConst): a constant condition is folded after both branches
      -- are checked (section 15)
      check env K c (.bool c.span)
      checkStmts env K t
      checkStmts env K e
      checkStmts env K rest
    | .loop _ n body =>
      -- (Repeat)
      checkCount env K "the count of `repeat`" n
      checkStmts env { K with inLoop := true } body
      checkStmts env K rest
    | .«for» span x lo hi body =>
      -- (For): the cap, the type of the bound under the facts, is
      -- session 3
      check env K lo tU64
      check env K hi tU64
      let l : Local := { name := x, ty := .int span false 64, mutable := false,
                         origin := .stack }
      checkStmts (env.bind l) { K with inLoop := true } body
      checkStmts env K rest
    | .brk span =>
      unless K.inLoop do err span "`break` outside a loop (section 9)"
      checkStmts env K rest
    | .cont span =>
      unless K.inLoop do err span "`continue` outside a loop (section 9)"
      checkStmts env K rest
    | .ret span v =>
      checkRet env K span v
      checkStmts env K rest
    | .raise span _ r =>
      -- (Mark), (Fail): the context may fail
      unless K.mayFail do
        if K.inHandler then
          err span "a handler is a non-failing context: no marker and no \
            `fail` may appear in it (section 10.6)"
        err span s!"`{K.fnName.getD "?"}` is not marked `fails`, so it may not \
          contain a marker, `check`, or `fail` (section 10.8)"
      check env K r tU32
      checkStmts env K rest
    | .«try» span x f thn els elseExits =>
      let b ← fallibleTy env K f
      let env' ← match x, b.ty with
        | "_", _ => pure env
        | _, some t =>
          pure (env.bind { name := x, ty := t, mutable := false,
                           origin := b.origin })
        | _, none =>
          err span s!"`{x}` binds nothing: the operation yields no value; \
            write `_`"
      checkStmts env' K thn
      checkStmts env { K with errnoOk := fallibleKind env f == .helper } els
      if elseExits && !exits els then
        err span s!"the `else` block must end in an exit: {exitForms} \
          (section 10.3)"
      checkStmts env K rest
    | .hold span r x acq body els =>
      -- (Hold); the held set, forbidden effects, nesting, and `move`
      -- consistency are session 4
      let b ← fallibleTy env K acq
      let row ← match env.prelude.resource? r with
        | some row => pure row
        | none => err span s!"`{r}` has no row in the resource table"
      match row.fails, els with
      | some k, none =>
        err span s!"`{acqName acq}` can fail (kind `{k}`); the acquisition \
          needs `?` or `else` (section 11.1)"
      | none, some _ =>
        err span s!"`{acqName acq}` cannot fail, so it takes no `?` or `else`"
      | _, _ => pure ()
      let env' ← match x, b.ty with
        | some n, some t =>
          pure (env.bind { name := n, ty := t, mutable := false,
                           origin := .kernel })
        | none, none => pure env
        | some _, none =>
          err span s!"`{acqName acq}` binds nothing: it is a scope-only \
            resource, `hold {acqName acq} \{ ... }` (section 11.1)"
        | none, some _ =>
          err span s!"`{acqName acq}` yields a value; bind it with \
            `hold x = ...` (section 11.1)"
      checkStmts env' K body
      if let some e := els then
        checkStmts env { K with errnoOk := row.fails == some .helper } e
        unless exits e do
          err span s!"the `else` block must end in an exit: {exitForms} \
            (section 10.3)"
      checkStmts env K rest
    | .atomic span x op p args =>
      let info ← placeTy env K p
      unless info.mutable do err span s!"`{p.print}` is immutable"
      let tn ← env.norm info.ty
      unless tn.isIntTy do
        err span s!"atomic updates apply to an integer place; `{p.print}` is a \
          `{info.ty.print}` (section 8.5)"
      match info.origin with
      | .stack | .map _ => pure ()
      | _ =>
        err span "atomic updates apply to a place in a map value or on the \
          stack (section 8.5)"
      let n := if op == .cmpxchg then 2 else 1
      unless args.length == n do
        err span s!"`{op.spelling}` takes a place and {n} value(s) \
          (section 8.5)"
      for a in args do
        check env K a tn
      let env' := match x with
        | some n => env.bind { name := n, ty := tn, mutable := false,
                               origin := .stack }
        | none => env
      checkStmts env' K rest
    | .invalid span m => err span m

/-! ### Declarations -/

/-- A context for declaration-level expressions: no failure, no loop,
no return. -/
def K0 : Ctx := { mayFail := false, ret := .fn "" none }

/-- A data type (section 7): what a `type` declaration, a map, a view,
and a struct field may have. -/
partial def checkDataTy (env : Env) (t : Ty) (fuel : Nat := 64) : M Unit := do
  if fuel == 0 then err t.span "type nesting too deep"
  match t with
  | .int .. | .be .. | .bool .. | .spinlock .. => pure ()
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
          struct holds data, and places are never stored (section 7)"
      | _ => checkDataTy env f.ty (fuel - 1)
      if let some p := f.pred then
        let tn ← env.norm f.ty
        unless tn.isScalar do
          err p.span s!"a `where` clause refines a scalar field; `{f.name}` is \
            a `{f.ty.print}` (section 17)"
        let sibs : List Local := fields.map fun g =>
          { name := g.name, ty := g.ty, mutable := false, origin := .stack }
        checkPred env sibs p
    if (← env.spinlocks t) > 1 then
      err s "at most one field of type `spinlock` (section 7)"
  | .array _ elem n =>
    checkDataTy env elem (fuel - 1)
    checkCount env.top K0 "an array length" n
  | .refined s v base pred =>
    let bn ← env.norm base
    unless bn.isScalar do err s "a refinement type refines a scalar (section 7)"
    checkPred env
      [{ name := v, ty := base, mutable := false, origin := .stack }] pred
  | .ref .. | .view .. | .own .. | .opt .. =>
    err t.span s!"`{t.print}` is not a data type: it names a place, and a \
      declaration names data (section 7)"

def checkTypeDecl (env : Env) (d : TypeDecl) : M Unit := checkDataTy env d.ty

/-- The names a constant's value may use (sections 6, 8.4), followed
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
    else err s s!"unknown name `{n}` in a constant expression (section 8.4)"
  | .arith _ _ l r | .cmp _ _ l r | .and _ l r | .or _ l r => do
    constNamesOk env visiting l
    constNamesOk env visiting r
  | .not _ e | .hton _ e => constNamesOk env visiting e
  | .cast s e t => do
    unless (← env.norm t).isIntTy do
      err s "`as` converts between integer types (section 8.1)"
    constNamesOk env visiting e
  | .size _ t => do let _ ← env.layout t
  | e => err e.span "the value of a constant is a constant expression: \
      literals, constants, `size`, `hton`, and arithmetic (section 8.4)"

def checkConst (env : Env) (d : ConstDecl) : M Unit := do
  match d.ty with
  | some t =>
    let tn ← env.norm t
    unless tn.isScalar do
      err t.span s!"a constant is a scalar; `{t.print}` is not one (section 6)"
    unless env.isConstExpr d.value do
      err d.value.span "the value of a constant is a constant expression \
        (section 8.4)"
    constNamesOk env [d.name] d.value
    check env.top K0 d.value t
  | none =>
    unless env.isConstExpr d.value do
      err d.value.span "the value of a constant is a constant expression \
        (section 8.4)"
    constNamesOk env [d.name] d.value

def checkConfig (env : Env) (d : ConfigDecl) : M Unit := do
  match ← env.norm d.ty with
  | .int .. | .bool _ => pure ()
  | _ =>
    err d.ty.span s!"a configuration constant is an integer or a `bool`; \
      `{d.ty.print}` is neither (section 15)"
  if let some i := d.init then
    unless env.isConstExpr i do
      err i.span "the default of a configuration constant is a constant \
        expression (section 15)"
    check env.top K0 i d.ty

/-- A map's capacity and its key and value types (section 7). -/
def checkMap (env : Env) (d : MapDecl) : M Unit := do
  let capacity (n : Expr) : M Unit :=
    checkCount env.top K0 "a map capacity" n
  let value (v : Ty) : M Unit := do
    let locks ← env.spinlocks v
    if locks > 1 then
      err v.span s!"the value type of map `{d.name}` has {locks} fields of \
        type `spinlock`; at most one field of type `spinlock` (section 7)"
    checkDataTy env v
    if let some why ← env.notRepresentable v true then
      err v.span s!"the value type of map `{d.name}` may not contain {why}: \
        map keys and values are packet-representable, and a value may hold \
        one `spinlock` (section 7)"
    let _ ← env.layout v
  match d.kind with
  | .array n v | .percpu n v =>
    capacity n
    value v
  | .hash n k v =>
    capacity n
    checkDataTy env k
    if let some why ← env.notRepresentable k false then
      err k.span s!"the key type of map `{d.name}` may not contain {why}: map \
        keys and values are packet-representable (section 7)"
    let _ ← env.layout k
    value v
  | .ringbuf n => capacity n

/-- A function against its signature (section 16). -/
def checkFn (env : Env) (f : Fn) : M Unit := do
  let mut locals : List Local := []
  let mut seen : List String := []
  for p in f.params do
    if seen.contains p.name then
      err p.span s!"parameter `{p.name}` is declared twice"
    seen := seen ++ [p.name]
    match p.ty with
    | .own .. =>
      err p.span s!"parameter `{p.name}` of `{f.name}`: user functions take \
        `ref` and `view` parameters and never `own` (section 16)"
    | .opt .. => err p.span "an optional is not a parameter type (section 16)"
    | .ref _ t =>
      checkDataTy env t
      locals := { name := p.name, ty := p.ty, mutable := false,
                  origin := .param } :: locals
    | .view _ t =>
      checkDataTy env t
      if let some why ← env.notRepresentable t false then
        err p.span s!"`{t.print}` is not packet-representable: it contains \
          {why} (section 7)"
      locals := { name := p.name, ty := p.ty, mutable := false,
                  origin := .pkt } :: locals
    | t =>
      checkDataTy env t
      let tn ← env.norm t
      unless tn.isScalar do
        err p.span s!"aggregates are passed by reference: declare \
          `{p.name}: ref {t.print}` (section 16)"
      let ty := match p.pred with
        | some q => Ty.refined p.span p.name t q
        | none => t
      locals := { name := p.name, ty, mutable := false, origin := .stack }
        :: locals
  let scalars := locals.reverse.filter fun l => !l.ty.isPlaceTy
  for p in f.params do
    if let some q := p.pred then
      checkPred env scalars q
  -- the result: a scalar, an optional scalar, or a refined scalar
  let resultScalar (t : Ty) : M Unit := do
    match t with
    | .ref .. | .view .. | .own .. =>
      err t.span s!"the result type of `{f.name}` must be a scalar: places \
        are never returned (section 7)"
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
  let K : Ctx := { mayFail := f.fails, ret := .fn f.name f.ret,
                   fnName := some f.name }
  checkStmts { env.top with locals } K f.body
  if f.ret.isSome && !exits f.body then
    err f.span s!"`{f.name}` has a result type, so its body must end in \
      `return` or an expression (section 16)"

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
      (section 16)"
  for h in (edges.lookup g).getD [] do
    visitCalls fns edges (path ++ [g]) h

/-- The call graph must be acyclic (section 16). -/
def checkCallGraph (env : Env) (fns : List Fn) : M Unit := do
  let edges : List (String × List String) := fns.map fun f =>
    (f.name, (calleesStmts f.body).filter fun g => (env.fn? g).isSome)
  for f in fns do
    visitCalls fns edges [] f.name

/-- The verdict names and regions of a contract or a program header
(section 14). -/
def checkClauses (env : Env) (row : KindRow)
    (verdicts : Option (List (Span × String))) (preserved : List Region) :
    M Unit := do
  if let some vs := verdicts then
    for (s, n) in vs do
      unless row.verdicts.any (·.1 == n) do
        err s s!"`{n}` is not a verdict of {article row.name} `{row.name}` \
          program (section 13)"
  for r in preserved do
    match r with
    | .pkt s range =>
      unless row.hasPkt do
        err s s!"{article row.name} `{row.name}` program has no packet \
          (section 13)"
      if let some (lo, hi) := range then
        for e in [lo, hi] do
          unless env.isConstExpr e do
            err e.span "the bounds of `pkt[a .. b)` are constant expressions \
              (section 14.1)"
          check env.top K0 e tU64
    | .map s m =>
      unless (env.map? m).isSome do err s s!"unknown map `{m}` in `preserve`"
    | .mapsExcept s names =>
      for m in names do
        unless (env.map? m).isSome do
          err s s!"unknown map `{m}` in `preserve maps except`"
    | .ctx s f =>
      unless row.ctx.any (·.name == f) do
        err s s!"the context of {article row.name} `{row.name}` program has no \
          field `{f}` (section 13)"

def kindRow (env : Env) (span : Span) (kind : String) : M KindRow := do
  match env.prelude.kind? kind with
  | some row => return row
  | none =>
    err span s!"unknown program kind `{kind}`; the kinds are \
      {", ".intercalate (env.prelude.kinds.map (·.name))} (section 13)"

def checkContract (env : Env) (c : Contract) : M Unit := do
  let row ← kindRow env c.span c.kind
  checkClauses env row c.verdicts c.preserved

/-- (Program) and (Handler), the base premises: the kind, the
contract, the clauses, every handler exiting in a non-failing context,
and the body; the verdict-set and preserved-region demands on the
facts and effects are session 4. -/
def checkProgram (env : Env) (p : Program) : M Unit := do
  let row ← kindRow env p.span p.kind
  if let some (s, c) := p.implements then
    match env.contracts.find? (·.name == c) with
    | some k =>
      unless k.kind == p.kind do
        err s s!"contract `{c}` is for `{k.kind}` programs; `{p.name}` is \
          {article p.kind} `{p.kind}` program (section 14.2)"
    | none => err s s!"unknown contract `{c}`"
  checkClauses env row p.verdicts p.preserved
  let env := { env with kind := some row }
  let vset := p.verdicts.map (·.map (·.2))
  for h in p.handlers do
    let hEnv := env.bind { name := "reason", ty := tU32, mutable := false,
                           origin := .stack }
    let K : Ctx := { mayFail := false, ret := .handler row.verdictTy,
                     inHandler := true, verdictSet := vset }
    checkStmts hEnv K h.body
    unless exits h.body do
      err h.span s!"the handler for `{h.kind}` must end in an exit \
        (section 10.6)"
  let K : Ctx := { mayFail := true, ret := .program row.verdictTy,
                   verdictSet := vset }
  checkStmts env K p.body
  if row.hasPkt && !exits p.body then
    err p.span s!"the body of {article row.name} `{row.name}` program must end \
      in an exit (section 13)"

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

/-- The checker's entry point: every declaration of the unit, in the
order of section 23.1. -/
def checkUnit (pre : Prelude) (u : CompUnit) : M Unit := do
  checkNames u
  let env : Env := { prelude := pre, license := u.license.map (·.2),
                     types := u.types, consts := u.consts,
                     configs := u.configs, maps := u.maps, fns := u.fns,
                     contracts := u.contracts }
  for d in u.types do checkTypeDecl env d
  for d in u.consts do checkConst env d
  for d in u.configs do checkConfig env d
  for d in u.maps do checkMap env d
  for f in u.fns do checkFn env f
  checkCallGraph env u.fns
  for c in u.contracts do checkContract env c
  for p in u.programs do checkProgram env p

end Koit.Check
