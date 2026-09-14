import Koit.Check.Expr

/-!
The statement rules, the base half: bindings, assignment, branches,
loops, exits, `raise`, `try`, `hold`, and atomic updates, with the
shape rules of failure handling. No facts, held sets, or effects yet;
those premises come with entailment and effects, and the comments name
each rule they will complete. Declarations and programs are in
`Decl.lean`.
-/

namespace Koit.Check

open Koit (Span)
open Koit.Core
open Koit.Prelude (tU32 tU64)

/-- Whether a block ends in an exit: its
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

/-- The struct type a literal has:
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
       "
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
       "
    | ds =>
      err span s!"the fields `{", ".intercalate names}` belong to several \
        declared types ({", ".intercalate (ds.map (·.name))}); annotate the \
        binding with the type"

/-- A binding: the local it introduces. -/
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
       "
    | _ => pure ()
    -- (P3): an aggregate place is named
    if mutable then
      err span "`var` binds a scalar; an aggregate place is named with `let` \
       "
    if let some t := ty then
      unless ← env.eqv t info.ty do mismatch env p.span t info.ty
    let pty := if info.origin == .pkt then Ty.view span info.ty
      else Ty.ref span info.ty
    return { name := x, ty := pty, mutable := false, origin := info.origin }
  | .lit ls fields =>
    if mutable then
      err span "`var` binds a scalar; a struct literal is a place, named with \
        `let`"
    let st ← structForLiteral env ls ty fields
    let fs ← match ← env.norm st with
      | .struct _ fs => pure fs
      | _ => err ls "a struct literal has a struct type"
    unless fs.map (·.name) == fields.map (·.name) do
      err ls s!"a struct literal gives every field of `{st.print}` in order: \
        {", ".intercalate (fs.map (·.name))}"
    for (fd, fi) in fs.zip fields do
      let ftn ← env.norm fd.ty
      unless ftn.isScalar do
        err fi.span s!"field `{fd.name}` of `{st.print}` is a `{fd.ty.print}`; \
          struct literals have scalar fields only"
      -- the predicate of the field is a demand of session 3
      check env K fi.value fd.ty
    return { name := x, ty := .ref span st, mutable := false, origin := .stack }

/-- `return` against what the context returns to. -/
def checkRet (env : Env) (K : Ctx) (span : Span) (v : Option Expr) :
    M Unit := do
  match K.ret, v with
  | .program ty, some e | .handler ty, some e =>
    check env K e ty
    -- a verdict constant against the verdict set; a
    -- computed verdict is a demand of session 4
    match e, K.verdictSet with
    | .var vs n, some vset =>
      if (env.verdict? n).isSome && !vset.contains n then
        err vs s!"`{n}` is not in the verdict set"
    | _, _ => pure ()
  | .program _, none | .handler _, none =>
    err span "a program returns a verdict"
  | .fn _ none, none => pure ()
  | .fn f none, some _ => err span s!"`{f}` returns nothing"
  | .fn _ (some (.opt _ t)), none =>
    err span s!"a bare `return` in a function returning `{t.print}?` is not \
      yet defined by the language (an open design point)"
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
        -- a bare expression statement is a call
        match init with
        | .expr (.call s' f args) =>
          let _ ← synthCall env K s' f args false
        | .expr (.invalid s' m) => err s' m
        | _ => err span "a bare expression statement must be a call"
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
            `{(env.kind.map (·.name)).get!}` program"
        | _, _ =>
          err span s!"`{p.print}` is immutable; declare it with `var` to \
            assign to it"
      let tn ← env.norm info.ty
      match tn with
      | .spinlock _ => err span "a `spinlock` is not assigned"
      | _ => pure ()
      unless tn.isScalar do
        err span s!"`{p.print}` is an aggregate of type `{info.ty.print}`; \
          assign its fields, or use `copy` (P3)"
      check env K e tn
      checkStmts env K rest
    | .ite _ c t e =>
      -- (IfConst): a constant condition is folded after both branches
      -- are checked
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
      unless K.inLoop do err span "`break` outside a loop"
      checkStmts env K rest
    | .cont span =>
      unless K.inLoop do err span "`continue` outside a loop"
      checkStmts env K rest
    | .ret span v =>
      checkRet env K span v
      checkStmts env K rest
    | .raise span _ r =>
      -- (Mark), (Fail): the context may fail
      unless K.mayFail do
        if K.inHandler then
          err span "a handler is a non-failing context: no marker and no \
            `fail` may appear in it"
        err span s!"`{K.fnName.getD "?"}` is not marked `fails`, so it may not \
          contain a marker, `check`, or `fail`"
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
         "
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
          needs `?` or `else`"
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
            resource, `hold {acqName acq} \{ ... }`"
        | none, some _ =>
          err span s!"`{acqName acq}` yields a value; bind it with \
            `hold x = ...`"
      checkStmts env' K body
      if let some e := els then
        checkStmts env { K with errnoOk := row.fails == some .helper } e
        unless exits e do
          err span s!"the `else` block must end in an exit: {exitForms} \
           "
      checkStmts env K rest
    | .atomic span x op p args =>
      let info ← placeTy env K p
      unless info.mutable do err span s!"`{p.print}` is immutable"
      let tn ← env.norm info.ty
      unless tn.isIntTy do
        err span s!"atomic updates apply to an integer place; `{p.print}` is a \
          `{info.ty.print}`"
      match info.origin with
      | .stack | .map _ => pure ()
      | _ =>
        err span "atomic updates apply to a place in a map value or on the \
          stack"
      let n := if op == .cmpxchg then 2 else 1
      unless args.length == n do
        err span s!"`{op.spelling}` takes a place and {n} value(s) \
         "
      for a in args do
        check env K a tn
      let env' := match x with
        | some n => env.bind { name := n, ty := tn, mutable := false,
                               origin := .stack }
        | none => env
      checkStmts env' K rest
    | .invalid span m => err span m

end Koit.Check
