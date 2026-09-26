import Koit.Syntax.AST
import Koit.Syntax.Print
import Koit.Core.Syntax
import Koit.Core.Print
import Koit.Interface.Decls

/-!
Desugaring, surface to Core: the syntactic rewrite of each surface
construct into its Core form. It is a total
function over the unit's declarations and the kernel interface, and it
uses no types: what needs a type stays in Core (functions, constant
conditionals, `for`, and a binding whose right side is a place).

What it does: markers and `else` tails become `try` with an explicit
`raise` of the operation's kind; `check P` is the
coercion `P as {b: bool | b}`; `if let` is a `try` whose `else` need not
exit; `hold` takes its resource from the interface's resources and its tail
becomes the `else` of the acquisition; `for x in it bounded N` is the
`hold` plus `loop` plus `try next` of (ForIter); verdict statements
are `return` of the kind's verdict constant; `fail` is `raise` with the
enclosing `else` block's kind or `program`; `-e` is `0 - e`; `p op= e`
is `p := rd p op e`; a function body's tail expression is its
`return`; and every program's handler table is made total from its
handlers, its `fail` exit, and the kind's default.

Surface forms with no meaning where they stand, a fallible operation
outside the positions that consume one for instance, become `invalid`
nodes carrying the diagnostic, so that the function is total and the
checker reports the error at the source line. Fresh names contain
`$`, which no surface identifier can.
-/

namespace Koit.Core

open Koit (Span)
open Koit.Interface (KindDecl)

namespace Desugar

/-- What the desugaring reads from the unit and the interface. -/
structure Info where
  interface   : Interface
  types     : List String
  maps      : List (String × Syntax.MapType)
  fns       : List Syntax.FnDecl
  contracts : List Syntax.Contract

/-- The syntactic context of a statement. -/
structure Ctx where
  info : Info
  /-- The program kind's declaration, inside a program body or handler. -/
  kind : Option KindDecl := none
  /-- The kind of the enclosing `else` block, for `fail`. -/
  elseKind : Option Kind := none
  /-- Names bound by enclosing statements; a local shadows a map or a
  type name. -/
  locals : List String := []
  /-- Whether a trailing expression is the function's result: true at
  the top of a function body with a result type only. -/
  tailIsResult : Bool := false

def Ctx.bind (c : Ctx) (x : String) : Ctx :=
  { c with locals := x :: c.locals }

def Ctx.bindAll (c : Ctx) (xs : List String) : Ctx :=
  { c with locals := xs ++ c.locals }

/-- A nested block: a trailing expression there is a statement. -/
def Ctx.nested (c : Ctx) : Ctx := { c with tailIsResult := false }

def Ctx.isLocal (c : Ctx) (x : String) : Bool := c.locals.contains x

/-- The enumeration a type name names, if it names one: one the
interface declares, or `verdict`, which is the enclosing kind's. A
coercion to one is fallible, since the value tested comes in as an
integer. -/
def Ctx.enumNamed? (c : Ctx) : Syntax.Ty → Option String
  | .named _ n =>
    if c.isLocal n then none
    else if n == "verdict" then
      c.kind.bind fun decl =>
        match decl.verdictTy with
        | .named _ e => (c.info.interface.enum? e).map (·.name)
        | .enum _ e => some e
        | _ => none
    else match c.info.interface.type? n with
      | some d =>
        match d.ty with
        | .enum _ e => some e
        | _ => none
      | none => none
  | _ => none

/-- The map `x` names, unless a local shadows it. -/
def Ctx.map? (c : Ctx) (x : String) : Option Syntax.MapType :=
  if c.isLocal x then none else c.info.maps.lookup x

def Ctx.isType (c : Ctx) (x : String) : Bool :=
  !c.isLocal x && c.info.types.contains x

def Ctx.fn? (c : Ctx) (x : String) : Option Syntax.FnDecl :=
  if c.isLocal x then none else c.info.fns.find? (·.name == x)

/-- A fresh-name supply. -/
abbrev M := StateM Nat

def fresh (hint : String) : M String := do
  let n ← get
  set (n + 1)
  return s!"${hint}{n + 1}"

/-- The primitive type a name spells, if any. -/
def primTy? (span : Span) : String → Option Ty
  | "u8"  => some (.int span false 8)   | "u16" => some (.int span false 16)
  | "u32" => some (.int span false 32)  | "u64" => some (.int span false 64)
  | "i8"  => some (.int span true 8)    | "i16" => some (.int span true 16)
  | "i32" => some (.int span true 32)   | "i64" => some (.int span true 64)
  | "be16" => some (.be span 16) | "be32" => some (.be span 32)
  | "be64" => some (.be span 64) | "bool" => some (.bool span)
  | _ => none

def lit0 (span : Span) : Expr := .lit span 0 "0"

/-- The default reason of a `raise` of kind `k`: the helper's negative
return for `helper`, 0 otherwise. -/
def defaultReason (span : Span) : Kind → Expr
  | .failed_call => .errno span
  | _ => lit0 span

def unmarkedMsg (what : String) (k : Kind) : String :=
  s!"{what} can fail (kind `{k}`): a fallible operation appears only \
    as the initializer of `let`, `var`, `if let`, or `hold`, or as a \
    statement, marked with `?` or followed by `else`"

def BinOp.arith? : Syntax.BinOp → Option ArithOp
  | .mul => some .mul | .div => some .div | .mod => some .mod
  | .add => some .add | .sub => some .sub | .shl => some .shl
  | .shr => some .shr | .band => some .band | .bxor => some .bxor
  | .bor => some .bor
  | _ => none

def BinOp.cmp? : Syntax.BinOp → Option CmpOp
  | .eq => some .eq | .ne => some .ne | .lt => some .lt | .le => some .le
  | .gt => some .gt | .ge => some .ge
  | _ => none

/-- A surface expression whose value is not read through a place:
`T.size` and `pkt.len` are place-shaped but denote values. -/
def isValueField (c : Ctx) : Syntax.Expr → Bool
  | .field _ (.var _ "pkt") "len" => true
  | .field _ (.var _ t) "size" => c.isType t || (primTy? default t).isSome
  | _ => false

/-- The failure kind of a fallible operation, from the resource's declaration
for an acquisition. -/
def kindOf (c : Ctx) : Fallible → Kind
  | .acquire _ r .. =>
    match c.info.interface.resource? r with
    | some decl => decl.fails.getD .failed_call
    | none => .failed_call
  | f => f.kind?.getD .failed_call

/-- The description a diagnostic uses for a fallible operation. -/
def describe : Fallible → String
  | .view .. => "`pkt.view`"
  | .lookup _ m _ => s!"the lookup in the hash map `{m}`"
  | .loadw _ p => s!"the marked load of `{p.print}`"
  | .call _ f _ => s!"`{f}`"
  | .acquire _ _ f .. => s!"`{f}`"
  | .callopt _ f _ => s!"`{f}`, which returns an optional,"
  | .coerce .. => "the coercion"
  | .tail _ m _ => s!"the tail call through `{m}`"

/-- A fallible operation as the surface writes it: one of section
8.3's forms, or the byte read `pkt[off]`, which binds the byte read
through a one-byte view. -/
inductive Op where
  | op (f : Fallible)
  | byte (span : Span) (off : Expr)

mutual

partial def dTy (c : Ctx) : Syntax.Ty → M Ty
  | .int s signed w => pure (.int s signed w)
  | .be s w => pure (.be s w)
  | .bool s => pure (.bool s)
  | .named s n => pure (.named s n)
  | .struct s fields => do
    let names := fields.map (·.name)
    return .struct s (← fields.mapM (dField (c.bindAll names)))
  | .refined s v t p => do
    return .refined s v (← dTy c t) (← dExpr (c.bind v) p)
  | .array s t n => do return .array s (← dTy c t) (← dExpr c n)
  | .ref s t => do return .ref s (← dTy c t)
  | .view s t => do return .view s (← dTy c t)
  | .opt s t => do return .opt s (← dTy c t)
  | .own s t => do return .own s (← dTy c t)

partial def dField (c : Ctx) : Syntax.Field → M Field
  | .mk s n t p => do
    return .mk s n (← dTy c t) (← p.mapM (dExpr c))

/-- Classifies a surface expression as a fallible operation. `marked`
says whether a marker or `else` follows, which is what makes a field
read a marked load. -/
partial def fallible? (c : Ctx) (marked : Bool) : Syntax.Expr → M (Option Op)
  | .paren _ e => fallible? c marked e
  | .cast s e (.refined ts v t p) => do
    let t' ← dTy c t
    let p' ← dExpr (c.bind v) p
    return some (.op (.coerce s (← dExpr c e) (.refined ts v t' p')))
  | .cast s e t => do
    match c.enumNamed? t with
    | none => return none
    | some n =>
      -- `e as E?` is the coercion whose predicate the declaration states: one
      -- of its constants, and no other value.
      let decl := c.info.interface.enum? n
      let atoms := (decl.map (·.constants)).getD [] |>.map fun (k, _) =>
        Expr.cmp s .eq (.var s "v") (.var s k)
      let pred := match atoms with
        | [] => Expr.invalid s s!"the enumeration `{n}` has no constants"
        | a :: rest => rest.foldl (fun P q => Expr.or s P q) a
      return some (.op (.coerce s (← dExpr c e)
        (.refined s "v" (← dTy c t) pred)))
  | .tcall s (.var _ "pkt") "view" ty args => do
    let off ← match args with
      | [e] => dExpr c e
      | _ => pure (.invalid s "`pkt.view<T>(off)` takes one argument, \
          the offset")
    return some (.op (.view s off (← dTy c ty)))
  | .index s (.var _ "pkt") off => do
    return some (.byte s (← dExpr c off))
  | .index s (.var _ m) k => do
    match c.map? m with
    | some (.hash ..) => return some (.op (.lookup s m (← dPlace c k)))
    | _ => return none
  | .tcall s (.var _ m) "reserve" ty [] => do
    -- the ring-buffer record's resource, from its declaration
    match c.map? m, c.info.interface.acquirer? "reserve" with
    | some _, some decl =>
      return some (.op (.acquire s decl.res "reserve" (some (← dTy c ty))
        [.map s m]))
    | _, _ => return none
  | .call s (.var _ f) args => do
    if let some d := c.fn? f then
      match d.ret with
      | some (.ty (.opt ..)) =>
        return some (.op (.callopt s f (← args.mapM (dArg c))))
      | _ => return none
    if let some decl := c.info.interface.call? f then
      if let some r := decl.acquires then
        return some (.op (.acquire s r f none (← args.mapM (dArg c))))
      if decl.fails.isSome then
        return some (.op (.call s f (← args.mapM (dArg c))))
      return none
    if let some decl := c.info.interface.acquirer? f then
      return some (.op (.acquire s decl.res f none (← args.mapM (dArg c))))
    return none
  | .call s (.field _ (.var _ "pkt") n) args => do
    if n == "adjust_head" || n == "adjust_tail" then
      return some (.op (.call s ("pkt." ++ n) (← args.mapM (dArg c))))
    return none
  | .call s (.field ms (.var _ m) n) args => do
    if (c.map? m).isSome && (n == "insert" || n == "delete") then
      return some (.op (.call s n (.map ms m :: (← args.mapM (dArg c)))))
    return none
  | e@(.field s _ _) => do
    if marked && e.isPlace then
      return some (.op (.loadw s (← dPlace c e)))
    return none
  | .var s f => do
    -- a scope-only resource, `hold rcu { }`
    match c.info.interface.acquirer? f with
    | some decl => return some (.op (.acquire s decl.res f none []))
    | none => return none
  | _ => return none

/-- An expression in value position. A fallible operation here is an
error the checker reports. -/
partial def dExpr (c : Ctx) (e : Syntax.Expr) : M Expr := do
  if let some op ← fallible? c false e then
    match op with
    | .op f => return .invalid e.span (unmarkedMsg (describe f) (kindOf c f))
    | .byte s _ => return .invalid s (unmarkedMsg "the byte read `pkt[off]`"
        .short_packet)
  match e with
  | .int s v t => return .lit s v t
  | .char s v => return .char s v
  | .str s v => return .str s v
  | .bool s b => return .bool s b
  | .var s n => return .var s n
  | .paren _ e => dExpr c e
  | .unary s .not e => return .not s (← dExpr c e)
  | .unary s .neg e => return .arith s .sub (lit0 s) (← dExpr c e)
  | .unary s .deref e => return .read s (.deref s (← dExpr c e))
  | .move s n => return .move s n
  | .binary s op l r => do
    let l' ← dExpr c l
    let r' ← dExpr c r
    match op with
    | .land => return .and s l' r'
    | .lor => return .or s l' r'
    | _ =>
      match BinOp.arith? op, BinOp.cmp? op with
      | some a, _ => return .arith s a l' r'
      | _, some k => return .cmp s k l' r'
      | _, _ => return .invalid s "unknown operator"
  | .cast s e t => return .cast s (← dExpr c e) (← dTy c t)
  | .field s (.var _ "pkt") "len" => return .call s "pkt.len" []
  | .field s (.var ts t) "size" =>
    if c.isType t then return .size s (.named ts t)
    else if let some pt := primTy? ts t then return .size s pt
    else return .read s (← dPlace c e)
  | .field s _ _ => return .read s (← dPlace c e)
  | .index s _ _ => return .read s (← dPlace c e)
  | .call s (.var _ "hton") [a] => return .hton s (← dExpr c a)
  | .call s (.var _ "ntoh") [a] => return .ntoh s (← dExpr c a)
  | .call s (.var _ f) _ =>
    if (AtomicOp.ofString? f).isSome then
      return .invalid s s!"`{f}` appears only as the initializer of a \
        binding or as a statement"
    else
      return .call s f (← callArgs c e)
  | .call s f _ => return .call s (← calleeName c f) (← callArgs c e)
  | .tcall s r n _ _ =>
    return .invalid s s!"`{r.print}.{n}<T>` is not an operation; the \
      forms are `pkt.view<T>(off)` and `rb.reserve<T>()`"
  | .structLit s _ =>
    return .invalid s "a struct literal appears only as the initializer \
      of `let` or `var`"

/-- The name a call's callee denotes: a function, a interface call, or
a method on `pkt` or a map spelled with its receiver. -/
partial def calleeName (c : Ctx) : Syntax.Expr → M String
  | .var _ f => pure f
  | .field _ (.var _ "pkt") n => pure ("pkt." ++ n)
  | .field _ (.var _ m) n =>
    if (c.map? m).isSome then pure n else pure (m ++ "." ++ n)
  | e => pure e.print

/-- The arguments of a call, with a map receiver first. -/
partial def callArgs (c : Ctx) : Syntax.Expr → M (List Arg)
  | .call _ (.field s (.var _ m) _) args => do
    let args' ← args.mapM (dArg c)
    if (c.map? m).isSome then return .map s m :: args' else return args'
  | .call _ _ args => args.mapM (dArg c)
  | _ => pure []

partial def dArg (c : Ctx) (e : Syntax.Expr) : M Arg := do
  match e with
  | .var s m =>
    -- a map, a local place, or a constant of the unit or interface
    if (c.map? m).isSome then return .map s m
    if c.isLocal m then return .place (.var s m)
    return .val (.var s m)
  | .paren _ e => dArg c e
  | _ =>
    if isValueField c e then return .val (← dExpr c e)
    if e.isPlace then return .place (← dPlace c e)
    return .val (← dExpr c e)

/-- An expression in place position. -/
partial def dPlace (c : Ctx) (e : Syntax.Expr) : M Place := do
  match e with
  | .var s n => return .var s n
  | .paren _ e => dPlace c e
  | .field s (.var _ "pkt") f =>
    return .invalid s s!"`pkt.{f}`: the packet is read through views"
  | .field s b f =>
    if isValueField c e then
      return .invalid s s!"`{e.print}` is a value, not a place"
    return .field s (← dPlace c b) f
  | .index s (.var _ "pkt") _ =>
    return .invalid s (unmarkedMsg "the byte read `pkt[off]`" .short_packet)
  | .index s (.var vs m) i =>
    match c.map? m with
    | some (.hash ..) =>
      return .invalid s (unmarkedMsg s!"the lookup in the hash map `{m}`"
        .not_found)
    | some _ => return .slot s m (← dExpr c i)
    | none => return .index s (.var vs m) (← dExpr c i)
  | .index s b i => return .index s (← dPlace c b) (← dExpr c i)
  | .unary s .deref e => return .deref s (← dExpr c e)
  | _ =>
    return .invalid e.span s!"`{e.print}` is not a place: a place is a \
      variable, a map slot, a field, an element, or `*x`"

end

/-! ### Statements -/

/-- The Core of an `else` tail of kind `k`: the marker raises with
the default reason; a block or exit runs with `k` as the kind `fail`
raises. -/
def tailKind (c : Ctx) (k : Kind) : Ctx := { c.nested with elseKind := some k }

mutual

partial def dBlock (c : Ctx) (b : Syntax.Block) : M (List Stmt) :=
  dStmts c.nested b.stmts

partial def dTail (c : Ctx) (k : Kind) : Syntax.Tail → M (List Stmt)
  | .mark s => pure [.raise s k (defaultReason s k)]
  | .elseBlock _ b => dStmts (tailKind c k) b.stmts
  | .elseExit _ s => dStmts (tailKind c k) [s]

/-- `try x = F then rest else tail`, or the byte read's temporary. -/
partial def dTry (c : Ctx) (span : Span) (x : String) (op : Op)
    (tail : Syntax.Tail) (rest : List Syntax.Stmt) (mutable : Bool)
    (ty : Option Ty) : M (List Stmt) := do
  match op with
  | .op f =>
    let k := kindOf c f
    let els ← dTail c k tail
    let rest' ← dStmts (c.bind x) rest
    -- a declared type on a marked binding restates the operation's
    -- result; it is kept as a plain rebinding for the checker
    let thn := match ty with
      | some t =>
        Stmt.«let» span mutable x (some t) (.expr (.var span x)) :: rest'
      | none => rest'
    return [.«try» span x f thn els true]
  | .byte s off =>
    let v ← fresh "b"
    let els ← dTail c .short_packet tail
    let rest' ← dStmts (c.bind x) rest
    let read : Stmt := .«let» span mutable x ty (.expr (.read s (.deref s
      (.var s v))))
    return [.«try» span v (.view s off (.int s false 8)) (read :: rest') els
      true]

/-- A binding with no tail. -/
partial def dInit (c : Ctx) (span : Span) (mutable : Bool) (x : String)
    (ty : Option Ty) (init : Syntax.Expr) : M Stmt := do
  match init with
  | .structLit s fields =>
    let fields' ← fields.mapM fun (.mk fs n v) => do
      return ({ span := fs, name := n, value := ← dExpr c v } : FieldInit)
    return .«let» span mutable x ty (.lit s fields')
  | .call _ (.var _ f) args =>
    match AtomicOp.ofString? f, args with
    | some op, p :: vs =>
      return .atomic span (some x) op (← dPlace c p) (← vs.mapM (dExpr c))
    | some op, [] =>
      return .atomic span (some x) op
        (.invalid span s!"`{f}` needs a place and a value") []
    | none, _ => return .«let» span mutable x ty (.expr (← dExpr c init))
  | .var _ n =>
    -- a local names a place; a constant or a verdict is a value
    if c.isLocal n then
      return .«let» span mutable x ty (.place (← dPlace c init))
    return .«let» span mutable x ty (.expr (← dExpr c init))
  | _ =>
    if init.isPlace && !isValueField c init then
      return .«let» span mutable x ty (.place (← dPlace c init))
    return .«let» span mutable x ty (.expr (← dExpr c init))

/-- The verdict statement of a kind, as `return` of the verdict's
name. -/
partial def dVerdict (c : Ctx) (span : Span) (v : Syntax.Verdict) : Stmt :=
  let word := v.spelling
  match c.kind with
  | none => .ret span (some (.invalid span s!"`{word}` is a verdict \
      statement, which belongs in a program body"))
  | some decl =>
    match decl.sugar.lookup word with
    | some name => .ret span (some (.var span name))
    | none => .ret span (some (.invalid span s!"`{word}` is not a verdict \
        statement of a `{decl.name}` program"))

/-- The acquisition of a `hold`, with its resource. -/
partial def acquisition (c : Ctx) (acq : Syntax.Expr) :
    M (Option (Resource × Fallible)) := do
  match ← fallible? c false acq with
  | some (.op f@(.acquire _ r ..)) => return some (r, f)
  | _ => return none

partial def dStmts (c : Ctx) : List Syntax.Stmt → M (List Stmt)
  | [] => pure []
  | s :: rest => do
    match s with
    | .decl span mutable x sty pred init tail =>
      let ty ← match sty, pred with
        | some t, some p =>
          pure (some (.refined t.span x (← dTy c t) (← dExpr (c.bind x) p)))
        | some t, none => pure (some (← dTy c t))
        | none, _ => pure none
      match tail with
      | none =>
        let s' ← dInit c span mutable x ty init
        return s' :: (← dStmts (c.bind x) rest)
      | some t =>
        match ← fallible? c true init with
        | some op => dTry c span x op t rest mutable ty
        | none =>
          let s' : Stmt := .«let» span mutable x ty (.expr (.invalid init.span
            s!"`{init.print}` cannot fail, so it takes no `?` or `else`"))
          return s' :: (← dStmts (c.bind x) rest)
    | .assign span target op value =>
      let p ← dPlace c target
      let v ← dExpr c value
      let v' := match op with
        | .set => v
        | .add => .arith span .add (.read span p) v
        | .sub => .arith span .sub (.read span p) v
        | .mul => .arith span .mul (.read span p) v
        | .band => .arith span .band (.read span p) v
        | .bor => .arith span .bor (.read span p) v
        | .bxor => .arith span .bxor (.read span p) v
        | .shl => .arith span .shl (.read span p) v
        | .shr => .arith span .shr (.read span p) v
      return .assign span p v' :: (← dStmts c rest)
    | .ite span cond thn els =>
      let s' : Stmt := .ite span (← dExpr c cond) (← dBlock c thn)
        (← match els with | some b => dBlock c b | none => pure [])
      return s' :: (← dStmts c rest)
    | .iteLet span x init thn els =>
      let els' ← match els with | some b => dBlock c b | none => pure []
      let s' ← match ← fallible? c true init with
        | some (.op f) =>
          pure (Stmt.«try» span x f (← dBlock (c.bind x) thn) els' false)
        | some (.byte s off) =>
          let v ← fresh "b"
          let read : Stmt := .«let» span false x none
            (.expr (.read s (.deref s (.var s v))))
          pure (Stmt.«try» span v (.view s off (.int s false 8))
            (read :: (← dBlock (c.bind x) thn)) els' false)
        | none =>
          pure (Stmt.«let» span false x none (.expr (.invalid init.span
            s!"`{init.print}` cannot fail; `if let` consumes a fallible \
              operation")))
      return s' :: (← dStmts c rest)
    | .loop span n body =>
      let s' : Stmt := .loop span (← dExpr c n) (← dBlock c body)
      return s' :: (← dStmts c rest)
    | .forRange span i lo hi body =>
      let s' : Stmt := .«for» span i (← dExpr c lo) (← dExpr c hi)
        (← dBlock (c.bind i) body)
      return s' :: (← dStmts c rest)
    | .forIter span pat it bound marked body =>
      let s' ← dForIter c span pat it bound marked body
      return s' :: (← dStmts c rest)
    | .hold span name acq tail body =>
      let c' := match name with | some n => c.bind n | none => c
      match ← acquisition c acq with
      | some (r, f) =>
        let els ← match tail with
          | some t => pure (some (← dTail c (kindOf c f) t))
          | none => pure none
        let s' : Stmt := .hold span r name f (← dBlock c' body) els
        return s' :: (← dStmts c rest)
      | none =>
        let pre := c.info.interface
        let head := match acq with
          | .call _ (.var _ f) _ | .var _ f => f
          | _ => acq.print
        let msg := match pre.missing? head with
          | some why => s!"`{head}` is not on kernel {pre.kernel}: {why}"
          | none =>
            let decls := pre.resources.flatMap fun r => r.acquirers.map fun a =>
              match r.arg with
              | .place _ => s!"`{a}(p)`"
              | .scope => s!"`{a}`"
              | .call => if a == "reserve" then "`rb.reserve<T>()`" else s!"`{a}(t)`"
            s!"`{acq.print}` is not a resource acquisition on kernel {pre.kernel}: \
              the resources the interface declares are {", ".intercalate decls}"
        let s' : Stmt := .invalid acq.span msg
        return s' :: (← dStmts c rest)
    | .tail span m i tail =>
      -- a taken call never returns, so nothing follows it for that
      -- case; the else block is what a call not taken runs
      let i' ← dExpr c i
      let els ← match tail with
        | some t => dTail c .no_program t
        | none => pure [.raise span .no_program (lit0 span)]
      let rest' ← dStmts c rest
      return [.«try» span "_" (.tail span m i') [] els true] ++ rest'
    | .check span cond tail =>
      let p ← dExpr c cond
      let bs := cond.span
      let boolTrue : Ty := .refined bs "b" (.bool bs) (.var bs "b")
      let els ← match tail with
        | some t => dTail c .failed_check t
        | none => pure [.raise span .failed_check (lit0 span)]
      let rest' ← dStmts c rest
      return [.«try» span "_" (.coerce span p boolTrue) rest' els true]
    | .expr span e tail =>
      match tail with
      | none =>
        if rest.isEmpty && c.tailIsResult then
          return [.ret span (some (← dExpr c e))]
        match e with
        | .call _ (.var _ f) (p :: vs) =>
          if let some op := AtomicOp.ofString? f then
            let s' : Stmt := .atomic span none op (← dPlace c p)
              (← vs.mapM (dExpr c))
            return s' :: (← dStmts c rest)
          let s' : Stmt := .«let» span false "_" none (.expr (← dExpr c e))
          return s' :: (← dStmts c rest)
        | _ =>
          let s' : Stmt := .«let» span false "_" none (.expr (← dExpr c e))
          return s' :: (← dStmts c rest)
      | some t =>
        match ← fallible? c true e with
        | some op => dTry c span "_" op t rest false none
        | none =>
          let s' : Stmt := .«let» span false "_" none (.expr (.invalid e.span
            s!"`{e.print}` cannot fail, so it takes no `?` or `else`"))
          return s' :: (← dStmts c rest)
    | .brk span => return .brk span :: (← dStmts c rest)
    | .cont span => return .cont span :: (← dStmts c rest)
    | .ret span v =>
      let s' : Stmt := .ret span (← v.mapM (dExpr c))
      return s' :: (← dStmts c rest)
    | .verdict span v => return dVerdict c span v :: (← dStmts c rest)
    | .fail span r =>
      let k := c.elseKind.getD .fail
      let r' ← match r with
        | some e => dExpr c e
        | none => pure (defaultReason span k)
      return .raise span k r' :: (← dStmts c rest)

/-- (ForIter): `hold I h = new(it) (var i = 0 ; loop N (try x = next(h)
then (s' ; i := i + 1) else break))`, and with `bounded N?` one more
`next` after the loop when the cap was reached. -/
partial def dForIter (c : Ctx) (span : Span) (pat : Syntax.Pattern)
    (it bound : Syntax.Expr) (marked : Bool) (body : Syntax.Block) :
    M Stmt := do
  let h ← fresh "it"
  let i ← fresh "i"
  let n ← dExpr c bound
  let next : Fallible := .callopt span "next" [.place (.var span h)]
  let (binders, names) ← match pat with
    | .one _ x => pure (([] : List Stmt), [x])
    | .pair s k v =>
      let e ← fresh "kv"
      pure ([Stmt.«let» s false k none (.place (.field s (.var s e) "key")),
             Stmt.«let» s false v none
               (.place (.field s (.var s e) "value"))],
            [e, k, v])
  let x := names.head!
  let body' ← dBlock (c.bindAll names) body
  let step : Stmt := .assign span (.var span i)
    (.arith span .add (.var span i) (.lit span 1 "1"))
  let loop : Stmt := .loop span n
    [.«try» span x next (binders ++ body' ++ [step]) [.brk span] false]
  let overflow : List Stmt :=
    if marked then
      [.ite span (.cmp span .eq (.var span i) n)
        [.«try» span "_" next [.raise span .failed_check (lit0 span)] [] false] []]
    else []
  let init : Stmt := .«let» span true i none (.expr (lit0 span))
  return .hold span .iter (some h) (.acquire span .iter "iter" none
    [← dArg c it]) (init :: loop :: overflow) none

end

/-! ### Declarations -/

def dParam (c : Ctx) (p : Syntax.Param) : M Param := do
  return { span := p.span, name := p.name, ty := ← dTy c p.ty,
           pred := ← p.pred.mapM (dExpr (c.bind p.name)) }

def dRet (c : Ctx) : Syntax.RetType → M Ty
  | .ty t => dTy c t
  | .refined s n t p => do
    return .refined s n (← dTy c t) (← dExpr (c.bind n) p)

def dFn (info : Info) (d : Syntax.FnDecl) : M Fn := do
  let names := d.params.map (·.name)
  let c : Ctx := { info, locals := names }
  let params ← d.params.mapM (dParam c)
  let ret ← d.ret.mapM (dRet c)
  let body ← dStmts { c with tailIsResult := ret.isSome } d.body.stmts
  return { span := d.span, name := d.name, params, ret, fails := d.fails,
           global := d.global,
           body }

def dRegion (c : Ctx) : Syntax.Region → M Region
  | .pkt s none => pure (.pkt s none)
  | .pkt s (some (lo, hi)) => do
    return .pkt s (some (← dExpr c lo, ← dExpr c hi))
  | .maps s names => pure (.mapsExcept s names)
  | .map s n => pure (.map s n)
  | .ctxField s f => pure (.ctx s f)

/-- The verdict set and preserved regions of a clause list. -/
def dClauses (c : Ctx) (clauses : List Syntax.Clause) :
    M (Option (List (Span × String)) × List Region) := do
  let mut verdicts : Option (List (Span × String)) := none
  let mut preserved : List Region := []
  for cl in clauses do
    match cl with
    | .verdicts s names =>
      let vs := names.map fun n => (s, n)
      verdicts := some (match verdicts with
        | some old => old.filter fun (_, n) => names.contains n
        | none => vs)
    | .preserve _ regions =>
      preserved := preserved ++ (← regions.mapM (dRegion c))
  return (verdicts, preserved)

def dContract (info : Info) (k : Syntax.Contract) : M Contract := do
  let (verdicts, preserved) ← dClauses { info } k.clauses
  return { span := k.span, name := k.name, kind := k.kind, verdicts,
           preserved }

/-- The intersection of two verdict sets, or the one given; the
demands of a contract and inline clauses are their union. -/
def meetVerdicts : Option (List (Span × String)) →
    Option (List (Span × String)) → Option (List (Span × String))
  | some a, some b => some (a.filter fun (_, n) => b.any (·.2 == n))
  | some a, none => some a
  | none, b => b

/-- A program's total handler table, and the problems
found while building it, as `invalid` statements for the body. -/
def dHandlers (c : Ctx) (p : Syntax.Program) (decl : KindDecl) :
    M (List Handler × List Stmt × List (Span × Kind)) := do
  let hc : Ctx := { c with locals := ["reason"], elseKind := none }
  let mut problems : List Stmt := []
  let mut seen : List String := []
  for h in p.handlers do
    for k in h.kinds.getD [] do
      if (Kind.ofString? k).isNone then
        problems := problems ++ [.invalid h.span s!"`{k}` is not a failure \
          kind; the kinds are short_packet, not_found, bad_value, \
          failed_check, failed_call, and fail"]
      else if seen.contains k then
        problems := problems ++ [.invalid h.span s!"the kind `{k}` has two \
          handlers; at most one handler per kind"]
      seen := seen ++ [k]
  if (p.handlers.filter (·.kinds.isNone)).length > 1 then
    problems := problems ++ [.invalid p.span "two `default` handlers"]
  let mut table : List Handler := []
  for k in Kind.all do
    let listed := p.handlers.find? fun h =>
      (h.kinds.getD []).contains k.spelling
    let wild := p.handlers.find? (·.kinds.isNone)
    let body ← match listed <|> wild with
      | some h => do
        let b ← dStmts hc h.body.stmts
        pure (h.span, b)
      | none =>
          let s := p.span
          let d : Expr := match decl.defaultExit with
            | .verdict n => .var s n
            | .value v =>
              if v < 0 then .arith s .sub (lit0 s) (.lit s v.natAbs
                (toString v.natAbs))
              else .lit s v.natAbs (toString v.natAbs)
          pure (s, [Stmt.ret s (some d)])
    table := table ++ [{ span := body.1, kind := k, body := body.2 }]
  -- the kinds an `on` handler named, for the reachability rule
  let mut named : List (Span × Kind) := []
  for h in p.handlers do
    for k in h.kinds.getD [] do
      if let some kk := Kind.ofString? k then
        named := named ++ [(h.span, kk)]
  return (table, problems, named)

def dProgram (info : Info) (p : Syntax.Program) : M Program := do
  let c : Ctx := { info, kind := info.interface.kind? p.kind }
  let (verdicts, preserved) ← dClauses c p.clauses
  let (verdicts, preserved) ← match p.implements.bind fun n =>
      info.contracts.find? (·.name == n) with
    | some k =>
      let (kv, kp) ← dClauses c k.clauses
      pure (meetVerdicts verdicts kv, preserved ++ kp)
    | none => pure (verdicts, preserved)
  let (handlers, problems, named) ← match c.kind with
    | some decl => dHandlers c p decl
    | none =>
      -- an unknown kind: an empty table; the checker rejects the kind
      pure ([], [], [])
  let body ← dStmts c p.body.stmts
  let implements := p.implements.map fun n => (p.span, n)
  return { span := p.span, name := p.name, kind := p.kind, implements,
           verdicts, preserved, handlers, named, body := problems ++ body }

def dItem (info : Info) (u : CompUnit) : Syntax.Item → M CompUnit
  | .const s n ty v => do
    let c : Ctx := { info }
    let d : ConstDecl := { span := s, name := n, ty := ← ty.mapM (dTy c),
                           value := ← dExpr c v }
    return { u with consts := u.consts ++ [d] }
  | .config s n ty init => do
    let c : Ctx := { info }
    let d : ConfigDecl := { span := s, name := n, ty := ← dTy c ty,
                            init := ← init.mapM (dExpr c) }
    return { u with configs := u.configs ++ [d] }
  | .type s n ty => do
    let d : TypeDecl := { span := s, name := n, ty := ← dTy { info } ty }
    return { u with types := u.types ++ [d] }
  | .map s n mt access init => do
    let c : Ctx := { info }
    let kind ← match mt with
      | .array _ e v => pure (MapKind.array (← dExpr c e) (← dTy c v))
      | .percpuArray _ e v =>
        pure (MapKind.percpu (← dExpr c e) (← dTy c v))
      | .hash _ e k v =>
        pure (MapKind.hash (← dExpr c e) (← dTy c k) (← dTy c v))
      | .ringbuf _ e => pure (MapKind.ringbuf (← dExpr c e))
      | .progArray _ e k => pure (MapKind.progArray (← dExpr c e) k)
      | .sockmap _ e => pure (MapKind.sockmap (← dExpr c e))
      | .sockhash _ e k => pure (MapKind.sockhash (← dExpr c e) (← dTy c k))
    let init ← match init with
      | some es => es.mapM (dExpr c)
      | none => pure []
    let d : MapDecl := { span := s, name := n, kind, access, init }
    return { u with maps := u.maps ++ [d] }
  | .fn d => do return { u with fns := u.fns ++ [← dFn info d] }
  | .contract k => do
    return { u with contracts := u.contracts ++ [← dContract info k] }
  | .program p => do
    return { u with programs := u.programs ++ [← dProgram info p] }

end Desugar

/-- Desugars a unit against a interface. Total: every surface unit has a
Core form, in which ill-formed constructs are `invalid` nodes. -/
def desugar (pre : Interface) (u : Syntax.CompUnit) : CompUnit :=
  let info : Desugar.Info :=
    { interface := pre,
      types := u.items.filterMap fun
        | .type _ n _ => some n
        | _ => none,
      maps := u.items.filterMap fun
        | .map _ n mt _ _ => some (n, mt)
        | _ => none,
      fns := u.items.filterMap fun
        | .fn d => some d
        | _ => none,
      contracts := u.items.filterMap fun
        | .contract k => some k
        | _ => none }
  let empty : CompUnit :=
    { license := u.license, types := [], consts := [], configs := [],
      maps := [], fns := [], contracts := [], programs := [] }
  (u.items.foldlM (Desugar.dItem info) empty).run' 0

end Koit.Core
