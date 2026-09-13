import Koit.Syntax.Lexer
import Koit.Syntax.AST

/-!
A recursive-descent parser for the grammar of spec/language.md
sections 6 to 9, 14, and 15, with the precedence table of section 5.

Newlines are tokens (see `Lexer`). Here they are statement
terminators inside blocks and between top-level items, and whitespace
inside brackets, in a program header, and in a contract, per
spec/ISSUES.md entry 6. A block may end in a bare expression (entry
7); `abort` in statement position is a verdict.

Every error carries the span of the token that could not be used and
names what was expected there.
-/

namespace Koit.Syntax

structure ParseError where
  span : Span
  msg  : String
  deriving Repr, Inhabited

instance : ToString ParseError := ⟨fun e => s!"{e.span.start}: {e.msg}"⟩

namespace Parser

structure State where
  toks : Array Lexeme
  i    : Nat := 0
  /-- Whether a newline token ends a statement here (true in blocks
  and at top level) or is whitespace (brackets, headers). -/
  nlSignificant : Bool := true
  /-- The end of the last token consumed, for closing spans. -/
  prevStop : Pos := Pos.origin

abbrev M := StateT State (Except ParseError)

/-! ### Tokens -/

/-- The current lexeme. When newlines are whitespace, skips them. The
last lexeme is always `eof`, which is never skipped or passed. -/
def cur : M Lexeme := do
  let st ← get
  if st.nlSignificant then
    return st.toks[st.i]!
  let mut i := st.i
  while i + 1 < st.toks.size && st.toks[i]!.tok == .newline do
    i := i + 1
  set { st with i }
  return st.toks[i]!

def peekTok : M Token := return (← cur).tok

/-- The lexeme `k` tokens after the current one, under the same
newline rule; for one- and two-token lookahead. -/
def lexemeAt (k : Nat) : M Lexeme := do
  let _ ← cur
  let st ← get
  let mut i := st.i
  for _ in [:k] do
    if i + 1 < st.toks.size then
      i := i + 1
    if !st.nlSignificant then
      while i + 1 < st.toks.size && st.toks[i]!.tok == .newline do
        i := i + 1
  return st.toks[i]!

/-- Consumes the current lexeme. -/
def advance : M Unit := do
  let _ ← cur
  modify fun st =>
    if st.i + 1 < st.toks.size then
      { st with i := st.i + 1, prevStop := st.toks[st.i]!.span.stop }
    else st

/-- Runs `p` with newlines significant or not, restoring the mode. -/
def withNl (sig : Bool) (p : M α) : M α := do
  let old := (← get).nlSignificant
  modify fun st => { st with nlSignificant := sig }
  let r ← p
  modify fun st => { st with nlSignificant := old }
  return r

/-- The span from `start` to the end of the last consumed token. -/
def spanFrom (start : Span) : M Span := do
  return { start := start.start, stop := (← get).prevStop }

/-! ### Errors and expectations -/

def failAt (span : Span) (msg : String) : M α :=
  throw { span, msg }

def unexpected (expected : String) : M α := do
  let l ← cur
  failAt l.span s!"expected {expected}, found {l.tok.describe}"

def isPunct (p : Punct) : M Bool := return (← peekTok) == .punct p
def isKw (k : Keyword) : M Bool := return (← peekTok) == .keyword k
def isIdent (s : String) : M Bool := return (← peekTok) == .ident s

/-- Consumes `p` if it is next. -/
def acceptPunct (p : Punct) : M Bool := do
  if (← isPunct p) then
    advance
    return true
  return false

def expectPunct (p : Punct) : M Span := do
  let l ← cur
  if l.tok == .punct p then
    advance
    return l.span
  unexpected s!"`{p.spelling}`"

def expectKw (k : Keyword) : M Span := do
  let l ← cur
  if l.tok == .keyword k then
    advance
    return l.span
  unexpected s!"`{k.spelling}`"

def expectIdent (what : String := "an identifier") : M (String × Span) := do
  let l ← cur
  match l.tok with
  | .ident n =>
    advance
    return (n, l.span)
  | _ => unexpected what

/-- Newlines and semicolons, as many as there are. -/
partial def skipTerminators : M Unit := do
  match ← peekTok with
  | .newline | .punct .semi =>
    advance
    skipTerminators
  | _ => pure ()

/-- After a statement or an item: a newline or `;`, consumed; or a
`}` or the end of file, left in place. -/
def endStmt : M Unit := do
  match ← peekTok with
  | .newline | .punct .semi => advance
  | .punct .rbrace | .eof => pure ()
  | _ => unexpected "a newline or `;` to end the statement"

/-! ### Small tables -/

def primType (span : Span) : String → Ty
  | "u8"  => .int span false 8   | "u16" => .int span false 16
  | "u32" => .int span false 32  | "u64" => .int span false 64
  | "i8"  => .int span true 8    | "i16" => .int span true 16
  | "i32" => .int span true 32   | "i64" => .int span true 64
  | "be16" => .be span 16 | "be32" => .be span 32 | "be64" => .be span 64
  | "bool" => .bool span
  | "spinlock" => .spinlock span
  | n => .named span n

def cmpOp : Token → Option BinOp
  | .punct .eqEq => some .eq | .punct .bangEq => some .ne
  | .punct .lt => some .lt   | .punct .le => some .le
  | .punct .gt => some .gt   | .punct .ge => some .ge
  | _ => none

def assignOp : Token → Option AssignOp
  | .punct .assign => some .set
  | .punct .plusAssign => some .add   | .punct .minusAssign => some .sub
  | .punct .starAssign => some .mul   | .punct .ampAssign => some .band
  | .punct .pipeAssign => some .bor   | .punct .caretAssign => some .bxor
  | .punct .shlAssign => some .shl    | .punct .shrAssign => some .shr
  | _ => none

/-- Whether a token can begin an expression. `{` is left out: a
struct literal never follows `return` or `fail`, and a block does. -/
def canStartExpr : Token → Bool
  | .int .. | .char .. | .string .. | .ident .. => true
  | .keyword .«true» | .keyword .«false» | .keyword .«move» => true
  | .punct .lparen | .punct .bang | .punct .minus | .punct .star => true
  | _ => false

/-- Method names that take a type argument, `recv.name<T>(...)`. -/
def typeCallNames : List String := ["reserve"]

mutual

-- Types

/-- A type; `allowOpt` is false after `as`, where a trailing `?` is
the statement's marker, not part of the type. -/
partial def parseType (allowOpt : Bool := true) : M Ty := do
  let l ← cur
  match l.tok with
  | .keyword .«ref» =>
    advance
    let t ← parseType allowOpt
    return .ref (l.span.merge t.span) t
  | .keyword .«view» =>
    advance
    let t ← parseType allowOpt
    return .view (l.span.merge t.span) t
  | .keyword .«own» =>
    advance
    let t ← parseType allowOpt
    return .own (l.span.merge t.span) t
  | _ => parsePostfixType allowOpt

partial def parsePostfixType (allowOpt : Bool) : M Ty := do
  let mut t ← parseTypeAtom
  while true do
    match ← peekTok with
    | .punct .lbrack =>
      advance
      let n ← withNl false parseExpr
      let close ← expectPunct .rbrack
      t := .array (t.span.merge close) t n
    | .punct .question =>
      if !allowOpt then break
      let q ← cur
      advance
      t := .opt (t.span.merge q.span) t
    | _ => break
  return t

partial def parseTypeAtom : M Ty := do
  let l ← cur
  match l.tok with
  | .ident name =>
    advance
    return primType l.span name
  | .punct .lbrace => withNl false do
    advance
    let (name, nspan) ← expectIdent "a field name"
    let _ ← expectPunct .colon
    let ty ← parseType
    -- `{ v: T | P }` is a refinement; anything else is a struct
    if (← isPunct .pipe) then
      advance
      let pred ← parseExpr
      let close ← expectPunct .rbrace
      return .refined (l.span.merge close) name ty pred
    let mut fields := [← parseFieldRest nspan name ty]
    while (← acceptPunct .comma) do
      if (← isPunct .rbrace) then break
      let (n, ns) ← expectIdent "a field name"
      let _ ← expectPunct .colon
      let t ← parseType
      fields := fields ++ [← parseFieldRest ns n t]
    let close ← expectPunct .rbrace
    return .struct (l.span.merge close) fields
  | _ => unexpected "a type: a primitive, a name, `{`, `ref`, `view`, or `own`"

/-- The optional `where P` of a struct field, after its type. -/
partial def parseFieldRest (start : Span) (name : String) (ty : Ty) :
    M Field := do
  if (← isKw .«where») then
    advance
    let p ← parseExpr
    return .mk (start.merge p.span) name ty (some p)
  return .mk (start.merge ty.span) name ty none

-- Expressions, loosest first

partial def parseExpr : M Expr := parseLor

partial def parseLor : M Expr := parseLeftAssoc parseLand [(.pipePipe, .lor)]
partial def parseLand : M Expr := parseLeftAssoc parseCmp [(.ampAmp, .land)]

/-- Comparisons do not associate: `a < b < c` is an error. -/
partial def parseCmp : M Expr := do
  let l ← parseBor
  match cmpOp (← peekTok) with
  | none => return l
  | some op =>
    advance
    let r ← parseBor
    if (cmpOp (← peekTok)).isSome then
      let c ← cur
      failAt c.span "comparisons do not chain; parenthesize one of them"
    return .binary (l.span.merge r.span) op l r

partial def parseBor : M Expr := parseLeftAssoc parseBxor [(.pipe, .bor)]
partial def parseBxor : M Expr := parseLeftAssoc parseBand [(.caret, .bxor)]
partial def parseBand : M Expr := parseLeftAssoc parseShift [(.amp, .band)]
partial def parseShift : M Expr :=
  parseLeftAssoc parseAdd [(.shl, .shl), (.shr, .shr)]
partial def parseAdd : M Expr :=
  parseLeftAssoc parseMul [(.plus, .add), (.minus, .sub)]
partial def parseMul : M Expr :=
  parseLeftAssoc parseCast [(.star, .mul), (.slash, .div), (.percent, .mod)]

partial def parseLeftAssoc (next : M Expr) (ops : List (Punct × BinOp)) :
    M Expr := do
  let mut l ← next
  while true do
    match ← peekTok with
    | .punct p =>
      match ops.lookup p with
      | some op =>
        advance
        let r ← next
        l := .binary (l.span.merge r.span) op l r
      | none => break
    | _ => break
  return l

partial def parseCast : M Expr := do
  let mut e ← parseUnary
  while (← isKw .«as») do
    advance
    let t ← parseType (allowOpt := false)
    e := .cast (e.span.merge t.span) e t
  return e

partial def parseUnary : M Expr := do
  let l ← cur
  match l.tok with
  | .punct .bang =>
    advance
    let e ← parseUnary
    return .unary (l.span.merge e.span) .not e
  | .punct .minus =>
    advance
    let e ← parseUnary
    return .unary (l.span.merge e.span) .neg e
  | .punct .star =>
    advance
    let e ← parseUnary
    return .unary (l.span.merge e.span) .deref e
  | .keyword .«move» =>
    advance
    let (name, s) ← expectIdent "the name to move"
    return .move (l.span.merge s) name
  | _ => parsePostfix

partial def parsePostfix : M Expr := do
  let mut e ← parsePrimary
  while true do
    match ← peekTok with
    | .punct .dot =>
      advance
      let l ← cur
      match l.tok with
      | .keyword .«view» =>
        advance
        e ← parseTypeCall e "view"
      | .ident name =>
        advance
        if typeCallNames.contains name && (← isPunct .lt) then
          e ← parseTypeCall e name
        else
          e := .field (e.span.merge l.span) e name
      | _ => unexpected "a field name"
    | .punct .lbrack =>
      advance
      let idx ← withNl false parseExpr
      let close ← expectPunct .rbrack
      e := .index (e.span.merge close) e idx
    | .punct .lparen =>
      let (args, close) ← parseArgs
      e := .call (e.span.merge close) e args
    | _ => break
  return e

/-- `<T>(args)` after `recv.name`. -/
partial def parseTypeCall (recv : Expr) (name : String) : M Expr := do
  let _ ← expectPunct .lt
  let ty ← parseType (allowOpt := false)
  let _ ← expectPunct .gt
  let (args, close) ← parseArgs
  return .tcall (recv.span.merge close) recv name ty args

/-- `(e, ...)`; returns the arguments and the span of the `)`. -/
partial def parseArgs : M (List Expr × Span) := do
  let _ ← expectPunct .lparen
  withNl false do
    let mut args := []
    if !(← isPunct .rparen) then
      args := [← parseExpr]
      while (← acceptPunct .comma) do
        args := args ++ [← parseExpr]
    let close ← expectPunct .rparen
    return (args, close)

partial def parsePrimary : M Expr := do
  let l ← cur
  match l.tok with
  | .int v t =>
    advance
    return .int l.span v t
  | .char c =>
    advance
    return .char l.span c
  | .string s =>
    advance
    return .str l.span s
  | .keyword .«true» =>
    advance
    return .bool l.span true
  | .keyword .«false» =>
    advance
    return .bool l.span false
  | .ident name =>
    advance
    return .var l.span name
  | .punct .lparen =>
    advance
    let e ← withNl false parseExpr
    let close ← expectPunct .rparen
    return .paren (l.span.merge close) e
  | .punct .lbrace => withNl false do
    advance
    let mut fields := [← parseFieldInit]
    while (← acceptPunct .comma) do
      if (← isPunct .rbrace) then break
      fields := fields ++ [← parseFieldInit]
    let close ← expectPunct .rbrace
    return .structLit (l.span.merge close) fields
  | _ => unexpected "an expression"

partial def parseFieldInit : M FieldInit := do
  let (name, s) ← expectIdent "a field name"
  let _ ← expectPunct .colon
  let v ← parseExpr
  return .mk (s.merge v.span) name v

-- Statements

partial def parseBlock : M Block := do
  let open_ ← expectPunct .lbrace
  withNl true do
    let mut stmts := []
    skipTerminators
    while !(← isPunct .rbrace) do
      if (← peekTok) == .eof then
        unexpected "`}`"
      stmts := stmts ++ [← parseStmt]
      endStmt
      skipTerminators
    let close ← expectPunct .rbrace
    return .mk (open_.merge close) stmts

partial def parseStmt : M Stmt := do
  let l ← cur
  match l.tok with
  | .keyword .«let» => parseDecl false
  | .keyword .«var» => parseDecl true
  | .keyword .«if» => parseIf
  | .keyword .«repeat» =>
    advance
    let n ← parseExpr
    let body ← parseBlock
    return .loop (l.span.merge body.span) n body
  | .keyword .«for» => parseFor
  | .keyword .«hold» => parseHold
  | .keyword .«check» =>
    advance
    let c ← parseExpr
    let tail ← parseTail
    return .check (← spanFrom l.span) c tail
  | .keyword .«break» =>
    advance
    return .brk l.span
  | .keyword .«continue» =>
    advance
    return .cont l.span
  | .keyword .«return» =>
    advance
    let v ← parseOptExpr
    return .ret (← spanFrom l.span) v
  | .keyword .«pass» =>
    advance
    return .verdict l.span .pass
  | .keyword .«drop» =>
    advance
    return .verdict l.span .drop
  | .keyword .«tx» =>
    advance
    return .verdict l.span .tx
  | .keyword .«fail» =>
    advance
    let r ← parseOptExpr
    return .fail (← spanFrom l.span) r
  | .ident "abort" =>
    -- the verdict, unless it is used as an expression
    match (← lexemeAt 1).tok with
    | .punct .lparen | .punct .dot | .punct .lbrack => parseExprStmt
    | _ =>
      advance
      return .verdict l.span .abort
  | tok =>
    if canStartExpr tok then
      parseExprStmt
    else
      unexpected "a statement: `let`, `var`, `if`, `repeat`, `for`, \
        `hold`, `check`, a verdict, `return`, `fail`, `break`, \
        `continue`, or a call"

partial def parseOptExpr : M (Option Expr) := do
  if canStartExpr (← peekTok) then
    return some (← parseExpr)
  return none

/-- An assignment, or an expression statement with its tail. -/
partial def parseExprStmt : M Stmt := do
  let e ← parseExpr
  match assignOp (← peekTok) with
  | some op =>
    if !e.isPlace then
      failAt e.span "the left side of an assignment must be a place: \
        a variable, a field, an element, or `*x`"
    advance
    let v ← parseExpr
    return .assign (e.span.merge v.span) e op v
  | none =>
    let tail ← parseTail
    return .expr (← spanFrom e.span) e tail

partial def parseTail : M (Option Tail) := do
  let l ← cur
  match l.tok with
  | .punct .question =>
    advance
    return some (.mark l.span)
  | .keyword .«else» =>
    advance
    if (← isPunct .lbrace) then
      let b ← parseBlock
      return some (.elseBlock (l.span.merge b.span) b)
    let s ← parseExit
    return some (.elseExit (l.span.merge s.span) s)
  | _ => return none

/-- A statement that must be an exit form. -/
partial def parseExit : M Stmt := do
  let s ← parseStmt
  if !s.isExit then
    failAt s.span "expected an exit: `fail`, a verdict, `return`, \
      `break`, or `continue`"
  return s

partial def parseDecl (mutable : Bool) : M Stmt := do
  let l ← cur
  advance
  let (name, _) ← expectIdent "a name"
  let mut ty := none
  let mut pred := none
  if (← acceptPunct .colon) then
    ty := some (← parseType)
    if (← isKw .«where») then
      advance
      pred := some (← parseExpr)
  let _ ← expectPunct .assign
  let init ← parseExpr
  let tail ← parseTail
  return .decl (← spanFrom l.span) mutable name ty pred init tail

partial def parseIf : M Stmt := do
  let l ← cur
  advance
  if (← isKw .«let») then
    advance
    let (name, _) ← expectIdent "a name"
    let _ ← expectPunct .assign
    let init ← parseExpr
    let thn ← parseBlock
    let els ← parseElse
    return .iteLet (← spanFrom l.span) name init thn els
  let c ← parseExpr
  let thn ← parseBlock
  let els ← parseElse
  return .ite (← spanFrom l.span) c thn els

/-- `else { ... }` or `else if ...`, the latter as a one-statement
block. -/
partial def parseElse : M (Option Block) := do
  if !(← isKw .«else») then
    return none
  advance
  if (← isKw .«if») then
    let s ← parseIf
    return some (.mk s.span [s])
  return some (← parseBlock)

partial def parseFor : M Stmt := do
  let l ← cur
  advance
  let pat ← do
    if (← isPunct .lparen) then
      let p ← cur
      advance
      let (k, _) ← expectIdent "a name"
      let _ ← expectPunct .comma
      let (v, _) ← expectIdent "a name"
      let close ← expectPunct .rparen
      pure (Pattern.pair (p.span.merge close) k v)
    else
      let (n, s) ← expectIdent "a loop variable"
      pure (Pattern.one s n)
  let _ ← expectKw .«in»
  let first ← parseExpr
  if (← isPunct .dotdot) then
    advance
    let hi ← parseExpr
    let body ← parseBlock
    match pat with
    | .one _ n => return .forRange (← spanFrom l.span) n first hi body
    | .pair s .. =>
      failAt s "a range loop binds one name; `(k, v)` iterates a map"
  let _ ← expectKw .«bounded»
  let bound ← parseExpr
  let marked ← acceptPunct .question
  let body ← parseBlock
  return .forIter (← spanFrom l.span) pat first bound marked body

partial def parseHold : M Stmt := do
  let l ← cur
  advance
  let name ← do
    match (← cur).tok, (← lexemeAt 1).tok with
    | .ident n, .punct .assign =>
      advance
      advance
      pure (some n)
    | _, _ => pure none
  let acq ← parseExpr
  let tail ← parseTail
  let body ← parseBlock
  return .hold (← spanFrom l.span) name acq tail body

-- Declarations

partial def parseUnit : M CompUnit := do
  skipTerminators
  let license ← do
    if (← isKw .«license») then
      let l ← cur
      advance
      match (← cur).tok with
      | .string s =>
        let sl ← cur
        advance
        endStmt
        skipTerminators
        pure (some (l.span.merge sl.span, s))
      | _ => unexpected "a string after `license`"
    else pure none
  let mut items := []
  while (← peekTok) != .eof do
    items := items ++ [← parseItem]
    endStmt
    skipTerminators
  return { license, items }

partial def parseItem : M Item := do
  let l ← cur
  match l.tok with
  | .keyword .«const» =>
    advance
    let (name, _) ← expectIdent "a constant name"
    let mut ty := none
    if (← acceptPunct .colon) then
      ty := some (← parseType)
    let _ ← expectPunct .assign
    let v ← parseExpr
    return .const (← spanFrom l.span) name ty v
  | .keyword .«config» =>
    advance
    let (name, _) ← expectIdent "a configuration name"
    let _ ← expectPunct .colon
    let ty ← parseType
    let mut init := none
    if (← acceptPunct .assign) then
      init := some (← parseExpr)
    return .config (← spanFrom l.span) name ty init
  | .keyword .«type» =>
    advance
    let (name, _) ← expectIdent "a type name"
    let _ ← expectPunct .assign
    let ty ← parseType
    return .type (← spanFrom l.span) name ty
  | .keyword .«map» =>
    advance
    let (name, _) ← expectIdent "a map name"
    let _ ← expectPunct .colon
    let mt ← parseMapType
    return .map (← spanFrom l.span) name mt
  | .keyword .«fn» => return .fn (← parseFn)
  | .keyword .«contract» => return .contract (← parseContract)
  | .keyword .«program» => return .program (← parseProgram)
  | _ => unexpected "a declaration: `const`, `config`, `type`, `map`, \
      `fn`, `contract`, or `program`"

partial def parseMapType : M MapType := do
  let (kind, ks) ← expectIdent
    "a map kind: `array`, `percpu_array`, `hash`, or `ringbuf`"
  let _ ← expectPunct .lbrack
  let n ← withNl false parseExpr
  let close ← expectPunct .rbrack
  match kind with
  | "array" =>
    let _ ← expectKw .«of»
    let v ← parseType
    return .array (ks.merge v.span) n v
  | "percpu_array" =>
    let _ ← expectKw .«of»
    let v ← parseType
    return .percpuArray (ks.merge v.span) n v
  | "hash" =>
    let _ ← expectKw .«of»
    let k ← parseType
    let _ ← expectPunct .arrow
    let v ← parseType
    return .hash (ks.merge v.span) n k v
  | "ringbuf" => return .ringbuf (ks.merge close) n
  | _ => failAt ks s!"unknown map kind `{kind}`; expected `array`, \
      `percpu_array`, `hash`, or `ringbuf`"

partial def parseFn : M FnDecl := do
  let l ← cur
  advance
  let (name, _) ← expectIdent "a function name"
  let _ ← expectPunct .lparen
  let params ← withNl false do
    let mut ps := []
    if !(← isPunct .rparen) then
      ps := [← parseParam]
      while (← acceptPunct .comma) do
        ps := ps ++ [← parseParam]
    let _ ← expectPunct .rparen
    pure ps
  let ret ← do
    if (← acceptPunct .arrow) then
      pure (some (← parseRetType))
    else pure none
  let fails ← do
    if (← isKw .«fails») then
      advance
      pure true
    else pure false
  let body ← parseBlock
  return { span := ← spanFrom l.span, name, params, ret, fails, body }

partial def parseParam : M Param := do
  let (name, s) ← expectIdent "a parameter name"
  let _ ← expectPunct .colon
  let ty ← parseType
  if (← isKw .«where») then
    advance
    let p ← parseExpr
    return { span := s.merge p.span, name, ty, pred := some p }
  return { span := s.merge ty.span, name, ty, pred := none }

partial def parseRetType : M RetType := do
  match (← cur).tok, (← lexemeAt 1).tok with
  | .ident name, .punct .colon =>
    let s := (← cur).span
    advance
    advance
    let ty ← parseType
    let _ ← expectKw .«where»
    let p ← parseExpr
    return .refined (s.merge p.span) name ty p
  | _, _ => return .ty (← parseType)

partial def parseContract : M Contract := do
  let l ← cur
  advance
  let (name, _) ← expectIdent "a contract name"
  let _ ← expectPunct .colon
  let (kind, _) ← expectIdent "a program kind"
  let _ ← expectPunct .lbrace
  let (clauses, close) ← withNl false do
    let mut cs := []
    while !(← isPunct .rbrace) do
      cs := cs ++ [← parseClause]
    let close ← expectPunct .rbrace
    pure (cs, close)
  return { span := l.span.merge close, name, kind, clauses }

partial def parseClause : M Clause := do
  let l ← cur
  match l.tok with
  | .keyword .«verdict» =>
    advance
    let _ ← expectKw .«in»
    let _ ← expectPunct .lbrace
    let mut names := [(← expectIdent "a verdict name").1]
    while (← acceptPunct .comma) do
      names := names ++ [(← expectIdent "a verdict name").1]
    let close ← expectPunct .rbrace
    return .verdicts (l.span.merge close) names
  | .keyword .«preserve» =>
    advance
    let mut regions := [← parseRegion]
    while (← acceptPunct .comma) do
      regions := regions ++ [← parseRegion]
    return .preserve (← spanFrom l.span) regions
  | _ => unexpected "`verdict` or `preserve`"

partial def parseRegion : M Region := do
  let (name, s) ← expectIdent
    "a region: `pkt`, `maps`, a map name, or `ctx.field`"
  match name with
  | "pkt" =>
    if (← isPunct .lbrack) then
      advance
      let lo ← withNl false parseExpr
      let _ ← expectPunct .dotdot
      let hi ← withNl false parseExpr
      let close ← expectPunct .rparen
      return .pkt (s.merge close) (some (lo, hi))
    return .pkt s none
  | "maps" =>
    if (← isKw .«except») then
      advance
      let mut names := [(← expectIdent "a map name").1]
      while (← acceptPunct .comma) do
        names := names ++ [(← expectIdent "a map name").1]
      return .maps (← spanFrom s) names
    return .maps s []
  | "ctx" =>
    let _ ← expectPunct .dot
    let (f, fs) ← expectIdent "a context field"
    return .ctxField (s.merge fs) f
  | _ => return .map s name

/-- `program p : kind [implements C] clause* [fail exit] handler*
{ body }`; newlines in the header are whitespace. -/
partial def parseProgram : M Program := do
  let l ← cur
  advance
  let (name, _) ← expectIdent "a program name"
  let _ ← expectPunct .colon
  let (kind, _) ← expectIdent "a program kind"
  withNl false do
    let implements ← do
      if (← isKw .«implements») then
        advance
        pure (some (← expectIdent "a contract name").1)
      else pure none
    let mut clauses := []
    while (← isKw .«verdict») || (← isKw .«preserve») do
      clauses := clauses ++ [← parseClause]
    let failExit ← do
      if (← isKw .«fail») then
        advance
        pure (some (← parseExit))
      else pure none
    let mut handlers := []
    while (← isKw .«on») do
      handlers := handlers ++ [← parseHandler]
    let body ← parseBlock
    return { span := ← spanFrom l.span, name, kind, implements, clauses,
             failExit, handlers, body }

partial def parseHandler : M Handler := do
  let l ← cur
  advance
  let kinds ← do
    if (← isIdent "_") then
      advance
      pure none
    else
      let mut ks := [← parseKind]
      while (← acceptPunct .comma) do
        ks := ks ++ [← parseKind]
      pure (some ks)
  let body ← parseBlock
  return { span := l.span.merge body.span, kinds, body }

/-- A failure kind; `program` is a keyword that is also a kind. -/
partial def parseKind : M String := do
  let l ← cur
  match l.tok with
  | .ident n =>
    advance
    return n
  | .keyword .«program» =>
    advance
    return "program"
  | _ => unexpected "a failure kind"

end

end Parser

/-- Lexes and parses one compilation unit. -/
def parse (src : String) : Except ParseError CompUnit :=
  match lex src with
  | .error e => .error { span := Span.point e.pos, msg := e.msg }
  | .ok toks =>
    match Parser.parseUnit.run { toks } with
    | .ok (u, _) => .ok u
    | .error e => .error e

end Koit.Syntax
