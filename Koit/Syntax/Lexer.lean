import Koit.Syntax.Token

/-!
The lexer.

Identifiers `[A-Za-z_][A-Za-z0-9_]*`; integer literals in decimal,
`0x`, and `0b` with `_` separators; character literals denoting one
byte; string literals; `//` and non-nesting `/* */` comments. The
newline rule is applied here: a newline token is emitted only when the
previous token can end a statement (`Token.continuesLine` is false)
and it is not itself a newline, so blank lines and continuation lines
produce nothing. A block comment that spans lines counts as a newline.
Which newlines the parser treats as whitespace (inside brackets, in a
program header) is the parser's decision.

The lexer works on the UTF-8 bytes of the source. Every token is
ASCII; non-ASCII bytes are legal only inside comments and string
literals, and a column counts one per character, not per byte.
-/

namespace Koit.Syntax

/-- A lexical error at a position. The message names what was
expected or what was wrong; the parser's errors have the same shape. -/
structure LexError where
  pos : Pos
  msg : String
  deriving Repr, Inhabited

instance : ToString LexError := ⟨fun e => s!"{e.pos}: {e.msg}"⟩

namespace Lexer

structure State where
  src  : ByteArray
  pos  : Pos := Pos.origin
  toks : Array Lexeme := #[]
  /-- The last token emitted, for the newline rule. A file begins as if
  after a newline, so leading blank lines emit nothing. -/
  last : Token := .newline

abbrev M := StateT State (Except LexError)

/-- Fails at the current position, or at `at?` when given. -/
def fail (msg : String) (at? : Option Pos := none) : M α := do
  let st ← get
  throw { pos := at?.getD st.pos, msg }

/-- The byte `k` places ahead, if any. -/
def peek (k : Nat := 0) : M (Option UInt8) := do
  let st ← get
  let j := st.pos.byte + k
  return if j < st.src.size then some st.src[j]! else none

/-- Consumes one byte, keeping line and column current. A UTF-8
continuation byte does not advance the column. -/
def advance : M Unit := modify fun st =>
  let b := st.src[st.pos.byte]!
  let p := st.pos
  let p' :=
    if b == '\n'.toUInt8 then
      { line := p.line + 1, col := 1, byte := p.byte + 1 }
    else if b &&& 0xC0 == 0x80 then { p with byte := p.byte + 1 }
    else { p with col := p.col + 1, byte := p.byte + 1 }
  { st with pos := p' }

def advanceN : Nat → M Unit
  | 0 => pure ()
  | n + 1 => do
    advance
    advanceN n

/-- Emits a token spanning from `start` to the current position. -/
def emit (tok : Token) (start : Pos) : M Unit := modify fun st =>
  { st with
    toks := st.toks.push { tok, span := { start, stop := st.pos } },
    last := tok }

/-- The source text between two byte offsets. -/
def text (start stop : Nat) : M String := do
  let st ← get
  return String.fromUTF8! (st.src.extract start stop)

/-- Whether the source at the current position begins with `s`. -/
def matchesAt (st : State) (s : String) : Bool :=
  let bs := s.toUTF8
  let i := st.pos.byte
  i + bs.size ≤ st.src.size &&
    (List.range bs.size).all fun k => st.src[i + k]! == bs[k]!

partial def scanWhile (p : UInt8 → Bool) : M Unit := do
  match ← peek with
  | some b =>
    if p b then
      advance
      scanWhile p
  | none => pure ()

/-! ### Character classes, ASCII only -/

def isIdentStart (b : UInt8) : Bool :=
  let c := Char.ofNat b.toNat
  c.isAlpha || c == '_'

def isIdentChar (b : UInt8) : Bool :=
  isIdentStart b || (Char.ofNat b.toNat).isDigit

def isHexDigit (b : UInt8) : Bool :=
  let c := Char.ofNat b.toNat
  c.isDigit || ('a' ≤ c && c ≤ 'f') || ('A' ≤ c && c ≤ 'F')

/-- The value of a hex digit; meaningful only when `isHexDigit`. -/
def hexValue (b : UInt8) : Nat :=
  let c := Char.ofNat b.toNat
  if c.isDigit then c.toNat - '0'.toNat
  else if 'a' ≤ c && c ≤ 'f' then c.toNat - 'a'.toNat + 10
  else c.toNat - 'A'.toNat + 10

/-! ### The newline rule -/

/-- Emits a newline token at `at` unless the previous token continues
the line or is itself a newline. -/
def terminator (here : Pos) : M Unit := do
  let st ← get
  if st.last != .newline && !st.last.continuesLine then
    emit .newline here

/-! ### Comments -/

partial def skipLineComment : M Unit := do
  match ← peek with
  | some b =>
    if b != '\n'.toUInt8 then
      advance
      skipLineComment
  | none => pure ()

/-- Skips to the closing `*/`; returns whether a newline was inside. -/
partial def skipBlockComment (start : Pos) (sawNewline : Bool) : M Bool := do
  match ← peek with
  | none => fail "unterminated block comment" (some start)
  | some b =>
    if b == '*'.toUInt8 && (← peek 1) == some '/'.toUInt8 then
      advanceN 2
      return sawNewline
    advance
    skipBlockComment start (sawNewline || b == '\n'.toUInt8)

/-! ### Tokens -/

def ident (start : Pos) : M Unit := do
  scanWhile isIdentChar
  let s ← text start.byte (← get).pos.byte
  match Keyword.ofString? s with
  | some k => emit (.keyword k) start
  | none => emit (.ident s) start

/-- An integer literal. Every hex digit and `_` is scanned first, so
that a wrong digit for the base is an error at the digit rather than
the start of a new token. -/
def number (start : Pos) : M Unit := do
  let base ← do
    if (← peek) == some '0'.toUInt8 then
      match ← peek 1 with
      | some b =>
        if b == 'x'.toUInt8 then
          advanceN 2
          pure 16
        else if b == 'b'.toUInt8 then
          advanceN 2
          pure 2
        else pure 10
      | none => pure 10
    else pure 10
  let digits := (← get).pos
  scanWhile fun b => isHexDigit b || b == '_'.toUInt8
  let stop := (← get).pos
  let st ← get
  let mut value := 0
  let mut count := 0
  for k in [digits.byte : stop.byte] do
    let b := st.src[k]!
    if b == '_'.toUInt8 then continue
    let d := hexValue b
    if d ≥ base then
      let here : Pos :=
        { digits with col := digits.col + (k - digits.byte), byte := k }
      fail s!"digit `{Char.ofNat b.toNat}` is not valid in base {base}"
        (some here)
    value := value * base + d
    count := count + 1
  if count == 0 then
    fail "an integer literal needs at least one digit" (some start)
  match ← peek with
  | some b =>
    if isIdentChar b then
      fail "an integer literal cannot run into an identifier"
  | none => pure ()
  emit (.int value (← text start.byte stop.byte)) start

def hexDigit : M Nat := do
  match ← peek with
  | some b =>
    if isHexDigit b then
      advance
      return hexValue b
    fail "expected two hex digits after `\\x`"
  | none => fail "expected two hex digits after `\\x`"

/-- An escape sequence, after its backslash: `\n \r \t \0 \\ \' \"`
and `\xHH`. -/
def escape (start : Pos) : M UInt8 := do
  match ← peek with
  | none => fail "unterminated literal" (some start)
  | some b =>
    let here := (← get).pos
    advance
    match Char.ofNat b.toNat with
    | 'n'  => return '\n'.toUInt8
    | 'r'  => return '\r'.toUInt8
    | 't'  => return '\t'.toUInt8
    | '0'  => return 0
    | '\\' => return '\\'.toUInt8
    | '\'' => return '\''.toUInt8
    | '"'  => return '"'.toUInt8
    | 'x'  =>
      let hi ← hexDigit
      let lo ← hexDigit
      return (hi * 16 + lo).toUInt8
    | c => fail s!"unknown escape `\\{c}`" (some here)

/-- A character literal, after its opening quote; one byte. -/
def charLit (start : Pos) : M Unit := do
  let v ← do
    match ← peek with
    | none => fail "unterminated character literal" (some start)
    | some b =>
      if b == '\''.toUInt8 then
        fail "empty character literal" (some start)
      else if b == '\n'.toUInt8 then
        fail "unterminated character literal" (some start)
      else if b == '\\'.toUInt8 then
        advance
        escape start
      else if b ≥ 0x80 then
        fail "a character literal is one byte, so it must be ASCII" (some start)
      else
        advance
        pure b
  match ← peek with
  | some b =>
    if b == '\''.toUInt8 then
      advance
      emit (.char v) start
    else
      fail "expected `'` to close the character literal"
  | none => fail "expected `'` to close the character literal"

/-- A string literal, after its opening quote. -/
partial def stringLit (start : Pos) (buf : ByteArray) : M Unit := do
  match ← peek with
  | none => fail "unterminated string literal" (some start)
  | some b =>
    if b == '"'.toUInt8 then
      advance
      match String.fromUTF8? buf with
      | some s => emit (.string s) start
      | none => fail "string literal is not valid UTF-8" (some start)
    else if b == '\n'.toUInt8 then
      fail "unterminated string literal" (some start)
    else if b == '\\'.toUInt8 then
      advance
      let v ← escape start
      stringLit start (buf.push v)
    else
      advance
      stringLit start (buf.push b)

/-- Punctuation by longest match over `Punct.all`. -/
def punct (start : Pos) : M Unit := do
  let st ← get
  match Punct.all.find? (fun p => matchesAt st p.spelling) with
  | some p =>
    advanceN p.spelling.length
    emit (.punct p) start
  | none =>
    let b := st.src[st.pos.byte]!
    if b < 0x80 then
      fail s!"unexpected character `{Char.ofNat b.toNat}`"
    else
      fail "unexpected non-ASCII character"

partial def loop : M Unit := do
  let start := (← get).pos
  match ← peek with
  | none =>
    -- a final terminator, so every item ends the same way
    terminator start
    emit .eof start
  | some b =>
    let c := Char.ofNat b.toNat
    if c == ' ' || c == '\t' || c == '\r' then
      advance
    else if c == '\n' then
      advance
      terminator start
    else if c == '/' && (← peek 1) == some '/'.toUInt8 then
      skipLineComment
    else if c == '/' && (← peek 1) == some '*'.toUInt8 then
      advanceN 2
      if ← skipBlockComment start false then
        terminator start
    else if isIdentStart b then
      ident start
    else if c.isDigit then
      number start
    else if c == '\'' then
      advance
      charLit start
    else if c == '"' then
      advance
      stringLit start ByteArray.empty
    else
      punct start
    loop

end Lexer

/-- Lexes a whole source file. On success the last token is `eof`,
preceded by a newline unless the source ends in a continuation. -/
def lex (src : String) : Except LexError (Array Lexeme) :=
  match Lexer.loop.run { src := src.toUTF8 } with
  | .ok ((), st) => .ok st.toks
  | .error e => .error e

end Koit.Syntax
