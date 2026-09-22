import Koit.Syntax.Span

/-!
The tokens of koit.

The lexer produces a list of `Lexeme`, a token with its span. Newlines
are tokens, because a newline is a statement terminator
unless the previous token cannot end a statement; `Token.continuesLine`
is that predicate. Where a newline is a terminator and where it is
whitespace (inside brackets, inside a program header) is the parser's
decision, by context.
-/

namespace Koit.Syntax

/-- The reserved keywords. Spellings that are also Lean
keywords are quoted; the constructor is still named by the koit
spelling. -/
inductive Keyword where
  | «as» | «bounded» | «break» | «check» | «config» | «const»
  | «continue» | «contract» | «default» | «drop» | «else» | «except»
  | «fail»
  | «fails» | «false» | «fn» | «for» | «hold» | «if» | «implements»
  | «in» | «let» | «license» | «map» | «move» | «of» | «on» | «own»
  | «pass» | «preserve» | «program» | «ref» | «repeat» | «return»
  | «true» | «tx» | «type» | «var» | «verdict» | «view» | «where»
  deriving Repr, BEq, DecidableEq, Inhabited, Hashable

namespace Keyword

/-- The source spelling. -/
def spelling : Keyword → String
  | .«as» => "as"               | .«bounded» => "bounded"
  | .«break» => "break"         | .«check» => "check"
  | .«config» => "config"       | .«const» => "const"
  | .«continue» => "continue"   | .«contract» => "contract"
  | .«default» => "default"
  | .«drop» => "drop"           | .«else» => "else"
  | .«except» => "except"       | .«fail» => "fail"
  | .«fails» => "fails"         | .«false» => "false"
  | .«fn» => "fn"               | .«for» => "for"
  | .«hold» => "hold"           | .«if» => "if"
  | .«implements» => "implements" | .«in» => "in"
  | .«let» => "let"             | .«license» => "license"
  | .«map» => "map"             | .«move» => "move"
  | .«of» => "of"               | .«on» => "on"
  | .«own» => "own"             | .«pass» => "pass"
  | .«preserve» => "preserve"   | .«program» => "program"
  | .«ref» => "ref"             | .«repeat» => "repeat"
  | .«return» => "return"       | .«true» => "true"
  | .«tx» => "tx"               | .«type» => "type"
  | .«var» => "var"             | .«verdict» => "verdict"
  | .«view» => "view"           | .«where» => "where"

/-- Every keyword, for the lexer's table. -/
def all : List Keyword :=
  [.«as», .«bounded», .«break», .«check», .«config», .«const»,
   .«continue», .«contract», .«default», .«drop», .«else», .«except»,
   .«fail»,
   .«fails», .«false», .«fn», .«for», .«hold», .«if», .«implements»,
   .«in», .«let», .«license», .«map», .«move», .«of», .«on», .«own»,
   .«pass», .«preserve», .«program», .«ref», .«repeat», .«return»,
   .«true», .«tx», .«type», .«var», .«verdict», .«view», .«where»]

/-- The keyword with this spelling, if any. -/
def ofString? (s : String) : Option Keyword :=
  all.find? (·.spelling == s)

instance : ToString Keyword := ⟨spelling⟩

end Keyword

/-- Operators, brackets, and separators. -/
inductive Punct where
  | lparen | rparen | lbrack | rbrack | lbrace | rbrace
  | comma | dot | colon | semi | question | dotdot | arrow
  | assign | plusAssign | minusAssign | starAssign | ampAssign
  | pipeAssign | caretAssign | shlAssign | shrAssign
  | plus | minus | star | slash | percent | bang | amp | pipe | caret
  | shl | shr | eqEq | bangEq | lt | le | gt | ge | ampAmp | pipePipe
  deriving Repr, BEq, DecidableEq, Inhabited, Hashable

namespace Punct

/-- The source spelling. -/
def spelling : Punct → String
  | .lparen => "("      | .rparen => ")"      | .lbrack => "["
  | .rbrack => "]"      | .lbrace => "{"      | .rbrace => "}"
  | .comma => ","       | .dot => "."         | .colon => ":"
  | .semi => ";"        | .question => "?"    | .dotdot => ".."
  | .arrow => "->"      | .assign => "="      | .plusAssign => "+="
  | .minusAssign => "-=" | .starAssign => "*=" | .ampAssign => "&="
  | .pipeAssign => "|=" | .caretAssign => "^=" | .shlAssign => "<<="
  | .shrAssign => ">>=" | .plus => "+"        | .minus => "-"
  | .star => "*"        | .slash => "/"       | .percent => "%"
  | .bang => "!"        | .amp => "&"         | .pipe => "|"
  | .caret => "^"       | .shl => "<<"        | .shr => ">>"
  | .eqEq => "=="       | .bangEq => "!="     | .lt => "<"
  | .le => "<="         | .gt => ">"          | .ge => ">="
  | .ampAmp => "&&"     | .pipePipe => "||"

/-- Every punctuation token, longest spelling first, so a lexer that
tries them in this order takes the longest match. -/
def all : List Punct :=
  [.shlAssign, .shrAssign,
   .plusAssign, .minusAssign, .starAssign, .ampAssign, .pipeAssign,
   .caretAssign, .dotdot, .arrow, .eqEq, .bangEq, .le, .ge, .ampAmp,
   .pipePipe, .shl, .shr,
   .lparen, .rparen, .lbrack, .rbrack, .lbrace, .rbrace, .comma, .dot,
   .colon, .semi, .question, .assign, .plus, .minus, .star, .slash,
   .percent, .bang, .amp, .pipe, .caret, .lt, .gt]

instance : ToString Punct := ⟨spelling⟩

end Punct

/-- A token. Literals keep their text so that printing round-trips
`0x10` and `1_000` as written. -/
inductive Token where
  | ident (name : String)
  | keyword (k : Keyword)
  | int (value : Nat) (text : String)
  /-- A character literal, which denotes a `u8`. -/
  | char (value : UInt8)
  /-- A string literal; only `license` and `printk` take one. -/
  | string (value : String)
  | punct (p : Punct)
  | newline
  | eof
  deriving Repr, BEq, Inhabited

namespace Token

/-- How a diagnostic names the token. -/
def describe : Token → String
  | .ident n   => s!"identifier `{n}`"
  | .keyword k => s!"`{k.spelling}`"
  | .int _ t   => s!"integer `{t}`"
  | .char c    => s!"character literal ({c})"
  | .string s  => s!"string {s.quote}"
  | .punct p   => s!"`{p.spelling}`"
  | .newline   => "end of line"
  | .eof       => "end of file"

/-- Section 5: a newline after this token does not end a statement,
because the token cannot end one: an operator, a comma, `of`, `->`,
`=`, or an opening bracket. -/
def continuesLine : Token → Bool
  | .keyword .«of» => true
  | .punct p =>
    match p with
    | .rparen | .rbrack | .rbrace | .semi | .question => false
    | _ => true
  | _ => false

end Token

/-- A token with its span. -/
structure Lexeme where
  tok  : Token
  span : Span
  deriving Repr, Inhabited

end Koit.Syntax
