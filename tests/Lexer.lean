import Koit.Syntax.Lexer

/-!
Checks on the lexer over small inputs. They run when this module is
built, so `lake build` fails if one is wrong. The corpus under
`tests/` is the other half: every file there must lex.
-/

open Koit Koit.Syntax

/-- The tokens of `s`, or `none` on a lexical error. -/
def toks (s : String) : Option (List Token) :=
  match lex s with
  | .ok ls => some (ls.toList.map (·.tok))
  | .error _ => none

/-- Where `s` fails to lex, as `(line, col)`, or `none`. -/
def errAt (s : String) : Option (Nat × Nat) :=
  match lex s with
  | .ok _ => none
  | .error e => some (e.pos.line, e.pos.col)

-- keywords, identifiers, and the final terminator
#guard toks "let x = 1" ==
  some [.keyword .«let», .ident "x", .punct .assign, .int 1 "1",
        .newline, .eof]
#guard toks "" == some [.eof]
#guard toks "_ as_ hold_x" ==
  some [.ident "_", .ident "as_", .ident "hold_x", .newline, .eof]

-- integer literals keep their text
#guard toks "0x1F_FF 0b1010 1_000 0" ==
  some [.int 8191 "0x1F_FF", .int 10 "0b1010", .int 1000 "1_000",
        .int 0 "0", .newline, .eof]
#guard toks "0..6" ==
  some [.int 0 "0", .punct .dotdot, .int 6 "6", .newline, .eof]

-- character and string literals
#guard toks "'a' '\\n' '\\x20' '\\'' ' '" ==
  some [.char 97, .char 10, .char 32, .char 39, .char 32, .newline, .eof]
#guard toks "\"GPL\" \"n = {}\\n\"" ==
  some [.string "GPL", .string "n = {}\n", .newline, .eof]

-- punctuation by longest match
#guard toks "a <<= b >> c -> d != !e && f || g" ==
  some [.ident "a", .punct .shlAssign, .ident "b", .punct .shr,
        .ident "c", .punct .arrow, .ident "d", .punct .bangEq,
        .punct .bang, .ident "e", .punct .ampAmp, .ident "f",
        .punct .pipePipe, .ident "g", .newline, .eof]
#guard toks "pkt.view<u8[4]>(off)?" ==
  some [.ident "pkt", .punct .dot, .keyword .«view», .punct .lt,
        .ident "u8", .punct .lbrack, .int 4 "4", .punct .rbrack,
        .punct .gt, .punct .lparen, .ident "off", .punct .rparen,
        .punct .question, .newline, .eof]

-- the newline rule: blank lines collapse, continuations skip
#guard toks "a\n\n\nb" ==
  some [.ident "a", .newline, .ident "b", .newline, .eof]
#guard toks "a,\nb" ==
  some [.ident "a", .punct .comma, .ident "b", .newline, .eof]
#guard toks "x =\n 1" ==
  some [.ident "x", .punct .assign, .int 1 "1", .newline, .eof]
#guard toks "array[1] of\n T" ==
  some [.ident "array", .punct .lbrack, .int 1 "1", .punct .rbrack,
        .keyword .«of», .ident "T", .newline, .eof]
#guard toks "f(\n a\n)" ==
  some [.ident "f", .punct .lparen, .ident "a", .newline, .punct .rparen,
        .newline, .eof]
#guard toks "x?\ny" ==
  some [.ident "x", .punct .question, .newline, .ident "y", .newline, .eof]
#guard toks "a +\n b" ==
  some [.ident "a", .punct .plus, .ident "b", .newline, .eof]

-- comments
#guard toks "a // c\nb" ==
  some [.ident "a", .newline, .ident "b", .newline, .eof]
#guard toks "a /* x */ b" == some [.ident "a", .ident "b", .newline, .eof]
#guard toks "a /* x\n y */ b" ==
  some [.ident "a", .newline, .ident "b", .newline, .eof]
#guard toks "/* é */ a" == some [.ident "a", .newline, .eof]

-- positions: 1-based line and column, columns count characters
/-- The `(line, col)` of each token, or `none` on an error. -/
def starts (s : String) : Option (Array (Nat × Nat)) :=
  (lex s).toOption.map (·.map fun l => (l.span.start.line, l.span.start.col))

#guard starts "ab\n  cd" == some #[(1, 1), (1, 3), (2, 3), (2, 5), (2, 5)]
#guard (lex "/* é */a").toOption.map (·[0]!.span.start.col) == some 8

-- errors, at the position a message would name
#guard errAt "0x" == some (1, 1)
#guard errAt "0b12" == some (1, 4)
#guard errAt "1abc" == some (1, 2)
#guard errAt "1_" == none
#guard errAt "''" == some (1, 1)
#guard errAt "'ab'" == some (1, 3)
#guard errAt "'\\q'" == some (1, 3)
#guard errAt "'\\x2'" == some (1, 5)
#guard errAt "'é'" == some (1, 1)
#guard errAt "\"abc" == some (1, 1)
#guard errAt "\"a\nb\"" == some (1, 1)
#guard errAt "/* x" == some (1, 1)
#guard errAt "@" == some (1, 1)
#guard errAt "a\n  §" == some (2, 3)
