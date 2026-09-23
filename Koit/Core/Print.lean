import Koit.Core.Syntax

/-!
Printing Core in its own notation, for
`koitc desugar`. The output is for reading, not for parsing back:
`try x = F then { ... } else { ... }`, `rd p`, `raise k e`, `hold R x
= acquire R f(a...)`, `loop n { ... }`, with one statement per line.
Expressions are fully parenthesized below the top level of each
operator, so precedence never has to be inferred.
-/

namespace Koit.Core

def Kind.print (k : Kind) : String := k.spelling
def Resource.print (r : Resource) : String := r.spelling

/-- Two hex digits, for character literals outside printable ASCII. -/
private def hex2 (b : UInt8) : String :=
  let ds := Nat.toDigits 16 b.toNat
  String.ofList (if ds.length < 2 then '0' :: ds else ds)

def charLit (c : UInt8) : String :=
  let body :=
    if c == '\n'.toUInt8 then "\\n"
    else if c == '\r'.toUInt8 then "\\r"
    else if c == '\t'.toUInt8 then "\\t"
    else if c == 0 then "\\0"
    else if c == '\\'.toUInt8 then "\\\\"
    else if c == '\''.toUInt8 then "\\'"
    else if 32 ≤ c && c < 127 then (Char.ofNat c.toNat).toString
    else "\\x" ++ hex2 c
  "'" ++ body ++ "'"

def strLit (s : String) : String :=
  let body := s.foldl (init := "") fun acc c =>
    acc ++
      if c == '"' then "\\\""
      else if c == '\\' then "\\\\"
      else if c == '\n' then "\\n"
      else if c == '\r' then "\\r"
      else if c == '\t' then "\\t"
      else if c.toNat < 32 then "\\x" ++ hex2 c.toNat.toUInt8
      else c.toString
  "\"" ++ body ++ "\""

mutual

partial def Ty.print : Ty → String
  | .int _ signed w => (if signed then "i" else "u") ++ toString w
  | .be _ w => "be" ++ toString w
  | .bool _ => "bool"
  | .slot _ n => n
  | .enum _ n => n
  | .named _ n => n
  | .struct _ [] => "{ }"
  | .struct _ fields =>
    "{ " ++ ", ".intercalate (fields.map Field.print) ++ " }"
  | .array _ t n => t.print ++ "[" ++ n.print ++ "]"
  | .ref _ t => "ref " ++ t.print
  | .view _ t => "view " ++ t.print
  | .own _ t => "own " ++ t.print
  | .refined _ v t p =>
    "{ " ++ v ++ ": " ++ t.print ++ " | " ++ p.print ++ " }"
  | .opt _ t => t.print ++ "?"

partial def Field.print : Field → String
  | .mk _ n t none => n ++ ": " ++ t.print
  | .mk _ n t (some p) => n ++ ": " ++ t.print ++ " where " ++ p.print

/-- An operand: atoms print bare, anything else in parentheses. -/
partial def Expr.operand (e : Expr) : String :=
  match e with
  | .lit .. | .char .. | .bool .. | .str .. | .var .. | .read .. | .size ..
  | .call .. | .errno .. | .invalid .. => e.print
  | _ => "(" ++ e.print ++ ")"

partial def Expr.print : Expr → String
  | .lit _ _ t => t
  | .char _ c => charLit c
  | .bool _ b => if b then "true" else "false"
  | .str _ s => strLit s
  | .var _ n => n
  | .arith _ op l r => l.operand ++ " " ++ op.spelling ++ " " ++ r.operand
  | .cmp _ op l r => l.operand ++ " " ++ op.spelling ++ " " ++ r.operand
  | .not _ e => "!" ++ e.operand
  | .and _ l r => l.operand ++ " && " ++ r.operand
  | .or _ l r => l.operand ++ " || " ++ r.operand
  | .cast _ e t => e.operand ++ " as " ++ t.print
  | .hton _ e => "hton " ++ e.operand
  | .ntoh _ e => "ntoh " ++ e.operand
  | .read _ p => "rd " ++ p.print
  | .size _ t => "size " ++ t.print
  | .move _ n => "move " ++ n
  | .call _ f args => "call " ++ f ++ "(" ++ Arg.printList args ++ ")"
  | .errno _ => "errno"
  | .invalid _ m => "invalid " ++ strLit m

partial def Place.print : Place → String
  | .var _ n => n
  | .field _ p f => p.print ++ "." ++ f
  | .index _ p i => p.print ++ "[" ++ i.print ++ "]"
  | .slot _ m i => m ++ "[" ++ i.print ++ "]"
  | .deref _ e => "*" ++ e.operand
  | .invalid _ m => "invalid " ++ strLit m

partial def Arg.print : Arg → String
  | .val e => e.print
  | .place p => p.print
  | .map _ m => m

partial def Arg.printList (args : List Arg) : String :=
  ", ".intercalate (args.map Arg.print)

partial def Fallible.print : Fallible → String
  | .view _ off t => "view(" ++ off.print ++ ", " ++ t.print ++ ")"
  | .lookup _ m k => "lookup(" ++ m ++ ", " ++ k.print ++ ")"
  | .loadw _ p => "loadw(" ++ p.print ++ ")"
  | .call _ f args => "call " ++ f ++ "(" ++ Arg.printList args ++ ")"
  | .acquire _ r f ty args =>
    "acquire " ++ r.print ++ " " ++ f ++
      (match ty with | some t => "<" ++ t.print ++ ">" | none => "") ++
      "(" ++ Arg.printList args ++ ")"
  | .callopt _ f args => "callopt " ++ f ++ "(" ++ Arg.printList args ++ ")"
  | .tail _ m i => "tail " ++ m ++ "[" ++ i.print ++ "]"
  | .coerce _ e t => "coerce(" ++ e.print ++ ", " ++ t.print ++ ")"

end

def Init.print : Init → String
  | .expr e => e.print
  | .place p => p.print
  | .lit _ fields =>
    "{ " ++ ", ".intercalate (fields.map fun f => f.name ++ ": " ++
      f.value.print) ++ " }"

def pad (n : Nat) : String := String.ofList (List.replicate n ' ')

mutual

/-- A statement without its own indentation; nested blocks close at
column `ind`. -/
partial def Stmt.print (s : Stmt) (ind : Nat) : String :=
  match s with
  | .«let» _ mutable x ty init =>
    (if mutable then "var " else "let ") ++ x ++
      (match ty with | some t => " : " ++ t.print | none => "") ++
      " = " ++ init.print
  | .assign _ p e => p.print ++ " := " ++ e.print
  | .ite _ c t [] => "if " ++ c.print ++ " then " ++ Stmt.printBlock t ind
  | .ite _ c t e =>
    "if " ++ c.print ++ " then " ++ Stmt.printBlock t ind ++ " else " ++
      Stmt.printBlock e ind
  | .loop _ n body => "loop " ++ n.operand ++ " " ++ Stmt.printBlock body ind
  | .«for» _ x lo hi body =>
    "for " ++ x ++ " in " ++ lo.operand ++ ".." ++ hi.operand ++ " " ++
      Stmt.printBlock body ind
  | .brk _ => "break"
  | .cont _ => "continue"
  | .ret _ none => "return"
  | .ret _ (some e) => "return " ++ e.print
  | .raise _ k e => "raise " ++ k.print ++ " " ++ e.operand
  | .«try» _ x f thn els _ =>
    "try " ++ x ++ " = " ++ f.print ++ " then " ++ Stmt.printBlock thn ind ++
      " else " ++ Stmt.printBlock els ind
  | .hold _ r x acq body els =>
    "hold " ++ r.print ++ " " ++ (match x with | some n => n | none => "_") ++
      " = " ++ acq.print ++
      (match els with
       | some e =>
         " then " ++ Stmt.printBlock body ind ++ " else " ++
           Stmt.printBlock e ind
       | none => " " ++ Stmt.printBlock body ind)
  | .atomic _ x op p args =>
    (match x with | some n => "let " ++ n ++ " = " | none => "") ++
      op.spelling ++ "(" ++ ", ".intercalate (p.print :: args.map Expr.print)
      ++ ")"
  | .invalid _ m => "invalid " ++ strLit m

/-- `{` ... `}` with the statements at `ind + 2`. -/
partial def Stmt.printBlock (ss : List Stmt) (ind : Nat) : String :=
  match ss with
  | [] => "{ }"
  | _ =>
    let lines := ss.map fun s => pad (ind + 2) ++ s.print (ind + 2)
    "{\n" ++ "\n".intercalate lines ++ "\n" ++ pad ind ++ "}"

end

def Param.print (p : Param) : String :=
  p.name ++ ": " ++ p.ty.print ++
    (match p.pred with | some q => " where " ++ q.print | none => "")

def Fn.print (f : Fn) : String :=
  "fn " ++ f.name ++ "(" ++ ", ".intercalate (f.params.map Param.print) ++
    ")" ++ (match f.ret with | some t => " -> " ++ t.print | none => "") ++
    (if f.fails then " fails" else "") ++ " " ++ Stmt.printBlock f.body 0

def MapKind.print : MapKind → String
  | .array n v => "array[" ++ n.print ++ "] of " ++ v.print
  | .percpu n v => "percpu_array[" ++ n.print ++ "] of " ++ v.print
  | .hash n k v =>
    "hash[" ++ n.print ++ "] of " ++ k.print ++ " -> " ++ v.print
  | .ringbuf n => "ringbuf[" ++ n.print ++ "]"
  | .progArray n k => "prog_array[" ++ n.print ++ "] of " ++ k

def Region.print : Region → String
  | .pkt _ none => "pkt"
  | .pkt _ (some (lo, hi)) =>
    "pkt[" ++ lo.print ++ " .. " ++ hi.print ++ ")"
  | .map _ n => n
  | .mapsExcept _ [] => "maps"
  | .mapsExcept _ names => "maps except " ++ ", ".intercalate names
  | .ctx _ f => "ctx." ++ f

/-- The clauses `S` and `W`, one per line at indentation 2. -/
def printClauses (verdicts : Option (List (Span × String)))
    (preserved : List Region) : List String :=
  (match verdicts with
   | some vs => ["  verdicts { " ++ ", ".intercalate (vs.map (·.2)) ++ " }"]
   | none => []) ++
  preserved.map fun r => "  preserve " ++ r.print

def Contract.print (c : Contract) : String :=
  "contract " ++ c.name ++ " : " ++ c.kind ++ "\n" ++
    "\n".intercalate (printClauses c.verdicts c.preserved)

def Handler.print (h : Handler) : String :=
  "  on " ++ h.kind.print ++ " " ++ Stmt.printBlock h.body 2

def Program.print (p : Program) : String :=
  "program " ++ p.name ++ " : " ++ p.kind ++
    (match p.implements with
     | some (_, c) => " implements " ++ c
     | none => "") ++ "\n" ++
    "\n".intercalate (printClauses p.verdicts p.preserved ++
      p.handlers.map Handler.print) ++ "\n" ++
    Stmt.printBlock p.body 0

def TypeDecl.print (d : TypeDecl) : String :=
  "type " ++ d.name ++ " = " ++ d.ty.print

def ConstDecl.print (d : ConstDecl) : String :=
  "const " ++ d.name ++
    (match d.ty with | some t => " : " ++ t.print | none => "") ++
    " = " ++ d.value.print

def ConfigDecl.print (d : ConfigDecl) : String :=
  "config " ++ d.name ++ " : " ++ d.ty.print ++
    (match d.init with | some e => " = " ++ e.print | none => "")

def MapDecl.print (d : MapDecl) : String :=
  "map " ++ d.name ++ " : " ++ d.kind.print ++ d.access.print ++
    (if d.init.isEmpty then "" else
      " = [" ++ ", ".intercalate (d.init.map Expr.print) ++ "]")

/-- Declarations in the order of a unit's template (constants and
types, maps, functions, entry points), separated by blank
lines, ending in a newline. -/
def CompUnit.print (u : CompUnit) : String :=
  let items :=
    (match u.license with
     | some (_, s) => ["license " ++ strLit s]
     | none => []) ++
    u.consts.map ConstDecl.print ++
    u.configs.map ConfigDecl.print ++
    u.types.map TypeDecl.print ++
    u.maps.map MapDecl.print ++
    u.fns.map Fn.print ++
    u.contracts.map Contract.print ++
    u.programs.map Program.print
  "\n\n".intercalate items ++ "\n"

end Koit.Core
