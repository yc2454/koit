import Koit.Syntax.AST

/-!
Printing the surface AST back as source, for `koitc print` and the
round-trip test: printing, parsing, and printing again must give the
same text. Comments are not in the tree and are not reproduced.

Expressions print with the parentheses the source had and with any
further parentheses the precedence table needs, so a tree built by
hand prints correctly too. Blocks print one statement per line.
-/

namespace Koit.Syntax

def UnOp.spelling : UnOp → String
  | .not => "!" | .neg => "-" | .deref => "*"

def BinOp.spelling : BinOp → String
  | .mul => "*" | .div => "/" | .mod => "%" | .add => "+" | .sub => "-"
  | .shl => "<<" | .shr => ">>" | .band => "&" | .bxor => "^" | .bor => "|"
  | .eq => "==" | .ne => "!=" | .lt => "<" | .le => "<=" | .gt => ">"
  | .ge => ">=" | .land => "&&" | .lor => "||"

/-- Section 5, tightest first: `* / %` 9, `+ -` 8, shifts 7, `&` 6,
`^` 5, `|` 4, comparisons 3, `&&` 2, `||` 1. Casts are 10, unary 11,
postfix and atoms 12. -/
def BinOp.prec : BinOp → Nat
  | .mul | .div | .mod => 9
  | .add | .sub => 8
  | .shl | .shr => 7
  | .band => 6
  | .bxor => 5
  | .bor => 4
  | .eq | .ne | .lt | .le | .gt | .ge => 3
  | .land => 2
  | .lor => 1

def AssignOp.spelling : AssignOp → String
  | .set => "=" | .add => "+=" | .sub => "-=" | .mul => "*="
  | .band => "&=" | .bor => "|=" | .bxor => "^=" | .shl => "<<="
  | .shr => ">>="

def Verdict.spelling : Verdict → String
  | .pass => "pass" | .drop => "drop" | .tx => "tx" | .abort => "abort"

/-- Two hex digits. -/
def hex2 (b : UInt8) : String :=
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

def Expr.prec : Expr → Nat
  | .binary _ op .. => op.prec
  | .cast .. => 10
  | .unary .. | .move .. => 11
  | _ => 12

def Pattern.print : Pattern → String
  | .one _ n => n
  | .pair _ k v => s!"({k}, {v})"

mutual

partial def Ty.print : Ty → String
  | .int _ signed w => (if signed then "i" else "u") ++ toString w
  | .be _ w => "be" ++ toString w
  | .bool _ => "bool"
  | .spinlock _ => "spinlock"
  | .named _ n => n
  | .struct _ fields =>
    "{ " ++ ", ".intercalate (fields.map Field.print) ++ " }"
  | .refined _ v t p => "{ " ++ v ++ ": " ++ t.print ++ " | " ++ p.print ++ " }"
  | .array _ t n => t.print ++ "[" ++ n.print ++ "]"
  | .ref _ t => "ref " ++ t.print
  | .view _ t => "view " ++ t.print
  | .opt _ t => t.print ++ "?"
  | .own _ t => "own " ++ t.print

partial def Field.print : Field → String
  | .mk _ n t none => n ++ ": " ++ t.print
  | .mk _ n t (some p) => n ++ ": " ++ t.print ++ " where " ++ p.print

/-- Prints `e`, parenthesized when its precedence is below `min`. -/
partial def Expr.print (e : Expr) (min : Nat := 0) : String :=
  let s :=
    match e with
    | .int _ _ t => t
    | .char _ c => charLit c
    | .str _ s => strLit s
    | .bool _ b => if b then "true" else "false"
    | .var _ n => n
    | .paren _ e => "(" ++ e.print ++ ")"
    | .unary _ op e => op.spelling ++ e.print 11
    | .move _ n => "move " ++ n
    | .binary _ op l r =>
      let q := op.prec
      -- comparisons do not associate, so both sides bind tighter
      let lmin := if q == 3 then q + 1 else q
      l.print lmin ++ " " ++ op.spelling ++ " " ++ r.print (q + 1)
    | .cast _ e t => e.print 11 ++ " as " ++ t.print
    | .field _ e n => e.print 12 ++ "." ++ n
    | .index _ e i => e.print 12 ++ "[" ++ i.print ++ "]"
    | .call _ f args =>
      f.print 12 ++ "(" ++ ", ".intercalate (args.map (·.print)) ++ ")"
    | .tcall _ r n t args =>
      r.print 12 ++ "." ++ n ++ "<" ++ t.print ++ ">(" ++
        ", ".intercalate (args.map (·.print)) ++ ")"
    | .structLit _ fs =>
      "{ " ++ ", ".intercalate (fs.map FieldInit.print) ++ " }"
  if e.prec < min then "(" ++ s ++ ")" else s

partial def FieldInit.print : FieldInit → String
  | .mk _ n v => n ++ ": " ++ v.print

end

def pad (n : Nat) : String := String.ofList (List.replicate n ' ')

mutual

/-- A statement, without its own indentation; nested blocks close at
column `ind`. -/
partial def Stmt.print (s : Stmt) (ind : Nat) : String :=
  match s with
  | .decl _ mutable name ty pred init tail =>
    (if mutable then "var " else "let ") ++ name ++
      (match ty with | some t => ": " ++ t.print | none => "") ++
      (match pred with | some p => " where " ++ p.print | none => "") ++
      " = " ++ init.print ++ Tail.printOpt tail ind
  | .assign _ t op v => t.print ++ " " ++ op.spelling ++ " " ++ v.print
  | .ite _ c thn els =>
    "if " ++ c.print ++ " " ++ thn.print ind ++ Block.printElse els ind
  | .iteLet _ n init thn els =>
    "if let " ++ n ++ " = " ++ init.print ++ " " ++ thn.print ind ++
      Block.printElse els ind
  | .loop _ n body => "repeat " ++ n.print ++ " " ++ body.print ind
  | .forRange _ v lo hi body =>
    "for " ++ v ++ " in " ++ lo.print ++ ".." ++ hi.print ++ " " ++
      body.print ind
  | .forIter _ pat it bound marked body =>
    "for " ++ pat.print ++ " in " ++ it.print ++ " bounded " ++
      bound.print ++ (if marked then "?" else "") ++ " " ++ body.print ind
  | .hold _ name acq tail body =>
    "hold " ++ (match name with | some n => n ++ " = " | none => "") ++
      acq.print ++ Tail.printOpt tail ind ++ " " ++ body.print ind
  | .check _ c tail => "check " ++ c.print ++ Tail.printOpt tail ind
  | .expr _ e tail => e.print ++ Tail.printOpt tail ind
  | .brk _ => "break"
  | .cont _ => "continue"
  | .ret _ none => "return"
  | .ret _ (some v) => "return " ++ v.print
  | .verdict _ v => v.spelling
  | .fail _ none => "fail"
  | .fail _ (some r) => "fail " ++ r.print

partial def Tail.printOpt (t : Option Tail) (ind : Nat) : String :=
  match t with
  | none => ""
  | some (.mark _) => "?"
  | some (.elseBlock _ b) => " else " ++ b.print ind
  | some (.elseExit _ s) => " else " ++ s.print ind

/-- The else part of an `if`; a block holding one `if` prints as
`else if`. -/
partial def Block.printElse (els : Option Block) (ind : Nat) : String :=
  match els with
  | none => ""
  | some (.mk _ [s@(.ite ..)]) => " else " ++ s.print ind
  | some b => " else " ++ b.print ind

/-- `{` ... `}` with the statements at `ind + 2`. -/
partial def Block.print (b : Block) (ind : Nat) : String :=
  match b.stmts with
  | [] => "{ }"
  | ss =>
    let lines := ss.map fun s => pad (ind + 2) ++ s.print (ind + 2)
    "{\n" ++ "\n".intercalate lines ++ "\n" ++ pad ind ++ "}"

end

def Param.print (p : Param) : String :=
  p.name ++ ": " ++ p.ty.print ++
    (match p.pred with | some q => " where " ++ q.print | none => "")

def RetType.print : RetType → String
  | .ty t => t.print
  | .refined _ n t p => n ++ ": " ++ t.print ++ " where " ++ p.print

def MapType.print : MapType → String
  | .array _ n v => "array[" ++ n.print ++ "] of " ++ v.print
  | .percpuArray _ n v => "percpu_array[" ++ n.print ++ "] of " ++ v.print
  | .hash _ n k v =>
    "hash[" ++ n.print ++ "] of " ++ k.print ++ " -> " ++ v.print
  | .ringbuf _ n => "ringbuf[" ++ n.print ++ "]"

def Region.print : Region → String
  | .pkt _ none => "pkt"
  | .pkt _ (some (lo, hi)) => "pkt[" ++ lo.print ++ " .. " ++ hi.print ++ ")"
  | .maps _ [] => "maps"
  | .maps _ names => "maps except " ++ ", ".intercalate names
  | .map _ n => n
  | .ctxField _ f => "ctx." ++ f

def Clause.print : Clause → String
  | .verdicts _ names => "verdict in { " ++ ", ".intercalate names ++ " }"
  | .preserve _ regions =>
    "preserve " ++ ", ".intercalate (regions.map Region.print)

def Handler.print (h : Handler) : String :=
  "on " ++ (match h.kinds with
    | none => "_"
    | some ks => ", ".intercalate ks) ++ " " ++ h.body.print 2

def FnDecl.print (d : FnDecl) : String :=
  "fn " ++ d.name ++ "(" ++ ", ".intercalate (d.params.map Param.print) ++
    ")" ++ (match d.ret with | some r => " -> " ++ r.print | none => "") ++
    (if d.fails then " fails" else "") ++ " " ++ d.body.print 0

def Contract.print (c : Contract) : String :=
  "contract " ++ c.name ++ " : " ++ c.kind ++ " {\n" ++
    "\n".intercalate (c.clauses.map fun cl => "  " ++ cl.print) ++ "\n}"

/-- The header on one line when it has no clauses, handlers, or
`fail`; otherwise one header part per line and the body's `{` on its
own line, as the examples write it. -/
def Program.print (p : Program) : String :=
  let head := "program " ++ p.name ++ " : " ++ p.kind ++
    (match p.implements with | some c => " implements " ++ c | none => "")
  let parts :=
    p.clauses.map Clause.print ++
    (match p.failExit with | some s => ["fail " ++ s.print 2] | none => []) ++
    p.handlers.map Handler.print
  match parts with
  | [] => head ++ " " ++ p.body.print 0
  | _ =>
    head ++ "\n" ++ "\n".intercalate (parts.map ("  " ++ ·)) ++ "\n" ++
      p.body.print 0

def Item.print : Item → String
  | .const _ n none v => "const " ++ n ++ " = " ++ v.print
  | .const _ n (some t) v =>
    "const " ++ n ++ " : " ++ t.print ++ " = " ++ v.print
  | .config _ n t none => "config " ++ n ++ " : " ++ t.print
  | .config _ n t (some v) =>
    "config " ++ n ++ " : " ++ t.print ++ " = " ++ v.print
  | .type _ n t => "type " ++ n ++ " = " ++ t.print
  | .map _ n mt => "map " ++ n ++ " : " ++ mt.print
  | .fn d => d.print
  | .contract c => c.print
  | .program p => p.print

/-- Items separated by blank lines, ending in a newline. -/
def CompUnit.print (u : CompUnit) : String :=
  let items := u.items.map Item.print
  let all := match u.license with
    | some (_, s) => ("license " ++ strLit s) :: items
    | none => items
  "\n\n".intercalate all ++ "\n"

end Koit.Syntax
