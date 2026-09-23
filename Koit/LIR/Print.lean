import Koit.LIR.Syntax

/-!
The LIR printer, behind `koitc lower`: one line per statement, blocks
indented, every literal and operator with its width, so that the
text is the language of `lir.md` section 3.
-/

namespace Koit.LIR

open Koit (Span)
open Koit.Core (ArithOp CmpOp AtomicOp Kind Resource)

def Kind.print (k : Kind) : String := k.spelling

mutual

partial def Expr.print : Expr → String
  | .lit w k => s!"{k}({w})"
  | .var x => x
  | .arith op s w l r =>
    s!"{l.operand} {op.spelling}({Ty.print (.int s w)}) {r.operand}"
  | .cast s w s' w' e =>
    s!"cast({Ty.print (.int s w)} -> {Ty.print (.int s' w')}) {e.operand}"
  | .bswap w e => s!"bswap({w}) {e.operand}"
  | .load s w a => s!"load({Ty.print (.int s w)}) {a.operand}"
  | .ctx f => s!"ctx {f}"
  | .addr a => a.print

partial def Expr.operand (e : Expr) : String :=
  match e with
  | .lit .. | .var .. => e.print
  | .addr a => a.operand
  | _ => "(" ++ e.print ++ ")"

partial def Addr.print : Addr → String
  | .var x => x
  | .plus a k => s!"{a.operand} + {k}"
  | .index a e k => s!"{a.operand} + {e.operand} * {k}"
  | .pktData => "pkt_data"
  | .pktEnd => "pkt_end"
  | .mapval m k => s!"mapval {m} + {k}"

partial def Addr.operand (a : Addr) : String :=
  match a with
  | .var .. | .pktData | .pktEnd => a.print
  | _ => "(" ++ a.print ++ ")"

end

def Cond.print (c : Cond) : String :=
  s!"{c.l.operand} {c.op.spelling}({Ty.print (.int c.signed c.w)}) {c.r.operand}"

def Builtin.print : Builtin → String
  | .lookup m => s!"lookup {m}"
  | .update m => s!"update {m}"
  | .delete m => s!"delete {m}"
  | .reserve m n => s!"reserve {m} {n}"
  | .submit => "submit"
  | .discard => "discard"
  | .lock => "lock"
  | .unlock => "unlock"
  | .enter r => s!"enter {r}"
  | .leave r => s!"leave {r}"
  | .copy n => s!"copy {n}"
  | .fill n => s!"fill {n}"
  | .printk fmt => s!"printk {Core.strLit fmt}"
  | .tail m => s!"tail {m}"
  | .atomic op s w fetch =>
    s!"atomic {(op.spelling.drop 7).toString}({Ty.print (.int s w)})" ++
      (if fetch then " fetch" else "")

def pad (n : Nat) : String := String.ofList (List.replicate n ' ')

def printArgs (args : List Expr) : String :=
  "(" ++ ", ".intercalate (args.map Expr.print) ++ ")"

mutual

partial def Stmt.print (s : Stmt) (ind : Nat) : String :=
  match s with
  | .«let» _ x t e => s!"let {x} : {t.print} = {e.print}"
  | .assign _ x e => s!"{x} := {e.print}"
  | .store _ w a e => s!"store({w}) {a.operand} <- {e.print}"
  | .ctxStore _ f e => s!"ctx {f} <- {e.print}"
  | .frame _ x n src =>
    s!"frame {x} : {n}" ++ (match src with
      | some t => s!" as {t.print}"
      | none => "")
  | .ite _ c t [] => s!"if {c.print} {Stmt.printBlock t ind}"
  | .ite _ c t e =>
    s!"if {c.print} {Stmt.printBlock t ind} else {Stmt.printBlock e ind}"
  | .block _ body => s!"block {Stmt.printBlock body ind}"
  | .loop _ body => s!"loop {Stmt.printBlock body ind}"
  | .br _ n => s!"br {n}"
  | .ret _ none => "return"
  | .ret _ (some e) => s!"return {e.print}"
  | .raise _ k e => s!"raise {k.print} {e.operand}"
  | .call _ x f args u a =>
    (match x with | some x => s!"{x} = " | none => "") ++
      s!"call {f}{printArgs args}" ++
      (match u with
       | some u => s!" unwind {Stmt.printBlock u ind}"
       | none => "") ++
      (match a with
       | some a => s!" absent {Stmt.printBlock a ind}"
       | none => "")
  | .builtin _ x b args =>
    (match x with | some x => s!"{x} = " | none => "") ++
      s!"{b.print}{printArgs args}"
  | .kernel _ x h args =>
    (match x with | some x => s!"{x} = " | none => "") ++
      s!"{h}{printArgs args}"

partial def Stmt.printBlock (ss : List Stmt) (ind : Nat) : String :=
  match ss with
  | [] => "{ }"
  | _ =>
    let lines := ss.map fun s => pad (ind + 2) ++ s.print (ind + 2)
    "{\n" ++ "\n".intercalate lines ++ "\n" ++ pad ind ++ "}"

end

def Fn.print (f : Fn) : String :=
  s!"fn {f.name}(" ++
    ", ".intercalate (f.params.map fun p => s!"{p.name} : {p.ty.print}") ++
    ")" ++ (match f.ret with
      | some t => s!" -> {t.print}" ++ (if f.opt then " ?" else "")
      | none => if f.opt then " -> ?" else "") ++
    (if f.fails then " fails" else "") ++ " " ++ Stmt.printBlock f.body 0

def Program.print (p : Program) : String :=
  s!"program {p.name} : {p.kind} " ++ Stmt.printBlock p.body 0 ++
    String.join (p.handlers.map fun h =>
      s!"\non {h.kind.print} => " ++ Stmt.printBlock h.body 0)

def CompUnit.print (u : CompUnit) : String :=
  let items :=
    u.types.map Core.TypeDecl.print ++
    u.maps.map (fun d => d.print ++
      (if u.direct.contains d.name then " direct" else "")) ++
    u.fns.map Fn.print ++
    u.programs.map Program.print
  "\n\n".intercalate items ++ "\n"

end Koit.LIR
