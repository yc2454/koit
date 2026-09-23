import Koit.Core.Syntax
import Koit.Core.Print
import Koit.Interface.Decls
import Koit.Facts.Entail
import Koit.Effects.Held
import Koit.Check.Diag

/-!
The typing environments: `G` as `Env`, with the unit's declarations,
the interface, the program kind, and the locals in scope; `K` as `Ctx`,
with what the statement rules read from it (whether the context may
fail, whether inside a loop, what `return` returns to), the facts `F`
on the current path, the program's preserved regions, which every
statement's effects are checked against, and the held set `H`. The
operations on types are in `Types.lean`.
-/

namespace Koit.Check

open Koit (Span)
open Koit.Core
open Koit.Interface (KindDecl)
open Koit.Facts (Origin Facts)
open Koit.Effects (Effs Held)

/-- A name in scope: a scalar value, or a place named by a binding,
whose type is then `ref T`, `view T`, or `own T`. -/
structure Local where
  name    : String
  ty      : Ty
  mutable : Bool
  origin  : Origin
  deriving Repr, Inhabited

/-- The typing environment `G`. Lookup order for a name is locals, the unit's
declarations, the verdicts of the program kind, then the interface. -/
structure Env where
  interface   : Interface
  license   : Option String
  types     : List TypeDecl
  consts    : List ConstDecl
  configs   : List ConfigDecl
  maps      : List MapDecl
  fns       : List Fn
  contracts : List Contract
  /-- The program kind, inside a program body or handler. -/
  kind      : Option KindDecl := none
  locals    : List Local := []
  /-- Untyped constants being expanded, to reject a cycle. -/
  visiting  : List String := []
  /-- The effect summary of each function checked so far, stated over
  its parameters; callees are checked before their callers. -/
  fnEffects : List (String × Effs) := []
  /-- Trace each accepted entailment as a solver query, for the
  testing cross-check. -/
  smt       : Bool := false
  deriving Inhabited

namespace Env

def type? (env : Env) (n : String) : Option TypeDecl :=
  -- `verdict` is the alias for the enclosing program's kind's verdict
  -- type; a function has no kind and names the declaration instead.
  if n == "verdict" then
    env.kind.map fun decl =>
      { span := decl.verdictTy.span, name := "verdict", ty := decl.verdictTy }
  else env.types.find? (·.name == n) <|> env.interface.type? n

def const? (env : Env) (n : String) : Option ConstDecl :=
  env.consts.find? (·.name == n) <|> env.interface.const? n

def config? (env : Env) (n : String) : Option ConfigDecl :=
  env.configs.find? (·.name == n)

def map? (env : Env) (n : String) : Option MapDecl :=
  env.maps.find? (·.name == n)

def fn? (env : Env) (n : String) : Option Fn :=
  env.fns.find? (·.name == n)

def local? (env : Env) (n : String) : Option Local :=
  env.locals.find? (·.name == n)

/-- The verdict `n` of the current kind, with its type. -/
def verdict? (env : Env) (n : String) : Option Ty :=
  env.kind.bind fun decl =>
    if decl.verdicts.any (·.1 == n) then some decl.verdictTy else none

def bind (env : Env) (l : Local) : Env := { env with locals := l :: env.locals }

def bindAll (env : Env) (ls : List Local) : Env :=
  { env with locals := ls ++ env.locals }

/-- The environment of a declaration: no locals, no kind. -/
def top (env : Env) : Env := { env with locals := [], kind := none }

/-- Whether the unit's license admits GPL-only kernel functions, per
the kernel's `license_is_gpl_compatible`. -/
def gplCompatible (env : Env) : Bool :=
  match env.license with
  | some s => ["GPL", "GPL v2", "GPL and additional rights", "Dual BSD/GPL",
               "Dual MIT/GPL", "Dual MPL/GPL"].contains s
  | none => false

end Env

/-- What `return` returns to. -/
inductive RetCtx where
  | program (ty : Ty)
  | handler (ty : Ty)
  | fn (name : String) (ret : Option Ty)
  deriving Inhabited

/-- The context `K` of the statement rules, the base half. -/
structure Ctx where
  mayFail   : Bool
  inLoop    : Bool := false
  ret       : RetCtx
  inHandler : Bool := false
  /-- The name of the function under check, for messages. -/
  fnName    : Option String := none
  /-- Inside the `else` of a `try` on a helper call, where `errno` is
  the reason. -/
  errnoOk   : Bool := false
  /-- The program's verdict set `S`, when it has one. -/
  verdictSet : Option (List String) := none
  /-- The facts on the current path. -/
  facts : Facts := {}
  /-- The preserved regions of the enclosing program, `W`. -/
  preserved : List Region := []
  /-- The resources held by the enclosing `hold` blocks, innermost
  first. -/
  held : Held := []
  /-- The owned names moved at the head of the innermost loop, which a
  path back to the head or out of the loop must not have added to. -/
  loopMoved : List String := []
  /-- The names in scope derived from another, each with the name it
  derives from: a socket cast under its socket. The parent cannot be
  moved while one is in scope. -/
  derived : List (String × String) := []
  deriving Inhabited

end Koit.Check
