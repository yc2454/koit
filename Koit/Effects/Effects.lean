import Koit.Core.Syntax
import Koit.Core.Print

/-!
The effect set `E` of a statement or a function: whether it may call
the kernel, resize the packet, sleep, or raise a failure, and which
regions it may write. A write names its region: a byte range of the
packet as expressions over the names in scope, the whole packet when
the range is not known, a map, or a context field. Inside a function
a store through a `ref` or `view` parameter is recorded against the
parameter and instantiated at each call from the argument, so a
function's summary is stated over its parameters and constants.

This file is the data structure and its operations; the checker
computes the set statement by statement, since a packet write's
range comes from the facts at the store. The consumers are the
contracts (a preserved region against the writes and the resize),
the interface's resources (effects forbidden while a resource is held), and
the function summaries at call sites.
-/

namespace Koit.Effects

open Koit (Span)
open Koit.Core

/-- One effect. -/
inductive Eff where
  | call | resize | sleep | fail
  /-- `call(lock-safe)`: a call the kernel admits while a spin lock is
  held, which is the one distinction the spin lock's declaration
  draws among calls. -/
  | callSafe
  /-- A demand that the resource be held where the call runs: a
  function carries the demands of its calls to its callers. -/
  | needs (res : String)
  /-- `write(pkt[lo..hi))`, as expressions over the names in scope. -/
  | pkt (lo hi : Expr)
  /-- A write somewhere in the packet: a helper that writes it, or a
  store whose range the checker cannot state. -/
  | pktAll
  | map (name : String)
  | ctx (field : String)
  /-- In a function: a store through the `ref` parameter, wherever the
  argument lies. -/
  | viaRef (param : String)
  /-- In a function: a store through the `view` parameter, at the byte
  range relative to the parameter's start; a store at an offset that
  is not constant is recorded as the parameter's whole extent. -/
  | viaView (param : String) (lo hi : Nat)
  deriving Repr, Inhabited

namespace Eff

def print : Eff → String
  | .call => "call" | .resize => "resize" | .sleep => "sleep"
  | .fail => "fail" | .callSafe => "call(lock-safe)"
  | .needs r => s!"requires {r}"
  | .pkt lo hi => s!"write(pkt[{lo.print} .. {hi.print}))"
  | .pktAll => "write(pkt)"
  | .map m => s!"write({m})"
  | .ctx f => s!"write(ctx.{f})"
  | .viaRef x => s!"write(through {x})"
  | .viaView h lo hi => s!"write({h}[{lo} .. {hi}))"

/-- Structural equality, with expressions compared by their text. -/
def same (a b : Eff) : Bool := a.print == b.print

/-- The effect a interface declaration declares. A declaration's `write(pkt[a..b))`
keeps its range; its `write(pkt)` is the whole packet. -/
def ofCore : Core.Effect → Eff
  | .call => .call | .resize => .resize | .sleep => .sleep | .fail => .fail
  | .write (.pkt _ (some (lo, hi))) => .pkt lo hi
  | .write (.pkt _ none) => .pktAll
  | .write (.map _ m) => .map m
  | .write (.mapsExcept ..) => .pktAll
  | .write (.ctx _ f) => .ctx f

/-- Whether the effect is one of the four flags, as opposed to a
write. -/
def isFlag : Eff → Bool
  | .call | .resize | .sleep | .fail | .callSafe | .needs _ => true
  | _ => false

end Eff

/-- An effect set: a list without duplicates. -/
structure Effs where
  effs : List Eff := []
  deriving Repr, Inhabited

namespace Effs

def empty : Effs := {}

def has (E : Effs) (e : Eff) : Bool := E.effs.any (Eff.same · e)

def add (E : Effs) (e : Eff) : Effs :=
  if E.has e then E else { effs := E.effs ++ [e] }

def addAll (E : Effs) (es : List Eff) : Effs := es.foldl add E

def union (E F : Effs) : Effs := E.addAll F.effs

def ofList (es : List Eff) : Effs := empty.addAll es

/-- The effects an interface declaration declares. `resize` and
`sleep` imply `call`; a lock-safe declaration's `call` is
`call(lock-safe)`, and it never resizes or sleeps. -/
def ofCore (es : List Core.Effect) (lockSafe : Bool := false) : Effs :=
  let E := ofList (es.map Eff.ofCore)
  let E := if E.has .resize || E.has .sleep then E.add .call else E
  if lockSafe && E.has .call then
    { effs := E.effs.map fun e => match e with | .call => .callSafe | e => e }
  else E

def isEmpty (E : Effs) : Bool := E.effs.isEmpty

def print (E : Effs) : String :=
  "{" ++ ", ".intercalate (E.effs.map Eff.print) ++ "}"

/-- The set with every effect replaced by what `f` makes of it: the
instantiation of a function's summary at a call, where the effects
recorded against its parameters become effects on the arguments. -/
def bind (E : Effs) (f : Eff → Effs) : Effs :=
  E.effs.foldl (fun acc e => acc.union (f e)) empty

/-- The write effects of the set. -/
def writes (E : Effs) : List Eff := E.effs.filter fun e => !e.isFlag

/-- Whether a declaration's forbidden clause names the flag `e`. -/
def forbids (forbidden : List Core.Effect) (e : Eff) : Bool :=
  forbidden.any fun f =>
    match f, e with
    | .call, .call | .resize, .resize | .sleep, .sleep | .fail, .fail => true
    | _, _ => false

/-- The first effect of `E` that a resource's declaration forbids while it is
held; `sleep` is forbidden under every declaration. -/
def forbiddenBy (forbidden : List Core.Effect) (E : Effs) : Option Eff :=
  E.effs.find? fun e =>
    match e with
    | .sleep => true
    | e => forbids forbidden e

end Effs

/-! ### Preserved regions -/

/-- What a write effect does to a preserved region: nothing, a
violation, or a disjointness demand on the facts. -/
inductive Conflict where
  | none
  | always
  | demand (P : Expr)
  deriving Repr, Inhabited

/-- Whether the write `e` may touch the preserved region `r`. A packet
write against a packet range demands that the ranges be disjoint,
`hi <= a || b <= lo`, decided by entailment at the write; a resize
moves every byte, so it conflicts with any packet region. -/
def conflict (r : Region) (e : Eff) : Conflict :=
  match r, e with
  | .pkt .., .resize => .always
  | .pkt _ none, .pkt .. | .pkt _ none, .pktAll => .always
  | .pkt _ (some _), .pktAll => .always
  | .pkt _ (some (a, b)), .pkt lo hi =>
    .demand (.or noSpan (.cmp noSpan .le hi a) (.cmp noSpan .le b lo))
  | .map _ m, .map m' => if m == m' then .always else .none
  | .mapsExcept _ ms, .map m' => if ms.contains m' then .none else .always
  | .ctx _ f, .ctx f' => if f == f' then .always else .none
  | _, _ => .none
where noSpan : Span := Span.point Koit.Pos.origin

/-- The clause as the programmer wrote it, for diagnostics. -/
def _root_.Koit.Core.Region.printClause : Region → String
  | .pkt _ none => "preserve pkt"
  | .pkt _ (some (a, b)) => s!"preserve pkt[{a.print} .. {b.print})"
  | .map _ m => s!"preserve {m}"
  | .mapsExcept _ [] => "preserve maps"
  | .mapsExcept _ ms => s!"preserve maps except {", ".intercalate ms}"
  | .ctx _ f => s!"preserve ctx.{f}"

end Koit.Effects
