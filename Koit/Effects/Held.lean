import Koit.Interface.Decls
import Koit.Effects.Effects

/-!
The held set `H` of the statement rules: the resources the enclosing
`hold` blocks have acquired, innermost first, each with its declaration of
the interface's resources, the name bound to it when it yields a value, and
the statement that acquired it, for messages. While a resource is
held, the effects its declaration forbids are errors, `sleep` is forbidden
under every declaration, and a declaration that does not nest refuses a second
instance of itself. Resources are lexically scoped, so the set grows
at the entry of a `hold` body and is restored after it; a function
never sees its caller's set, since a resource is not held across a
function boundary.
-/

namespace Koit.Effects

open Koit (Span)
open Koit.Core
open Koit.Interface (ResourceDecl Nesting)

/-- One held resource. -/
structure HeldEntry where
  decl  : ResourceDecl
  /-- The owned name the `hold` bound, for a declaration that yields one. -/
  name : Option String
  /-- The acquisition as written, `lock(c.lk)`, for messages. -/
  what : String
  span : Span
  deriving Inhabited

/-- The held set, innermost first. -/
abbrev Held := List HeldEntry

namespace Held

/-- The innermost instance of the resource `r`, if held. -/
def holds (H : Held) (r : Resource) : Option HeldEntry :=
  H.find? (·.decl.res == r)

/-- The first effect of `E` that a held declaration forbids, with the entry
that forbids it; `sleep` is forbidden under every declaration. -/
def forbidden (H : Held) (E : Effs) : Option (Eff × HeldEntry) :=
  H.findSome? fun h => (Effs.forbiddenBy h.decl.forbidden E).map (·, h)

/-- The held instance that refuses acquiring `declaration` again: a declaration whose
nesting clause says no, when an instance of it is held. -/
def nestingConflict (H : Held) (decl : ResourceDecl) : Option HeldEntry :=
  if decl.nesting == .no then H.holds decl.res else none

end Held

end Koit.Effects
