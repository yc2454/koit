import Koit.Syntax.Span

/-!
Diagnostics. A `Diag` is a span and a message; `koitc` prints it as
`file:line:col: message`. The span is the Core node's, which is the
span of the surface construct it came from, so the line named is the
one the programmer wrote (spec/language.md 18.1, PLAN.md session 2).

The checker stops at the first error: its monad is `Except Diag`.
-/

namespace Koit.Check

open Koit (Span)

structure Diag where
  span : Span
  msg  : String
  deriving Repr, Inhabited

instance : ToString Diag := ⟨fun d => s!"{d.span.start}: {d.msg}"⟩

/-- The checker's monad. -/
abbrev M := Except Diag

def err (span : Span) (msg : String) : M α := throw { span, msg }

end Koit.Check
