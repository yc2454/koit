/-!
Source positions and spans.

Every token and every AST node carries a span, so a diagnostic can
name the line and column of what it is about, and so a Core node
produced by desugaring can point back at the surface construct it
came from.
-/

namespace Koit

/-- A position in a source file: 1-based line and column, and the
0-based byte offset used to slice the source text. -/
structure Pos where
  line : Nat
  col  : Nat
  byte : Nat
  deriving Repr, BEq, Inhabited

namespace Pos

/-- The first position of a file. -/
def origin : Pos := { line := 1, col := 1, byte := 0 }

/-- `line:col`, the form diagnostics print. -/
protected def toString (p : Pos) : String := s!"{p.line}:{p.col}"

instance : ToString Pos := ⟨Pos.toString⟩

end Pos

/-- A half-open range of source text, `[start, stop)`. -/
structure Span where
  start : Pos
  stop  : Pos
  deriving Repr, BEq, Inhabited

namespace Span

/-- The empty span at a position, for zero-width tokens such as the
end of file. -/
def point (p : Pos) : Span := { start := p, stop := p }

/-- The span from the start of `a` to the end of `b`, for an AST node
built from its first and last token. `a` must not start after `b`. -/
def merge (a b : Span) : Span := { start := a.start, stop := b.stop }

/-- The line a span starts on, which is what a diagnostic names. -/
def line (s : Span) : Nat := s.start.line

instance : ToString Span := ⟨fun s => toString s.start⟩

end Span

end Koit
