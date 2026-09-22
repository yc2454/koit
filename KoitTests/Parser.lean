import Koit.Syntax.Parser
import Koit.Syntax.Print

/-!
Checks on the parser and printer over small units. `rt` parses and
prints; `stable` checks that printing is a fixed point of parse then
print; `perr` gives the position of a parse error. Multi-line texts
are written as lists of lines, since Lean strings have no escape for
a leading space after a line break.
-/

open Koit Koit.Syntax

def rt (s : String) : Option String :=
  (parse s).toOption.map CompUnit.print

def stable (s : String) : Bool :=
  match parse s with
  | .ok u =>
    let p := u.print
    (parse p).toOption.map CompUnit.print == some p
  | .error _ => false

def perr (s : String) : Option (Nat × Nat) :=
  match parse s with
  | .ok _ => none
  | .error e => some (e.span.start.line, e.span.start.col)

/-- Lines joined by newlines, without a trailing one. -/
def lines (ls : List String) : String := "\n".intercalate ls

/-- The same, with the trailing newline `CompUnit.print` emits. -/
def printed (ls : List String) : Option String := some (lines ls ++ "\n")

-- precedence and grouping
#guard rt "const A = 1 + 2 * 3" == some "const A = 1 + 2 * 3\n"
#guard rt "const A = (1 + 2) * 3" == some "const A = (1 + 2) * 3\n"
#guard rt "const A = 1 - 2 - 3" == some "const A = 1 - 2 - 3\n"
#guard rt "const A = 1 - (2 - 3)" == some "const A = 1 - (2 - 3)\n"
#guard rt "const A = -x as u32 + 1" == some "const A = -x as u32 + 1\n"
#guard rt "const A = a & b == c | d" == some "const A = a & b == c | d\n"
#guard rt "const A = a || b && !c" == some "const A = a || b && !c\n"
#guard rt "const A = x.f[1](2).g" == some "const A = x.f[1](2).g\n"
#guard rt "const A : u32 = 0x10" == some "const A : u32 = 0x10\n"
#guard perr "const A = 1 < 2 < 3" == some (1, 17)

-- types and other declarations
#guard rt "type T = { a: u8, b: be16 where b != 0, }" ==
  some "type T = { a: u8, b: be16 where b != 0 }\n"
#guard rt "type T = { v: u32 | v < 10 }" ==
  some "type T = { v: u32 | v < 10 }\n"
#guard rt "type T = ref u8[6]?" == some "type T = ref u8[6]?\n"
#guard rt "map m : hash[64] of K -> { v: u32 }" ==
  some "map m : hash[64] of K -> { v: u32 }\n"
#guard rt "map r : ringbuf[4096]" == some "map r : ringbuf[4096]\n"
#guard rt "config N : u32" == some "config N : u32\n"
#guard rt "license \"GPL\"\nconst A = 1" ==
  some "license \"GPL\"\n\nconst A = 1\n"

-- functions
#guard rt (lines
    ["fn f(x: u32 where x < 10, y: ref T) -> r: u32 where r <= x fails {",
     "  return x",
     "}"]) ==
  printed
    ["fn f(x: u32 where x < 10, y: ref T) -> r: u32 where r <= x fails {",
     "  return x",
     "}"]
#guard rt "fn f() -> u32? { if let v = m[k] { return v } else { return } }" ==
  printed
    ["fn f() -> u32? {",
     "  if let v = m[k] {",
     "    return v",
     "  } else {",
     "    return",
     "  }",
     "}"]
#guard rt "fn g(h: u32) -> u32 { h * 3 }" ==
  printed ["fn g(h: u32) -> u32 {", "  h * 3", "}"]

-- statements, inside a one-line program header
def prog (body : List String) : String :=
  lines (["program p : xdp {"] ++ body ++ ["}"])

def progOut (body : List String) : Option String :=
  printed (["program p : xdp {"] ++ body ++ ["}"])

#guard rt (prog ["  let x = e as { v: u32 | v < 10 }?"]) ==
  progOut ["  let x = e as { v: u32 | v < 10 }?"]
#guard rt (prog ["  var n: u64 where n <= M = 0"]) ==
  progOut ["  var n: u64 where n <= M = 0"]
#guard rt (prog ["  let f = m[k] else { pass }"]) ==
  progOut ["  let f = m[k] else {", "    pass", "  }"]
#guard rt (prog ["  let c = p[0].cur else fail 7"]) ==
  progOut ["  let c = p[0].cur else fail 7"]
#guard rt (prog ["  if a { pass } else if b { drop } else { tx }"]) ==
  progOut ["  if a {", "    pass", "  } else if b {", "    drop",
           "  } else {", "    tx", "  }"]
#guard rt (prog ["  for i in 0..n + 1 { x += i }"]) ==
  progOut ["  for i in 0..n + 1 {", "    x += i", "  }"]
#guard rt (prog ["  for (k, v) in m bounded 4? { break }"]) ==
  progOut ["  for (k, v) in m bounded 4? {", "    break", "  }"]
#guard rt (prog ["  hold ev = r.reserve<E>() else drop { ev.k = 1 }"]) ==
  progOut ["  hold ev = r.reserve<E>() else drop {", "    ev.k = 1", "  }"]
#guard rt (prog ["  hold lock(e.lk) { }", "  abort"]) ==
  progOut ["  hold lock(e.lk) { }", "  abort"]
#guard rt (prog ["  *d = 1; check x < 2 else { drop }; f(x)?"]) ==
  progOut ["  *d = 1", "  check x < 2 else {", "    drop", "  }", "  f(x)?"]
#guard rt (prog ["  let v = pkt.view<u8[4]>(off)?", "  return v"]) ==
  progOut ["  let v = pkt.view<u8[4]>(off)?", "  return v"]
#guard rt (prog ["  let s = { a: 1, b: x }", "  printk(\"n = {}\\n\", n)"]) ==
  progOut ["  let s = { a: 1, b: x }", "  printk(\"n = {}\\n\", n)"]
#guard perr (prog ["  let x = e else 5"]) == some (2, 18)
#guard perr (prog ["  1 + 2 = 3"]) == some (2, 3)
#guard perr (prog ["  if x { pass }", "  else { drop }"]) == some (3, 3)
#guard perr (prog ["  for (k, v) in 0..4 { }"]) == some (2, 7)
#guard perr (prog ["  let x = 1 2"]) == some (2, 13)

-- headers and contracts, with newlines as whitespace in the header
def header : String := lines
  ["program pick : xdp implements Mon",
   "  verdict in { PASS, DROP }",
   "  preserve pkt[0 .. 14), maps except a, b",
   "  on short_packet, fail { drop }",
   "  default { pass }",
   "{",
   "  pass",
   "}"]
#guard rt header == printed
  ["program pick : xdp implements Mon",
   "  verdict in { PASS, DROP }",
   "  preserve pkt[0 .. 14), maps except a, b",
   "  on short_packet, fail {",
   "    drop",
   "  }",
   "  default {",
   "    pass",
   "  }",
   "{",
   "  pass",
   "}"]
#guard rt (lines ["contract C : tc {", "  verdict in { OK }",
                  "  preserve ctx.mark, s", "}"]) ==
  printed ["contract C : tc {", "  verdict in { OK }",
           "  preserve ctx.mark, s", "}"]
#guard perr (lines ["fn f(x: u32) -> u32 {", "  return x", "}", "fn"]) ==
  some (4, 3)

-- printing is a fixed point on everything above
#guard stable header
#guard stable (prog ["  let x = e as { v: u32 | v < 10 }?"])
#guard stable "type T = { a: u8, b: be16 where b != 0, }"
