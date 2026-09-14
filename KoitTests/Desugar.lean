import Koit.Syntax.Parser
import Koit.Core.Desugar

/-!
Checks on the desugaring over small units, one guard per rewrite:
the printed Core of a program body or
a function is compared with the expected text. Multi-line texts are
lists of lines, as in the parser checks.
-/

open Koit Koit.Syntax Koit.Core

/-- The Core body of the first program, printed. -/
private def bodyOf (s : String) : Option String :=
  (parse s).toOption.bind fun u =>
    match (desugar Check.prelude u).programs with
    | p :: _ => some (Stmt.printBlock p.body 0)
    | [] => none

/-- The handler table of the first program, one `kind: body` per
entry, bodies on one line. -/
private def handlersOf (s : String) : Option (List String) :=
  (parse s).toOption.bind fun u =>
    match (desugar Check.prelude u).programs with
    | p :: _ => some (p.handlers.map fun h =>
        h.kind.print ++ ": " ++ " ".intercalate (h.body.map (·.print 0)))
    | [] => none

/-- The first function, printed. -/
private def fnOf (s : String) : Option String :=
  (parse s).toOption.bind fun u =>
    match (desugar Check.prelude u).fns with
    | f :: _ => some f.print
    | [] => none

private def lines (ls : List String) : String := "\n".intercalate ls

/-- An `xdp` program over a header type, an array map, and a hash map. -/
private def xdp (body : List String) : String :=
  lines (["type T = { a: u8, b: be16 }",
          "map m : array[1] of { cur: u32 where cur < 4 }",
          "map tab : hash[8] of T -> { v: u32 }",
          "program p : xdp fail drop {"] ++ body ++ ["}"])

private def block (ls : List String) : Option String :=
  some (lines (["{"] ++ ls ++ ["}"]))

-- (Mark): a marked view, the rest of the block inside `then`
#guard bodyOf (xdp ["  let e = pkt.view<T>(0)?", "  let x = e.a", "  drop"]) ==
  block ["  try e = view(0, T) then {",
         "    let x = e.a",
         "    return DROP",
         "  } else {",
         "    raise short_packet 0",
         "  }"]

-- (Else) with an exit, and `fail R` raising the operation's kind
#guard bodyOf (xdp ["  let c = m[0].cur else fail 7", "  drop"]) ==
  block ["  try c = loadw(m[0].cur) then {",
         "    return DROP",
         "  } else {",
         "    raise invariant 7",
         "  }"]

-- (Else) with a block, on a hash lookup
#guard bodyOf (xdp ["  let k = m[0]", "  let f = tab[k] else { pass }",
                    "  drop"]) ==
  block ["  let k = m[0]",
         "  try f = lookup(tab, k) then {",
         "    return DROP",
         "  } else {",
         "    return PASS",
         "  }"]

-- (IfLet): the rest follows the `try`
#guard bodyOf (xdp ["  let k = m[0]",
                    "  if let f = tab[k] { pass } else { drop }",
                    "  tx"]) ==
  block ["  let k = m[0]",
         "  try f = lookup(tab, k) then {",
         "    return PASS",
         "  } else {",
         "    return DROP",
         "  }",
         "  return TX"]

-- (Check): the coercion to `{b: bool | b}`
#guard bodyOf (xdp ["  var x = 1", "  check x < 2", "  drop"]) ==
  block ["  var x = 1",
         "  try _ = coerce(x < 2, { b: bool | b }) then {",
         "    return DROP",
         "  } else {",
         "    raise bound 0",
         "  }"]

-- (Coerce), with `else` and a `fail` without reason raising `bound`
#guard bodyOf (xdp ["  var x = 1",
                    "  let y = x as { v: u64 | v < 2 } else { fail }",
                    "  drop"]) ==
  block ["  var x = 1",
         "  try y = coerce(x, { v: u64 | v < 2 }) then {",
         "    return DROP",
         "  } else {",
         "    raise bound 0",
         "  }"]

-- the byte read, through a one-byte view and a temporary
#guard bodyOf (xdp ["  let c = pkt[3]?", "  drop"]) ==
  block ["  try $b1 = view(3, u8) then {",
         "    let c = rd *$b1",
         "    return DROP",
         "  } else {",
         "    raise short_packet 0",
         "  }"]

-- a helper used for its effect: the reason is the errno
#guard bodyOf (xdp ["  pkt.adjust_tail(4)?", "  drop"]) ==
  block ["  try _ = call pkt.adjust_tail(4) then {",
         "    return DROP",
         "  } else {",
         "    raise helper errno",
         "  }"]

-- map operations take the map first
#guard bodyOf (xdp ["  let k = m[0]", "  tab.insert(k, k)?", "  drop"]) ==
  block ["  let k = m[0]",
         "  try _ = call insert(tab, k, k) then {",
         "    return DROP",
         "  } else {",
         "    raise helper errno",
         "  }"]

-- compound assignment, unary minus, `size`, `pkt.len`
#guard bodyOf (xdp ["  var x = 1", "  x += T.size", "  x = -x + pkt.len",
                    "  drop"]) ==
  block ["  var x = 1",
         "  x := rd x + size T",
         "  x := (0 - x) + call pkt.len()",
         "  return DROP"]

-- `hold` of a lock, and of a socket with a marker
#guard bodyOf (xdp ["  let c = m[0]", "  hold lock(c.lk) { c.cur = 1 }",
                    "  drop"]) ==
  block ["  let c = m[0]",
         "  hold spinlock _ = acquire spinlock lock(c.lk) {",
         "    c.cur := 1",
         "  }",
         "  return DROP"]
#guard bodyOf (xdp ["  let t = m[0]",
                    "  hold sk = sk_lookup_tcp(t)? { sk_release(move sk) }",
                    "  drop"]) ==
  block ["  let t = m[0]",
         "  hold sockref sk = acquire sockref sk_lookup_tcp(t) then {",
         "    let _ = call sk_release(move sk)",
         "  } else {",
         "    raise missing 0",
         "  }",
         "  return DROP"]

-- a fallible operation in value position is `invalid`
#guard (bodyOf (xdp ["  let x = pkt.view<T>(0)", "  drop"])).map
    (·.startsWith
      "{\n  let x = invalid \"`pkt.view` can fail (kind `short_packet`)") ==
  some true

-- a struct literal and an atomic update
#guard bodyOf (xdp ["  let k = { a: 1, b: hton(2) }",
                    "  let old = atomic_add(m[0].cur, 1)",
                    "  drop"]) ==
  block ["  let k = { a: 1, b: hton 2 }",
         "  let old = atomic_add(m[0].cur, 1)",
         "  return DROP"]

-- verdict statements per kind
#guard bodyOf "program p : tc { pass }" == block ["  return OK"]
#guard bodyOf "program p : tc { tx }" ==
  block ["  return invalid \"`tx` is not a verdict statement of a `tc` \
    program\""]

-- handler tables: `fail`, a listed kind, `on _`, and the defaults
#guard handlersOf
    "program p : xdp fail pass on short_packet { drop } { tx }" ==
  some ["short_packet: return DROP", "missing: return PASS",
        "invariant: return PASS", "bound: return PASS", "helper: return PASS",
        "program: return PASS"]
#guard handlersOf "program p : tc on _ { pass } { drop }" ==
  some ["short_packet: return OK", "missing: return OK",
        "invariant: return OK", "bound: return OK", "helper: return OK",
        "program: return OK"]
#guard handlersOf "program p : syscall { return 0 }" ==
  some ["short_packet: return 0 - 1", "missing: return 0 - 1",
        "invariant: return 0 - 1", "bound: return 0 - 1",
        "helper: return 0 - 1", "program: return 0 - 1"]
#guard handlersOf "program p : xdp { drop }" ==
  some ["short_packet: return ABORTED", "missing: return ABORTED",
        "invariant: return ABORTED", "bound: return ABORTED",
        "helper: return ABORTED", "program: return ABORTED"]

-- functions: the tail expression is the result; a trailing call in a
-- resultless function is a statement
#guard fnOf "fn g(h: u32) -> u32 { h * 3 }" ==
  some (lines ["fn g(h: u32) -> u32 {", "  return h * 3", "}"])
#guard fnOf "fn g(x: u32) { printk(\"x\", x) }" ==
  some (lines ["fn g(x: u32) {", "  let _ = call printk(\"x\", x)", "}"])
#guard fnOf "fn f(x: u32 where x < 4) -> r: u32 where r <= x fails \
    { check x < 2; x }" ==
  some (lines ["fn f(x: u32 where x < 4) -> { r: u32 | r <= x } fails {",
               "  try _ = coerce(x < 2, { b: bool | b }) then {",
               "    return x",
               "  } else {",
               "    raise bound 0",
               "  }",
               "}"])

-- `for` stays; `repeat` is `loop`
#guard bodyOf (xdp ["  var s = 0", "  for i in 0..4 { s += i }",
                    "  repeat 2 { break }", "  drop"]) ==
  block ["  var s = 0",
         "  for i in 0..4 {",
         "    s := rd s + i",
         "  }",
         "  loop 2 {",
         "    break",
         "  }",
         "  return DROP"]
