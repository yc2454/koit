import Koit.Syntax.Parser
import Koit.Core.Desugar
import Koit.Check.Decl
import Koit.Interface.Interface

/-!
Checks on the base checker over small units: `ok` accepts, `has`
looks for a fragment of the diagnostic's message, `rejAt` gives its
position. The corpus under `tests/` covers each rule with a whole
program; the guards here pin the fine points of expression typing,
name resolution, and the declaration checks.
-/

open Koit Koit.Syntax Koit.Core Koit.Check

private def chk (s : String) : Except Diag Unit :=
  match parse s with
  | .error e => .error { span := e.span, msg := s!"parse: {e.msg}" }
  | .ok u =>
    (checkUnit Interface.v6_8 (desugar Interface.v6_8 u)).map fun _ => ()

private def ok (s : String) : Bool := (chk s).toOption.isSome

/-- The message, or `none` when the unit is accepted. -/
private def rej (s : String) : Option String :=
  match chk s with
  | .ok () => none
  | .error d => some d.msg

private def rejAt (s : String) : Option (Nat × Nat) :=
  match chk s with
  | .ok () => none
  | .error d => some (d.span.start.line, d.span.start.col)

/-- Whether the message contains `frag`. -/
private def has (s frag : String) : Bool :=
  match rej s with
  | some m => (m.splitOn frag).length > 1
  | none => false

private def lines (ls : List String) : String := "\n".intercalate ls

/-- A `syscall` program that returns 0 after `body`. -/
private def sys (body : List String) : String :=
  lines (["program p : syscall {"] ++ body ++ ["  return 0", "}"])

/-- An `xdp` program over a header type and a predicated map, that
drops after `body`. -/
private def xdp (body : List String) : String :=
  lines (["type EthHdr = { dst: u8[6], src: u8[6], proto: be16 }",
          "const M = 16",
          "map policy : array[1] of { cur: u32 where cur < M }",
          "program p : xdp default { drop } {"] ++ body ++ ["  drop", "}"])

/-- The view every packet guard starts with. -/
private def V : String := "  let eth = pkt.view<EthHdr>(0)?"

/-- A unit of declarations followed by a `syscall` program body. -/
private def unit (decls : List String) (body : List String) : String :=
  lines (decls ++ ["program p : syscall {"] ++ body ++ ["  return 0", "}"])

-- literals take the type of the context (Lit, LitDef)
#guard ok (sys ["  let x: u8 = 255"])
#guard has (sys ["  let x: u8 = 256"]) "does not fit in `u8`"
#guard ok (sys ["  let x: i8 = 127"])
#guard has (sys ["  let x: i8 = 128"]) "does not fit"
#guard ok (sys ["  let x = 1", "  let y: u64 = x"])
#guard has (sys ["  let x = 1", "  let y: u32 = x"]) "no implicit conversions"
#guard ok (sys ["  let x: u32 = 1 + 2 * 3"])
#guard has (sys ["  let x: u32 = 1", "  let y = x + 5000000000"]) "does not fit"

-- untyped constants are typed at each use; typed ones are monomorphic
#guard ok (unit ["const A = 300"] ["  let x: u16 = A"])
#guard has (unit ["const A = 300"] ["  let x: u8 = A"]) "does not fit in `u8`"
#guard has (unit ["const A : u16 = 3"] ["  let x: u8 = A"])
  "no implicit conversions"
#guard has (unit ["const A = B", "const B = A"] []) "in terms of itself"
#guard has (unit ["const A = f(1)"] []) "constant expression"

-- the interface is an outer scope: the unit shadows it
#guard ok (unit ["const IPPROTO_UDP = 17"] ["  let x: u8 = IPPROTO_UDP"])
#guard ok (sys ["  let x: u8 = IPPROTO_UDP"])
#guard ok (xdp [V, "  if eth.proto == ETH_P_IP { pass }"])

-- byte order: `be` compares with `be` only, and never computes
#guard has (xdp [V, "  if eth.proto == 0x0800 { pass }"])
  "compares only with a byte-order value"
#guard ok (xdp [V, "  if eth.proto == hton(0x0800) { pass }"])
#guard has (xdp [V, "  if eth.proto < hton(1) { pass }"])
  "compares only with `==` and `!=`"
#guard has (xdp [V, "  let x = eth.proto + 1"]) "nothing else"
#guard ok (xdp [V, "  let x = ntoh(eth.proto) + 1"])
#guard ok (xdp [V, "  eth.proto = hton(0x86DD)"])
#guard has (xdp [V, "  eth.proto = 5"]) "byte-order"
#guard has (sys ["  let s = hton(0x0800)"]) "width of `hton`"
#guard ok (sys ["  let s = hton(0x0800 as u16)"])

-- casts (Cast) and `bool as uN`
#guard ok (sys ["  let x: u8 = 1", "  let y = x as u64", "  let b = x == 1",
                "  let z = b as u8"])
#guard has (sys ["  let b = 1 as bool"]) "converts between integer types"
#guard has (sys ["  let x = 1 == 1", "  let y = x as i8"]) "unsigned"

-- comparisons take integers, never places or booleans
#guard has (sys ["  let a = true", "  let b = a == a"])
  "comparison takes two integers"
#guard ok (sys ["  let a = true", "  let b = a && !a || a"])

-- `size` and `pkt.len`
#guard ok (xdp ["  let s: u8 = EthHdr.size", "  let t = u32.size + 1"])
#guard has (xdp ["  let n: u32 = pkt.len"]) "no implicit conversions"
#guard ok (xdp ["  let n = pkt.len + EthHdr.size"])
#guard has (sys ["  let n = pkt.len"]) "has no packet"

-- name resolution
#guard has (sys ["  let x = policy"]) "unknown name `policy`"
#guard has (xdp ["  let x = policy"]) "is a map"
#guard has (xdp ["  let x = EthHdr"]) "is a type"
#guard has (sys ["  let x = PASS"]) "not a verdict of a `syscall`"
#guard has (unit ["fn f() -> u32 { PASS }"] [])
  "available only in a program body"
#guard has (sys ["  let x = pkt"]) "read through views"
#guard has (sys ["  let x = ctx"]) "read through its fields"
#guard has (sys ["  let x = ctx.mark"]) "opaque"
#guard has (xdp ["  let x = ctx.mark"]) "has no field `mark`"
#guard ok (lines ["program p : tc default { drop } { ctx.mark = 1", "  drop }"])

-- places against values (P3), reads and bindings
#guard ok (xdp ["  let c = policy[0]", "  let v = c.cur", "  c.cur = 3"])
#guard has (xdp ["  let c = policy[0]", "  let v = c + 1"]) "names a place"
#guard ok (xdp ["  let c = policy[0]", "  let d = c"])
#guard has (xdp ["  let v = policy[0] + 1"]) "is an aggregate"
#guard has (xdp ["  policy[0] = policy[0]"]) "assign its fields"
#guard has (xdp [V, "  let d = eth.dst", "  let b = d + 1"]) "names a place"
#guard ok (xdp [V, "  let d = eth.dst", "  d[0] = d[1]"])
#guard has (sys ["  let x = 1", "  x = 2"]) "is immutable"
#guard ok (sys ["  var x = 1", "  x = 2", "  x += 3"])

-- indexes are unsigned, and the bound is demanded of the facts
#guard ok (xdp [V, "  let i: u8 = 1", "  let b = eth.dst[i]"])
#guard has (xdp [V, "  let i: i32 = 1", "  let b = eth.dst[i]"])
  "an index must be unsigned"
#guard has (xdp [V, "  let b = eth.proto[0]"]) "not an array"
#guard has (xdp [V, "  let i = ctx.rx_queue_index", "  let b = eth.dst[i]"])
  "the index demands `i < 6`"
#guard ok (xdp [V, "  let i = ctx.rx_queue_index",
                "  if i < 6 { let b = eth.dst[i] }"])

-- marked loads need a `where` field; the unmarked read is the base type
#guard ok (xdp ["  let cur = policy[0].cur?", "  let n: u32 = cur"])
#guard ok (xdp ["  let cur = policy[0].cur", "  let n: u32 = cur"])
#guard has (xdp [V, "  let x = eth.proto?"]) "has no `where` clause"

-- calls: arity, fails context, results, the call graph
#guard ok (unit ["fn f(x: u32) -> u32 { x + 1 }"] ["  let y = f(2)"])
#guard has (unit ["fn f(x: u32) -> u32 { x + 1 }"] ["  let y = f(2, 3)"])
  "takes 1 arguments"
#guard has (unit ["fn f(x: u32) { }"] ["  let y = f(2)"]) "returns nothing"
#guard ok (unit ["fn f(x: u32) { }"] ["  f(2)"])
#guard has (unit ["fn f(x: u32) -> u32 { g(x) }",
                  "fn g(x: u32) -> u32 { f(x) }"] []) "acyclic"
#guard ok (unit ["fn f(x: u32) -> u32 { if x == 0 { return 1 } \
    else { return 2 } }"] [])
#guard has (unit ["fn f(x: u32) -> u32 { x + 1 }", "fn f(x: u32) -> u32 { x }"]
  []) "declared twice"

-- struct literals
#guard ok (unit ["type Flow = { a: be32, b: be32 }"]
  ["  let k = { a: hton(1 as u32), b: hton(2 as u32) }"])
#guard has (unit ["type Flow = { a: be32, b: be32 }"]
  ["  let k = { b: hton(1 as u32), a: hton(2 as u32) }"])
  "no declared struct type has the fields"
#guard has (unit ["type Flow = { a: u32, b: u32 }",
                  "type Flow2 = { a: u32, b: u32 }"]
  ["  let k = { a: 1, b: 2 }"]) "several declared types"
#guard ok (unit ["type Flow = { a: u32, b: u32 }",
                 "type Flow2 = { a: u32, b: u32 }"]
  ["  let k: Flow = { a: 1, b: 2 }"])

-- handlers, verdict sets, and exits
#guard ok "program p : xdp verdict in { PASS, DROP } default { drop } { pass }"
#guard has "program p : xdp verdict in { PASS } default { drop } { pass }"
  "not in the verdict set"
#guard has "program p : xdp verdict in { PASS, FOO } default { drop } { pass }"
  "not a verdict"
-- the view makes the handler reachable, so each is rejected for what
-- its handler body does
#guard has (lines ["program p : xdp default { drop }",
                   "  on short_packet { reason == 1; pass }",
                   "{ let e = pkt.view<u8[4]>(0)?; pass }"]) "must be a call"
#guard has (lines ["map s : array[4] of { n: u64 }",
                   "program p : xdp default { drop }",
                   "  on short_packet { s[reason].n += 1; pass }",
                   "{ let e = pkt.view<u8[4]>(0)?; pass }"])
  "the index demands `reason < 4`"
#guard ok (lines ["map s : array[4] of { n: u64 }",
                  "program p : xdp default { drop }",
                  "  on short_packet { if reason < 4 { s[reason].n += 1 }",
                  "    pass }",
                  "{ let e = pkt.view<u8[4]>(0)?; pass }"])
#guard has (sys ["  break"]) "outside a loop"
#guard ok (sys ["  repeat 4 { break }"])
#guard has (xdp ["  let cur = policy[0].cur?", "  repeat cur { }"])
  "constant expression"
#guard has "program p : xdp default { drop } { if true { pass } }"
  "must end in an exit"
#guard ok "program p : xdp default { drop } { if true { pass } else { drop } }"
#guard ok "program p : syscall { let x = 1 }"

-- positions are the surface construct's
#guard rejAt (sys ["  let x = 1", "  let y: u8 = x"]) == some (3, 15)
#guard rejAt (unit ["type T = { a: u8, b: view u8 }"] []) == some (1, 19)
