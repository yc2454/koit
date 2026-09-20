import Koit.Syntax.Parser
import Koit.Core.Desugar
import Koit.Core.Interp
import Koit.Prelude.Stage1

/-!
Checks on the evaluator over small programs: verdicts, handlers,
map state, the kernel's arithmetic, views and resizes, resources and
`move`, and the two section 23 programs on real packets.
-/

open Koit Koit.Syntax Koit.Core Koit.Check Koit.Core.Sem

/-- Runs a unit on a packet; the verdicts, then the map lines. -/
private def run (s : String) (packet : String := "") (ctx : List (String × Nat) := []) :
    Except String (List String × List String) := do
  let u ← match parse s with
    | .ok u => pure u
    | .error e => throw s!"parse: {e.msg}"
  let core := desugar Prelude.stage1 u
  match checkUnit Prelude.stage1 core with
  | .error d => throw s!"check: {d}"
  | .ok _ => pure ()
  let some bytes := parseHex packet | throw "bad hex"
  let (reports, maps) ← runUnit Prelude.stage1 core bytes ctx none 100000
  return (reports.map fun r => s!"{r.program}: {r.verdict}" ++
    String.join (r.log.map fun l => s!" [{l}]"), maps)

private def verdicts (s : String) (packet : String := "")
    (ctx : List (String × Nat) := []) : List String :=
  match run s packet ctx with
  | .ok (vs, _) => vs
  | .error e => [s!"error: {e}"]

private def maps (s : String) (packet : String := "") : List String :=
  match run s packet with
  | .ok (_, ms) => ms
  | .error e => [s!"error: {e}"]

private def lines (ls : List String) : String := "\n".intercalate ls

private def sys (body : List String) : String :=
  lines (["map m : array[4] of { n: u64, b: u8 }", "program p : syscall {"] ++
    body ++ ["}"])

-- the kernel's arithmetic: wrapping, division and modulo by zero,
-- signed division, masked shifts
#guard maps (sys ["  m[0].b = 255", "  m[0].b = m[0].b + 3"]) == ["map m:\n  [0] = { n: 0, b: 2 }"]
#guard maps (sys ["  let x: u32 = 7", "  let z: u32 = 0", "  m[0].n = (x / z) as u64",
                  "  m[1].n = (x % z) as u64"])
  == ["map m:\n  [1] = { n: 7, b: 0 }"]
#guard maps (sys ["  let x: i32 = 0 - 7", "  let y: i32 = 2", "  m[0].n = (x / y) as u64"])
  == ["map m:\n  [0] = { n: 18446744073709551613, b: 0 }"]
#guard maps (sys ["  let x: u32 = 1", "  m[0].n = (x << 33) as u64"])
  == ["map m:\n  [0] = { n: 2, b: 0 }"]
#guard maps (sys ["  let x: u64 = 1", "  m[0].n = x << 63"])
  == ["map m:\n  [0] = { n: 9223372036854775808, b: 0 }"]

-- verdicts, fall-off, and `return`
#guard verdicts (sys ["  return 3"]) == ["p: 3"]
#guard verdicts (sys ["  m[0].n = 1"]) == ["p: 0"]
#guard verdicts (sys ["  return 0 - 1"]) == ["p: -1"]

-- loops: counts, `for` bounds, `break` and `continue`
#guard maps (sys ["  repeat 5 { m[0].n += 1 }"]) == ["map m:\n  [0] = { n: 5, b: 0 }"]
#guard maps (sys ["  for i in 1..4 { m[i].n = i }"])
  == ["map m:\n  [1] = { n: 1, b: 0 }\n  [2] = { n: 2, b: 0 }\n  [3] = { n: 3, b: 0 }"]
#guard maps (sys ["  for i in 0..4 { if i == 2 { break }; m[i].n = 1 }"])
  == ["map m:\n  [0] = { n: 1, b: 0 }\n  [1] = { n: 1, b: 0 }"]
#guard maps (sys ["  for i in 0..4 { if i == 2 { continue }; m[i].n = 1 }"])
  == ["map m:\n  [0] = { n: 1, b: 0 }\n  [1] = { n: 1, b: 0 }\n  [3] = { n: 1, b: 0 }"]

-- functions and their frames
#guard maps (lines ["map m : array[1] of { n: u64 }",
                    "fn twice(x: u64) -> u64 { x * 2 }",
                    "fn bump(c: ref { n: u64 }) { c.n += 1 }",
                    "program p : syscall { m[0].n = twice(21); let c = m[0]; bump(c) }"])
  == ["map m:\n  [0] = { n: 43 }"]

-- failures reach the handler of their kind with the reason
private def xdp (header : List String) (body : List String) : String :=
  lines (["type EthHdr = { dst: u8[6], src: u8[6], proto: be16 }",
          "map stats : array[8] of { n: u64 }",
          "program p : xdp"] ++ header ++ ["{"] ++ body ++ ["}"])

#guard verdicts (xdp ["  fail drop"] ["  let eth = pkt.view<EthHdr>(0)?", "  pass"])
  == ["p: DROP"]
#guard verdicts (xdp ["  fail drop"] ["  let eth = pkt.view<EthHdr>(0)?", "  pass"])
  ("aa" ++ "aa" ++ "aaaaaaaa" ++ "bbbbbbbbbbbb" ++ "0800") == ["p: PASS"]
#guard verdicts (xdp ["  fail drop", "  on program { stats[reason & 7].n += 1; abort }"]
                     ["  fail 3"]) == ["p: ABORTED"]
#guard maps (xdp ["  fail drop", "  on program { stats[reason & 7].n += 1; abort }"]
                 ["  fail 3"]) == ["map stats:\n  [3] = { n: 1 }"]
-- the default handler of the kind
#guard verdicts (xdp [] ["  fail 1"]) == ["p: ABORTED"]
-- `check` raises `bound`; a marked load raises `invariant`
#guard verdicts (xdp ["  fail drop", "  on bound { tx }"]
                     ["  let n = ctx.rx_queue_index", "  check n < 4", "  pass"])
  == ["p: PASS"]
#guard verdicts (xdp ["  fail drop", "  on bound { tx }"]
                     ["  let n = ctx.rx_queue_index", "  check n < 4", "  pass"])
  "" [("rx_queue_index", 9)] == ["p: TX"]
#guard verdicts (lines ["map policy : array[1] of { cur: u32 where cur < 4 }",
                        "program p : xdp fail drop on invariant { abort } {",
                        "  let c = policy[0].cur?", "  pass }",
                        "program q : syscall { policy[0].cur = 3 }",
                        "program r : xdp fail drop on invariant { abort } {",
                        "  let c = policy[0].cur?", "  if c == 3 { tx }", "  pass }"])
  == ["p: PASS", "q: 0", "r: TX"]

-- views: reads, writes, and a resize
#guard verdicts (xdp ["  fail drop"]
  ["  let eth = pkt.view<EthHdr>(0)?", "  if eth.dst[1] == 0xbb { tx }", "  pass"])
  "aabbccddeeff" == ["p: DROP"]
#guard verdicts (xdp ["  fail drop"]
  ["  let eth = pkt.view<EthHdr>(0)?", "  if eth.dst[1] == 0xbb { tx }", "  pass"])
  ("aabbccddeeff000000000000" ++ "0800") == ["p: TX"]
#guard verdicts (xdp ["  fail drop", "  on helper { abort }"]
  ["  pkt.adjust_head(-8)?", "  let eth = pkt.view<EthHdr>(0)?", "  if eth.dst[0] == 0 { tx }", "  pass"])
  "aabbccddeeff" == ["p: TX"]
#guard verdicts (xdp ["  fail drop", "  on helper { abort }"]
  ["  pkt.adjust_head(8)?", "  pass"]) "aabb" == ["p: ABORTED"]

-- hash maps, lookups, and `if let`
private def hashUnit : String :=
  lines ["type Key = { a: u32, b: u32 }", "type Cnt = { n: u64 }",
         "map t : hash[2] of Key -> Cnt",
         "program ins : syscall {",
         "  let k = { a: 1, b: 2 }", "  let v = { n: 7 }", "  t.insert(k, v)?", "}",
         "program look : syscall {",
         "  let k = { a: 1, b: 2 }",
         "  if let e = t[k] { e.n += 1; return 1 } else { return 0 }", "}",
         "program miss : syscall {",
         "  let k = { a: 9, b: 9 }",
         "  if let e = t[k] { return 1 } else { return 0 }", "}"]
#guard verdicts hashUnit == ["ins: 0", "look: 1", "miss: 0"]
#guard maps hashUnit == ["map t:\n  { a: 1, b: 2 } => { n: 8 }"]

-- resources: a lock around a store, a record submitted on the normal
-- exit and discarded on a verdict, a socket moved to its sink
private def resUnit (body : List String) : String :=
  lines (["type Ctr = { lk: spinlock, n: u64 }",
          "map counters : array[1] of Ctr",
          "map events : ringbuf[64]",
          "map tuples : array[1] of SockTuple",
          "program p : xdp fail drop {", "  let c = counters[0]", "  let t = tuples[0]"] ++
          body ++ ["  pass", "}"])
#guard maps (resUnit ["  hold lock(c.lk) { c.n += 5 }"])
  == ["map counters:\n  [0] = { lk: spinlock, n: 5 }", "map events: 0 record(s)",
      "map tuples: all zero"]
#guard maps (resUnit ["  hold ev = events.reserve<u32>()? { *ev = 0x01020304 }"])
  == ["map counters: all zero", "map events: 1 record(s)\n  0x04030201", "map tuples: all zero"]
#guard maps (resUnit ["  hold ev = events.reserve<u32>()? { *ev = 1; drop }"])
  == ["map counters: all zero", "map events: 0 record(s)", "map tuples: all zero"]
#guard verdicts (resUnit ["  hold sk = sk_lookup_tcp(t)? { sk_release(move sk) }"]) == ["p: PASS"]
#guard verdicts (resUnit ["  hold sk = sk_lookup_tcp(t)? { c.n += 1 }"]) == ["p: PASS"]

-- `printk` lines are reported with the program
#guard verdicts (lines ["license \"GPL\"", "map m : array[1] of { n: u64 }",
                        "program p : syscall { m[0].n = 4; printk(\"n = {}\", m[0].n) }"])
  == ["p: 0 [n = 4]"]

/-! ### The section 23 programs -/

private def picker : String :=
  lines ["const M = 16",
         "const ETH_P_VLAN = hton(0x8100)", "const ETH_P_IP   = hton(0x0800)",
         "type EthHdr  = { dst: u8[6], src: u8[6], proto: be16 }",
         "type VlanHdr = { tci: be16, proto: be16 }",
         "type Backend = { ip: be32, ifindex: u32 }",
         "map policy   : array[1] of { cur: u32 where cur < M }",
         "map backends : array[1] of Backend[M]",
         "program pick : xdp",
         "  verdict in { PASS, DROP, ABORTED, REDIRECT }",
         "  preserve pkt", "  fail abort", "  on short_packet { drop }", "{",
         "  var off = 0", "  let eth = pkt.view<EthHdr>(off)?", "  off += EthHdr.size",
         "  var proto = eth.proto",
         "  repeat 2 {", "    if proto != ETH_P_VLAN { break }",
         "    let tag = pkt.view<VlanHdr>(off)?", "    proto = tag.proto",
         "    off += VlanHdr.size", "  }",
         "  if proto != ETH_P_IP { pass }",
         "  let cur = policy[0].cur?", "  let be  = backends[0][cur]",
         "  let v   = redirect(be.ifindex)?", "  return v", "}",
         "program rotate : syscall {",
         "  policy[0].cur = (policy[0].cur + 1) % M", "}"]

private def ethIp : String := "aaaaaaaaaaaabbbbbbbbbbbb" ++ "0800"
private def ethVlanIp : String := "aaaaaaaaaaaabbbbbbbbbbbb" ++ "8100" ++ "00010800"

#guard verdicts picker ethIp == ["pick: REDIRECT", "rotate: 0"]
#guard verdicts picker ethVlanIp == ["pick: REDIRECT", "rotate: 0"]
#guard verdicts picker ("aaaaaaaaaaaabbbbbbbbbbbb" ++ "86dd") == ["pick: PASS", "rotate: 0"]
#guard verdicts picker "aabb" == ["pick: DROP", "rotate: 0"]
#guard maps picker ethIp == ["map policy:\n  [0] = { cur: 1 }", "map backends: all zero"]
