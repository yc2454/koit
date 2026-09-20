import Koit.Syntax.Parser
import Koit.Core.Desugar
import Koit.Core.Interp
import Koit.Compile.Lower
import Koit.Compile.Inline
import Koit.LIR.Interp
import Koit.Prelude.Stage1

/-!
Checks on the lowering: every unit here lowers to well-formed LIR,
with and without inlining, and the LIR runs print exactly what the
Core runs print, verdicts, `printk` lines, and maps, on the section
23 programs over real packets and on small units that exercise each
construct the lowering translates: booleans in value position, the
lookup by helper and its dead branch, hash maps, marked loads,
coercions, functions with and without failures, absence, locks,
ring-buffer records, sockets and `move`, atomics, and byte order.
-/

open Koit Koit.Syntax Koit.Core Koit.Check Koit.Core.Sem

/-- Core's report of a run, as lines. -/
private def coreRun (s : String) (packet : String) (ctx : List (String × Nat)) :
    Except String (List String) := do
  let u ← match parse s with
    | .ok u => pure u
    | .error e => throw s!"parse: {e.msg}"
  let core := desugar Prelude.stage1 u
  let _ ← match checkUnit Prelude.stage1 core with
    | .error d => throw s!"check: {d}"
    | .ok c => pure c
  let some bytes := parseHex packet | throw "bad hex"
  let (reports, maps) ← runUnit Prelude.stage1 core bytes ctx none 100000
  return (reports.map fun r => s!"{r.program}: {r.verdict}" ++
    String.join (r.log.map fun l => s!" [{l}]")) ++ maps

/-- The LIR report of the same run, inlined or not. -/
private def lirRun (s : String) (packet : String) (ctx : List (String × Nat))
    (inl : Bool) : Except String (List String) := do
  let u ← match parse s with
    | .ok u => pure u
    | .error e => throw s!"parse: {e.msg}"
  let core := desugar Prelude.stage1 u
  let checked ← match checkUnit Prelude.stage1 core with
    | .error d => throw s!"check: {d}"
    | .ok c => pure c
  let lir ← Compile.lower Prelude.stage1 (Compile.fold Prelude.stage1 core checked)
  let lir := if inl then Compile.inline lir else lir
  LIR.wf Prelude.stage1 lir |>.mapError ("wf: " ++ ·)
  let some bytes := parseHex packet | throw "bad hex"
  let (reports, maps) ← LIR.Sem.runUnit Prelude.stage1 core lir bytes ctx none 100000
  return (reports.map fun r => s!"{r.program}: {r.verdict}" ++
    String.join (r.log.map fun l => s!" [{l}]")) ++ maps

/-- Whether the three runs agree and the Core run is the expected
one. -/
private def agree (s : String) (expect : List String) (packet : String := "")
    (ctx : List (String × Nat) := []) : Bool :=
  match coreRun s packet ctx, lirRun s packet ctx false, lirRun s packet ctx true with
  | .ok a, .ok b, .ok c => a == expect && b == expect && c == expect
  | _, _, _ => false

/-- The three runs, for reading a failure. -/
private def runs (s : String) (packet : String := "") (ctx : List (String × Nat) := []) :
    List String :=
  let show_ : Except String (List String) → String
    | .ok ls => String.intercalate " | " ls
    | .error e => s!"error: {e}"
  [show_ (coreRun s packet ctx), show_ (lirRun s packet ctx false),
   show_ (lirRun s packet ctx true)]

private def lines (ls : List String) : String := "\n".intercalate ls

private def sys (decls : List String) (body : List String) : String :=
  lines (decls ++ ["program p : syscall {"] ++ body ++ ["}"])

private def M1 : List String := ["map m : array[4] of { n: u64, b: u8 }"]

-- arithmetic at every width, through the fold and the cast table
#guard agree (sys M1 ["  m[0].b = 255", "  m[0].b = m[0].b + 3"]) ["p: 0", "map m:\n  [0] = { n: 0, b: 2 }"]
#guard agree (sys M1 ["  let x: u32 = 7", "  let z: u32 = 0", "  m[1].n = (x / z) as u64",
                      "  m[2].n = (x % z) as u64"])
  ["p: 0", "map m:\n  [2] = { n: 7, b: 0 }"]
#guard agree (sys M1 ["  let x: i32 = 0 - 7", "  let y: i32 = 2", "  m[3].n = (x / y) as u64"])
  ["p: 0", "map m:\n  [3] = { n: 18446744073709551613, b: 0 }"]
#guard agree (sys M1 ["  let x: i8 = 0 - 100", "  m[0].n = (x >> 2) as u64"])
  ["p: 0", "map m:\n  [0] = { n: 18446744073709551591, b: 0 }"]
-- the lookup by helper into a map with several slots, its dead
-- branch untaken
#guard agree (sys M1 ["  for i in 1..4 { m[i].n = i * 10 }", "  return 5"])
  ["p: 5", "map m:\n  [1] = { n: 10, b: 0 }\n  [2] = { n: 20, b: 0 }\n  [3] = { n: 30, b: 0 }"]
-- loops: break and continue through the release-free exits
#guard agree (sys M1 ["  for i in 0..4 { if i == 2 { break }; m[i].n = 1 }"])
  ["p: 0", "map m:\n  [0] = { n: 1, b: 0 }\n  [1] = { n: 1, b: 0 }"]
#guard agree (sys M1 ["  repeat 4 { m[0].n += 1; if m[0].n == 2 { continue }; m[1].n += 1 }"])
  ["p: 0", "map m:\n  [0] = { n: 4, b: 0 }\n  [1] = { n: 3, b: 0 }"]
-- booleans in value position and in conditions
#guard agree (sys M1 ["  let a: u32 = 3", "  let b: u32 = 4",
                      "  let both = a < b && b < 10", "  let either = a > b || b == 4",
                      "  if both && either && !(a == b) { m[0].n = 1 }",
                      "  m[1].n = both as u64", "  m[2].n = (!either) as u64"])
  ["p: 0", "map m:\n  [0] = { n: 1, b: 0 }\n  [1] = { n: 1, b: 0 }"]
-- functions: by value, by reference, with a failure and with absence
#guard agree (lines ["map m : array[1] of { n: u64 }",
                     "fn twice(x: u64) -> u64 { x * 2 }",
                     "fn bump(c: ref { n: u64 }) { c.n += 1 }",
                     "program p : syscall { m[0].n = twice(21); let c = m[0]; bump(c) }"])
  ["p: 0", "map m:\n  [0] = { n: 43 }"]
#guard agree (lines ["map m : array[1] of { n: u64 }",
                     "fn pick(x: u64) -> u64? { if x > 3 { return x } else { return } }",
                     "program p : syscall {",
                     "  let a = pick(5) else { return 1 }", "  m[0].n = a",
                     "  let b = pick(1) else { return 2 }", "  m[0].n = b", "}"])
  ["p: 2", "map m:\n  [0] = { n: 5 }"]
#guard agree (lines ["map m : array[1] of { n: u64 }",
                     "fn guard(x: u64) -> u64 fails { check x < 10; x + 1 }",
                     "program p : syscall fail return 0 - 7 on bound { return 0 - 9 } {",
                     "  m[0].n = guard(3)", "  m[0].n = guard(30)", "}"])
  ["p: -9", "map m:\n  [0] = { n: 4 }"]
-- a map written before a failure keeps the write
#guard agree (sys ["map m : array[1] of { n: u64 }"]
  ["  m[0].n = 3", "  fail 2", "  m[0].n = 5"]) ["p: -1", "map m:\n  [0] = { n: 3 }"]
-- failures reach the handler of their kind with the reason
private def xdp (header : List String) (body : List String) : String :=
  lines (["type EthHdr = { dst: u8[6], src: u8[6], proto: be16 }",
          "map stats : array[8] of { n: u64 }",
          "program p : xdp"] ++ header ++ ["{"] ++ body ++ ["}"])

#guard agree (xdp ["  fail drop"] ["  let eth = pkt.view<EthHdr>(0)?", "  pass"])
  ["p: DROP", "map stats: all zero"]
#guard agree (xdp ["  fail drop"] ["  let eth = pkt.view<EthHdr>(0)?", "  pass"])
  ["p: PASS", "map stats: all zero"] ("aaaaaaaaaaaabbbbbbbbbbbb0800")
#guard agree (xdp ["  fail drop", "  on program { stats[reason & 7].n += 1; abort }"]
                  ["  fail 3"]) ["p: ABORTED", "map stats:\n  [3] = { n: 1 }"]
-- `check`, a marked load, a coercion, and byte order
#guard agree (xdp ["  fail drop", "  on bound { tx }"]
                  ["  let n = ctx.rx_queue_index", "  check n < 4", "  stats[n].n = 1", "  pass"])
  ["p: PASS", "map stats:\n  [2] = { n: 1 }"] "" [("rx_queue_index", 2)]
#guard agree (xdp ["  fail drop", "  on bound { tx }"]
                  ["  let n = ctx.rx_queue_index", "  check n < 4", "  pass"])
  ["p: TX", "map stats: all zero"] "" [("rx_queue_index", 9)]
#guard agree (lines ["map policy : array[1] of { cur: u32 where cur < 4 }",
                     "map stats : array[4] of { n: u64 }",
                     "program q : syscall { policy[0].cur = 3 }",
                     "program r : xdp fail drop on invariant { abort } {",
                     "  let c = policy[0].cur?", "  stats[c].n = 7", "  if c == 3 { tx }", "  pass }"])
  ["q: 0", "r: TX", "map policy:\n  [0] = { cur: 3 }", "map stats:\n  [3] = { n: 7 }"]
#guard agree (xdp ["  fail drop"]
  ["  let eth = pkt.view<EthHdr>(0)?", "  if eth.proto == hton(0x0800) { eth.proto = hton(0x86dd); tx }", "  pass"])
  ["p: TX", "map stats: all zero"] ("aabbccddeeff000000000000" ++ "0800")
#guard agree (xdp ["  fail drop"]
  ["  let eth = pkt.view<EthHdr>(0)?", "  let v = ntoh(eth.proto) as u64", "  stats[v & 7].n = v", "  pass"])
  ["p: PASS", "map stats:\n  [0] = { n: 2048 }"] ("aabbccddeeff000000000000" ++ "0800")
-- a resize: the view is carved again after it
#guard agree (xdp ["  fail drop", "  on helper { abort }"]
  ["  pkt.adjust_head(-8)?", "  let eth = pkt.view<EthHdr>(0)?", "  if eth.dst[0] == 0 { tx }", "  pass"])
  ["p: TX", "map stats: all zero"] "aabbccddeeff"
-- hash maps: insert, lookup, `if let`, delete, and a full map
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
         "  if let e = t[k] { return 1 } else { return 0 }", "}",
         "program full : syscall fail return 0 - 1 on helper { return reason as i32 } {",
         "  let k = { a: 3, b: 3 }", "  let v = { n: 1 }", "  t.insert(k, v)?",
         "  let k2 = { a: 4, b: 4 }", "  t.insert(k2, v)?", "}",
         "program del : syscall {",
         "  let k = { a: 3, b: 3 }", "  t.delete(k) else { return 5 }", "  return 6", "}"]
#guard agree hashUnit ["ins: 0", "look: 1", "miss: 0", "full: -7", "del: 6",
                       "map t:\n  { a: 1, b: 2 } => { n: 8 }"]
-- resources: a lock, a record submitted and discarded, a socket
-- moved to its sink and one released by the scope
private def resUnit (body : List String) : String :=
  lines (["type Ctr = { lk: spinlock, n: u64 }",
          "map counters : array[1] of Ctr",
          "map events : ringbuf[64]",
          "map tuples : array[1] of SockTuple",
          "program p : xdp fail drop {", "  let c = counters[0]", "  let t = tuples[0]"] ++
          body ++ ["  pass", "}"])
#guard agree (resUnit ["  hold lock(c.lk) { c.n += 5 }"])
  ["p: PASS", "map counters:\n  [0] = { lk: spinlock, n: 5 }", "map events: 0 record(s)",
   "map tuples: all zero"]
#guard agree (resUnit ["  hold lock(c.lk) { c.n += 5; if c.n == 5 { drop } }"])
  ["p: DROP", "map counters:\n  [0] = { lk: spinlock, n: 5 }", "map events: 0 record(s)",
   "map tuples: all zero"]
#guard agree (resUnit ["  hold ev = events.reserve<u32>()? { *ev = 0x01020304 }"])
  ["p: PASS", "map counters: all zero", "map events: 1 record(s)\n  0x04030201",
   "map tuples: all zero"]
#guard agree (resUnit ["  hold ev = events.reserve<u32>()? { *ev = 1; drop }"])
  ["p: DROP", "map counters: all zero", "map events: 0 record(s)", "map tuples: all zero"]
#guard agree (resUnit ["  hold sk = sk_lookup_tcp(t)? { sk_release(move sk) }"])
  ["p: PASS", "map counters: all zero", "map events: 0 record(s)", "map tuples: all zero"]
#guard agree (resUnit ["  hold sk = sk_lookup_tcp(t)? { c.n += 1 }"])
  ["p: PASS", "map counters:\n  [0] = { lk: spinlock, n: 1 }", "map events: 0 record(s)",
   "map tuples: all zero"]
-- a lock released by a failure inside it, on the way to the handler
#guard agree (lines ["type Ctr = { lk: spinlock, n: u64 where n < 4 }",
                     "map counters : array[1] of Ctr",
                     "program q : syscall { counters[0].n = 3 }",
                     "program p : xdp fail drop on invariant { tx } {",
                     "  let c = counters[0]",
                     "  hold lock(c.lk) { let n = c.n?; if n == 3 { fail } }", "  pass }"])
  ["q: 0", "p: DROP", "map counters:\n  [0] = { lk: spinlock, n: 3 }"]
-- atomics on a map place and on a local, with the previous value
#guard agree (sys ["map m : array[1] of { n: u64, k: u32 }"]
  ["  let old = atomic_add(m[0].n, 5)", "  let old2 = atomic_xchg(m[0].k, 9)",
   "  var x: u32 = 4", "  let o3 = atomic_add(x, 1)", "  m[0].k = m[0].k + old2 + o3 + x",
   "  return old as i32"])
  ["p: 0", "map m:\n  [0] = { n: 5, k: 18 }"]
-- `printk` lines and the trace
#guard agree (lines ["license \"GPL\"", "map m : array[1] of { n: u64 }",
                     "program p : syscall { m[0].n = 4; printk(\"n = {} {}\", m[0].n, 7) }"])
  ["p: 0 [n = 4 7]", "map m:\n  [0] = { n: 4 }"]

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

#guard agree picker ["pick: REDIRECT", "rotate: 0", "map policy:\n  [0] = { cur: 1 }",
                     "map backends: all zero"] ethIp
#guard agree picker ["pick: REDIRECT", "rotate: 0", "map policy:\n  [0] = { cur: 1 }",
                     "map backends: all zero"] ethVlanIp
#guard agree picker ["pick: PASS", "rotate: 0", "map policy:\n  [0] = { cur: 1 }",
                     "map backends: all zero"] ("aaaaaaaaaaaabbbbbbbbbbbb" ++ "86dd")
#guard agree picker ["pick: DROP", "rotate: 0", "map policy:\n  [0] = { cur: 1 }",
                     "map backends: all zero"] "aabb"
