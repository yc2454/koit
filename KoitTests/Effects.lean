import Koit.Syntax.Parser
import Koit.Core.Desugar
import Koit.Check.Decl
import Koit.Interface.Interface

/-!
Checks on the effect sets the checker computes and on the preserved
regions they are checked against: a function's summary over its
parameters, its instantiation at a call, a program's effects, and
the rejections a `preserve` clause causes.
-/

open Koit Koit.Syntax Koit.Core Koit.Check Koit.Effects

private def chk (s : String) : Except Diag Checked :=
  match parse s with
  | .error e => .error { span := e.span, msg := s!"parse: {e.msg}" }
  | .ok u => checkUnit Interface.v6_8 (desugar Interface.v6_8 u)

private def ok (s : String) : Bool := (chk s).toOption.isSome

private def has (s frag : String) : Bool :=
  match chk s with
  | .ok _ => false
  | .error d => (d.msg.splitOn frag).length > 1

/-- The summary of function `f`, printed. -/
private def fnEffs (s f : String) : Option String :=
  (chk s).toOption.bind fun out => (out.fns.lookup f).map (·.print)

/-- The effects of program `p`, printed. -/
private def progEffs (s p : String) : Option String :=
  (chk s).toOption.bind fun out => (out.programs.lookup p).map (·.print)

private def lines (ls : List String) : String := "\n".intercalate ls

private def decls : List String :=
  ["type EthHdr = { dst: u8[6], src: u8[6], proto: be16 }",
   "type Ctr = { n: u64 }",
   "map counters : array[1] of Ctr",
   "map stats : array[1] of Ctr",
   "fn bump(c: ref Ctr) { c.n += 1 }",
   "fn stamp(h: view EthHdr) { h.proto = hton(0) }",
   "fn zero(h: view EthHdr, i: u64 where i < 6) { h.dst[i] = 0 }",
   "fn both(c: ref Ctr, h: view EthHdr) { bump(c); stamp(h) }"]

/-- An `xdp` program with `clauses` in its header and `body`. -/
private def xdp (clauses : List String) (body : List String) : String :=
  lines (decls ++ ["program p : xdp"] ++ clauses ++ ["  default { drop }", "{"] ++
    body ++ ["  drop", "}"])

private def V : String := "  let eth = pkt.view<EthHdr>(0)?"

-- function summaries are stated over the parameters
#guard fnEffs (xdp [] []) "bump" == some "{write(through c)}"
#guard fnEffs (xdp [] []) "stamp" == some "{write(h[12 .. 14))}"
-- an element at a variable index is the view's whole extent
#guard fnEffs (xdp [] []) "zero" == some "{write(h[0 .. 14))}"
-- a callee's summary is instantiated in the caller's summary
#guard fnEffs (xdp [] []) "both" == some "{write(through c), write(h[12 .. 14))}"

-- a program's effects: the marker's `fail`, the writes with the
-- packet range from the view's offset, the calls of the interface
#guard progEffs (xdp [] [V, "  let c = counters[0]", "  bump(c)", "  stamp(eth)"])
  "p" == some "{write(counters), write(pkt[12 .. 14)), fail}"
#guard progEffs (xdp [] ["  let c = counters[0]", "  both(c, eth)"]) "p" == none
#guard progEffs (xdp [] [V, "  eth.dst[2] = 0"]) "p"
  == some "{write(pkt[2 .. 3)), fail}"
#guard progEffs (xdp [] [V, "  pkt.adjust_head(-8)?"]) "p"
  == some "{call, resize, fail}"
#guard progEffs (xdp [] ["  stats[0].n += 1", "  let c = counters[0]",
                         "  let old = atomic_add(c.n, 1)"]) "p"
  == some "{write(stats), write(counters)}"
-- the offset of a view carved at a variable offset
#guard progEffs (xdp [] ["  var off = 0", "  off = 14",
                         "  let eth = pkt.view<EthHdr>(off)?",
                         "  eth.proto = hton(0)"]) "p"
  == some "{write(pkt[off + 12 .. off + 14)), fail}"

-- `preserve pkt`: no packet write, no resize
#guard has (xdp ["  preserve pkt"] [V, "  eth.proto = hton(0)"])
  "writes the packet bytes [12 .. 14), which `preserve pkt` forbids"
#guard has (xdp ["  preserve pkt"] [V, "  stamp(eth)"])
  "which `preserve pkt` forbids"
#guard has (xdp ["  preserve pkt"] ["  pkt.adjust_head(-8)?"])
  "resizes the packet, which `preserve pkt` forbids"
#guard ok (xdp ["  preserve pkt"] [V, "  let x = eth.proto"])

-- `preserve pkt[a .. b)`: disjointness is a demand on the facts
#guard has (xdp ["  preserve pkt[0 .. 14)"] [V, "  eth.proto = hton(0)"])
  "under `preserve pkt[0 .. 14)` demands `14 <= 0 || 14 <= 12`"
#guard ok (xdp ["  preserve pkt[0 .. 12)"] [V, "  eth.proto = hton(0)"])
#guard ok (xdp ["  preserve pkt[0 .. 12)"] [V, "  stamp(eth)"])
#guard has (xdp ["  preserve pkt[0 .. 13)"] [V, "  stamp(eth)"])
  "the facts here do not entail it: `check` the offset, or narrow the clause"
#guard has (xdp ["  preserve pkt[0 .. 12)"] ["  pkt.adjust_tail(8)?"])
  "resizes the packet"
-- a variable offset with a fact behind it
#guard ok (xdp ["  preserve pkt[0 .. 14)"]
  ["  var off = 0", "  off = 14", "  let eth = pkt.view<EthHdr>(off)?",
   "  eth.proto = hton(0)"])
-- a marker's `fail` is the effect of the `else` its `try` carries
#guard progEffs (xdp [] [V]) "p" == some "{fail}"
#guard has (xdp ["  preserve pkt[0 .. 20)"]
  ["  let n = ctx.rx_queue_index as u64",
   "  let eth = pkt.view<EthHdr>(n)?", "  eth.proto = hton(0)"])
  "the facts here do not entail it"

-- maps and context fields
#guard has (xdp ["  preserve maps except stats"] ["  counters[0].n += 1"])
  "writes the map `counters`, which `preserve maps except stats` forbids"
#guard ok (xdp ["  preserve maps except stats"] ["  stats[0].n += 1"])
#guard has (xdp ["  preserve counters"] ["  let c = counters[0]", "  bump(c)"])
  "writes the map `counters`, which `preserve counters` forbids"
#guard ok (xdp ["  preserve counters"] ["  let c = stats[0]", "  bump(c)"])
#guard has (xdp ["  preserve counters"]
  ["  let c = counters[0]", "  let old = atomic_add(c.n, 1)"])
  "writes the map `counters`"
#guard has (lines (decls ++
  ["program t : tc", "  preserve ctx.mark", "  default { drop }",
   "{", "  ctx.mark = 1", "  drop", "}"]))
  "writes the context field `mark`, which `preserve ctx.mark` forbids"
-- a handler is part of the program
#guard has (lines (decls ++
  ["program p : xdp", "  preserve counters",
   "  on short_packet { counters[0].n += 1; drop }",
   "{", V, "  drop", "}"]))
  "writes the map `counters`"
