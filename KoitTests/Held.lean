import Koit.Syntax.Parser
import Koit.Core.Desugar
import Koit.Check.Decl
import Koit.Interface.Interface

/-!
Checks on the held set: the effects a row forbids while its resource
is held, through a function's summary too, and nesting per the row.
-/

open Koit Koit.Syntax Koit.Core Koit.Check

private def chk (s : String) : Except Diag Unit :=
  match parse s with
  | .error e => .error { span := e.span, msg := s!"parse: {e.msg}" }
  | .ok u =>
    (checkUnit Interface.v7_0_rc1 (desugar Interface.v7_0_rc1 u)).map fun _ => ()

private def ok (s : String) : Bool := (chk s).toOption.isSome

private def has (s frag : String) : Bool :=
  match chk s with
  | .ok () => false
  | .error d => (d.msg.splitOn frag).length > 1

private def lines (ls : List String) : String := "\n".intercalate ls

private def decls : List String :=
  ["license \"GPL\"",
   "type Ctr = { lk: spinlock, n: u64 }",
   "map counters : array[1] of Ctr",
   "map tuples : array[1] of SockTuple",
   "map events : ringbuf[4096]",
   "fn bump(c: ref Ctr) { c.n += 1 }",
   "fn now() -> u64 { ktime() }"]

private def xdp (body : List String) : String :=
  lines (decls ++ ["program p : xdp default { drop } {", "  let c = counters[0]",
                   "  let t = tuples[0]"] ++ body ++ ["  drop", "}"])

-- a spin lock forbids call and resize; a store and a function
-- without effects are fine
#guard ok (xdp ["  hold lock(c.lk) { c.n += 1; bump(c) }"])
#guard has (xdp ["  hold lock(c.lk) { printk(\"n\") }"])
  "the call effect is forbidden while a spin lock is held (`hold lock(c.lk)` at line 11)"
#guard has (xdp ["  hold lock(c.lk) { let x = now() }"])
  "the call effect is forbidden while a spin lock is held"
#guard has (xdp ["  hold lock(c.lk) { pkt.adjust_tail(8)? }"])
  "the call effect is forbidden while a spin lock is held"
#guard has (xdp ["  hold lock(c.lk) { if c.n == 0 { let x = now() } }"])
  "move it outside the block"
-- the acquisition itself is checked against the outer set
#guard has (xdp ["  hold lock(c.lk) { hold sk = sk_lookup_tcp(t)? { c.n += 1 } }"])
  "the call effect is forbidden while a spin lock is held"
-- the innermost holder is named
#guard has (xdp ["  hold rcu { hold lock(c.lk) { let x = now() } }"])
  "while a spin lock is held"
-- rows that forbid only sleep
#guard ok (xdp ["  hold rcu { let x = now() }"])
#guard ok (xdp ["  hold sk = sk_lookup_tcp(t)? { let x = now() }"])
#guard ok (xdp ["  hold ev = events.reserve<u64>()? { let x = now() }"])
-- the else block runs with nothing new held
#guard ok (xdp ["  hold sk = sk_lookup_tcp(t) else { let x = now(); drop } { c.n += 1 }"])
-- the set is restored after the block
#guard ok (xdp ["  hold lock(c.lk) { c.n += 1 }", "  let x = now()"])

-- nesting per the row
#guard has (xdp ["  hold lock(c.lk) { hold lock(c.lk) { c.n += 1 } }"])
  "a spin lock cannot be held inside another: `hold lock(c.lk)` at line 11 is still held"
#guard ok (xdp ["  hold rcu { hold rcu { c.n += 1 } }"])
#guard ok (xdp ["  hold rcu { hold lock(c.lk) { c.n += 1 } }"])
#guard ok (xdp ["  hold lock(c.lk) { hold rcu { c.n += 1 } }"])
