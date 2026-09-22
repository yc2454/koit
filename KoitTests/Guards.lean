import Koit.Syntax.Parser
import Koit.Core.Desugar
import Koit.Check.Decl
import Koit.Interface.Interface

/-!
Checks on guards: a view is dead after any statement that resizes
the packet, on every path through it, and a use is rejected naming
the statement.
-/

open Koit Koit.Syntax Koit.Core Koit.Check

private def chk (s : String) : Except Diag Unit :=
  match parse s with
  | .error e => .error { span := e.span, msg := s!"parse: {e.msg}" }
  | .ok u =>
    (checkUnit Interface.v6_8 (desugar Interface.v6_8 u)).map fun _ => ()

private def ok (s : String) : Bool := (chk s).toOption.isSome

private def has (s frag : String) : Bool :=
  match chk s with
  | .ok () => false
  | .error d => (d.msg.splitOn frag).length > 1

private def lines (ls : List String) : String := "\n".intercalate ls

/-- An `xdp` program with a view `eth` carved on line 4 before `body`. -/
private def xdp (body : List String) : String :=
  lines (["type EthHdr = { dst: u8[6], src: u8[6], proto: be16 }",
          "program p : xdp default { drop } {",
          "  let keep = ctx.ingress_ifindex == 2",
          "  let eth = pkt.view<EthHdr>(0)?"] ++ body ++ ["  drop", "}"])

-- the rejected program of the definition
#guard has (xdp ["  pkt.adjust_head(-8)?", "  let p = eth.proto"])
  "view `eth` was invalidated by `adjust_head` at line 5; carve it again after the resize"
#guard has (xdp ["  pkt.adjust_tail(8)?", "  eth.proto = hton(0)"])
  "invalidated by `adjust_tail` at line 5"
-- the operands of the resizing statement are read before it
#guard ok (xdp ["  pkt.adjust_head(eth.dst[0] as i32)?"])
-- a view carved after the resize is live
#guard ok (xdp ["  pkt.adjust_head(-8)?", "  let eth2 = pkt.view<EthHdr>(0)?",
                "  let p = eth2.proto"])
-- the `else` of the resizing statement sees the packet resized too
#guard has (xdp ["  pkt.adjust_head(-8) else { let p = eth.proto; drop }"])
  "invalidated by `adjust_head`"
-- a resize on one branch kills for the join; a branch that exits
-- contributes nothing
#guard has (xdp ["  if keep { pkt.adjust_tail(8)? }", "  let p = eth.proto"])
  "invalidated by `adjust_tail` at line 5"
#guard ok (xdp ["  if keep { pkt.adjust_tail(8)?; drop }", "  let p = eth.proto"])
-- a loop whose body resizes kills the views in scope at its head
#guard has (xdp ["  repeat 2 { let p = eth.proto; pkt.adjust_tail(1)? }"])
  "invalidated by `adjust_tail` at line 5"
#guard has (xdp ["  repeat 2 { pkt.adjust_tail(1)? }", "  let p = eth.proto"])
  "invalidated by `adjust_tail`"
-- a view carved inside the loop before the resize is used before it
#guard ok (xdp ["  repeat 2 { let h = pkt.view<EthHdr>(0)?", "    let p = h.proto",
                "    pkt.adjust_tail(1)? }"])
-- the view's block ends with it; a new view of the same name is live
#guard ok (xdp ["  if keep { let h = pkt.view<EthHdr>(0)?; pkt.adjust_tail(1)? }",
                "  if keep { let h = pkt.view<EthHdr>(0)?; let p = h.proto }"])
