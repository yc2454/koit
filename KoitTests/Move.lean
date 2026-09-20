import Koit.Syntax.Parser
import Koit.Core.Desugar
import Koit.Check.Decl
import Koit.Interface.Interface

/-!
Checks on ownership: `move` consumes its name on the path, the two
sides of a join agree on what is moved, and a loop's head agrees with
every path back to it or out of it.
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

private def decls : List String :=
  ["map tuples : array[1] of SockTuple",
   "fn half(a: u32) -> u32? { if a == 0 { return }; return a / 2 }"]

/-- An `xdp` program holding a socket reference `sk` around `body`. -/
private def held (body : List String) : String :=
  lines (decls ++ ["program p : xdp fail pass {", "  let t = tuples[0]",
                   "  let keep = ctx.ingress_ifindex == 2", "  var count = 0",
                   "  hold sk = sk_lookup_tcp(t)? {"] ++ body ++
         ["  }", "  pass", "}"])

-- a move on every path, or on none
#guard ok (held ["    sk_release(move sk)"])
#guard ok (held ["    count = 1"])
#guard ok (held ["    if keep { sk_release(move sk) } else { sk_release(move sk) }"])
-- a path that exits contributes nothing to the join
#guard ok (held ["    if keep { sk_release(move sk); pass }", "    count = 1"])
#guard ok (held ["    if keep { sk_release(move sk); return PASS }",
                 "    count = 1"])

-- the join of a conditional
#guard has (held ["    if keep { sk_release(move sk) }", "    count = 1"])
  "`sk` moved on one branch and held on the other at this join (`move sk` at line 8)"
#guard has (held ["    if keep { count = 1 } else { sk_release(move sk) }"])
  "moved on one branch and held on the other"
-- the join of `if let`
#guard has (held ["    if let h = half(count as u32) { sk_release(move sk) } \
                    else { count = 1 }"])
  "moved on one branch and held on the other"
#guard ok (held ["    if let h = half(count as u32) { sk_release(move sk) } \
                   else { sk_release(move sk) }"])
-- a dead branch does not join
#guard ok (held ["    if count == 0 { sk_release(move sk) }"])

-- the name is dead after `move`
#guard has (held ["    sk_release(move sk)", "    sk_release(move sk)"])
  "`sk` was moved at line 8 and is dead after it"
#guard has (held ["    if keep { sk_release(move sk); count = 1 } \
                    else { sk_release(move sk) }",
                  "    sk_release(move sk)"])
  "was moved at line"

-- loops: a name bound outside is moved only on a path that leaves
#guard has (held ["    repeat 2 { sk_release(move sk) }"])
  "`sk` moved inside the loop (`move sk` at line 8) and held at the loop head, so the next iteration would find it moved"
#guard has (held ["    repeat 2 { if keep { sk_release(move sk); break } }"])
  "so the code after the loop would find it moved"
#guard has (held ["    for i in 0..2 { if keep { sk_release(move sk); continue } }"])
  "so the next iteration would find it moved"
#guard ok (held ["    repeat 2 { if keep { sk_release(move sk); pass } }"])
-- a resource bound inside the loop is moved inside it
#guard ok (lines (decls ++
  ["program p : xdp fail pass {", "  let t = tuples[0]",
   "  repeat 2 { hold sk = sk_lookup_tcp(t)? { sk_release(move sk) } }",
   "  pass", "}"]))
