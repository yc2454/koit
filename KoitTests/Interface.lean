import Koit.Interface.Interface
import Koit.Interface.Print
import Koit.Syntax.Parser
import Koit.Core.Desugar
import Koit.Check.Decl

/-!
Checks on the kernel interface: the join of the koit side with each
transcribed kernel side, its disagreements as build errors, the rows
a tag lacks, the printout, and the diagnostics that name the kernel.
-/

open Koit Koit.Interface Koit.Core Koit.Check

/-- The join's verdict on a spec against v6.8: `none` when it fits,
else its disagreements. -/
private def verdict (spec : Spec) : Option String :=
  match join spec Kernel.v6_8 builtinLayouts with
  | .ok _ => none
  | .error e => some e

private def hasLine (s : Option String) (frag : String) : Bool :=
  match s with
  | some l => (l.splitOn frag).length > 1
  | none => false

private def withCall (c : CallSpec) : Spec :=
  { koitSide with calls := koitSide.calls ++ [c] }

-- the hand-written side fits both tags
#guard verdict koitSide == none
#guard (join koitSide Kernel.v7_0_rc1 builtinLayouts).toOption.isSome

-- every hand-typed number of stage 1 came back from the kernel side
#guard (v6_8.call? "redirect").map (·.impl) |>.any fun i => match i with
  | .helper 23 [.arg 0, .const 0] => true | _ => false
#guard (v6_8.call? "pkt.adjust_head").map (·.implIn "tc") |>.any fun i => match i with
  | .helper 43 _ => true | _ => false
#guard (v6_8.kind? "tc").map (·.ctx.map fun f => (f.name, f.offset)) ==
  some [("mark", 8), ("priority", 32), ("ifindex", 40)]
#guard (v6_8.kind? "tc").map (·.verdicts.lookup "UNSPEC") == some (some 0xFFFFFFFF)
#guard v6_8.helperId? "trace_printk" == some 6

-- the kernel side, not the hand, says what is GPL-only
#guard (v6_8.call? "ktime").map (·.gplOnly) == some false
#guard (v6_8.call? "printk").map (·.gplOnly) == some true

-- rows a tag lacks are dropped with the reason, not errors
#guard v6_8.missing? "preempt" == some "v6.8 has no bpf_preempt_disable"
#guard v6_8.missing? "irq_off" == some "v6.8 has no bpf_local_irq_save"
#guard (v6_8.resource? ⟨"irq"⟩).isNone
#guard (v7_0_rc1.resource? ⟨"irq"⟩).isSome
#guard v7_0_rc1.missing? "preempt" == none

-- a helper the tag has but a kind may not call
#guard hasLine (verdict (withCall
  { name := "fib", sig := .fn [] none, effects := [.call],
    link := .helper "fib_lookup" [.ctx, .const 0, .const 0, .const 0] }))
  "bpf_fib_lookup is not available to syscall"
-- the layout's arity against the prototype
#guard hasLine (verdict (withCall
  { name := "rd", sig := .fn [param "i" tU32] none, effects := [.call], kinds := ["xdp"],
    link := .helper "redirect" [.arg 0] })) "the layout has 1 arguments; bpf_xdp_redirect_proto takes 2"
-- a scalar where the verifier wants the context
#guard hasLine (verdict (withCall
  { name := "ah", sig := .fn [param "d" tI32] none, effects := [.call, .resize], kinds := ["xdp"],
    link := .helper "xdp_adjust_head" [.arg 0, .const 0] })) "asks for the context"
-- a place where the verifier wants a scalar
#guard hasLine (verdict (withCall
  { name := "rd2", sig := .fn [param "t" (.ref noSpan (.named noSpan "SockTuple"))] none,
    effects := [.call], kinds := ["xdp"], link := .helper "redirect" [.arg 0, .const 0] }))
  "asks for a scalar"
-- the resize effect against the kernel's packet-changing list
#guard hasLine (verdict (withCall
  { name := "ah2", sig := .fn [param "d" tI32] none, effects := [.call], kinds := ["xdp"],
    link := .helper "xdp_adjust_head" [.ctx, .arg 0] })) "no `resize` effect"
#guard hasLine (verdict (withCall
  { name := "kt", sig := .fn [] (some tU64), effects := [.call, .resize],
    link := .helper "ktime_get_ns" [] })) "does not list bpf_ktime_get_ns as changing the packet"
-- a helper the tag lacks is dropped, not an error
private def withNx : Spec := withCall
  { name := "nx", sig := .fn [] none, effects := [.call], link := .helper "no_such_helper" [] }
#guard (join withNx Kernel.v6_8 builtinLayouts).toOption.any
  fun i => i.missing? "nx" == some "v6.8 has no helper bpf_no_such_helper"
-- a kind's section must be one libbpf maps to its program type
#guard hasLine (verdict { koitSide with kinds := koitSide.kinds.map (fun k =>
    if k.name == "xdp" then { k with section_ := "xdp/nowhere" } else k) })
  "section \"xdp/nowhere\" is not one libbpf maps to BPF_PROG_TYPE_XDP"
-- a context field with the wrong width
#guard hasLine (verdict { koitSide with kinds := koitSide.kinds.map (fun k =>
    if k.name == "xdp" then { k with ctx := [{ name := "ingress_ifindex", ty := tU16, writable := false }] }
    else k) }) "is 4 bytes in struct xdp_md, typed `u16`"

-- the printout
private def doc6 : String := v6_8.doc
private def hasDoc (line : String) : Bool := (doc6.splitOn line).length > 1
#guard hasDoc "kind xdp : section \"xdp\", pkt rw, verdicts { ABORTED DROP PASS TX REDIRECT },"
#guard hasDoc "  ctx mark     : u32  writable"
#guard hasDoc "fn sk_lookup_tcp(tuple: ref SockTuple) -> own Sock\n     effects { call, fail } fails missing acquires sockref in xdp, tc"
#guard hasDoc "builtin printk  effects { call } gpl  // bpf_trace_printk"
#guard (doc6.splitOn "\n").all (·.length ≤ 80)
#guard hasDoc "// preempt: v6.8 has no bpf_preempt_disable"
#guard (v7_0_rc1.doc.splitOn "absent on").length == 1
-- with a kind, only what it sees; no number or offset anywhere
#guard ((v6_8.doc (some "syscall")).splitOn "sk_lookup").length == 1
#guard ((v6_8.doc (some "syscall")).splitOn "builtin insert").length == 2
#guard (doc6.splitOn " 84").length == 1 && (doc6.splitOn "offset").length == 2

-- the diagnostics name the kernel
private def chk (pre : Interface) (s : String) : Option String :=
  match Syntax.parse s with
  | .error e => some s!"parse: {e.msg}"
  | .ok u =>
    match checkUnit pre (desugar pre u) with
    | .ok _ => none
    | .error d => some d.msg
private def has (pre : Interface) (s frag : String) : Bool :=
  match chk pre s with
  | some m => (m.splitOn frag).length > 1
  | none => false
#guard has v6_8 "program p : syscall {\n  hold preempt_off { let x = 1 }\n  return 0\n}\n"
  "`preempt_off` is not on kernel v6.8: v6.8 has no bpf_preempt_disable"
#guard chk v7_0_rc1 "program p : syscall {\n  hold preempt_off { let x = 1 }\n  return 0\n}\n" == none
#guard has v6_8 "program p : syscall {\n  hold nothing { let x = 1 }\n  return 0\n}\n"
  "not a resource acquisition on kernel v6.8: the rows of the resource table are `lock(p)`, `rcu`, `rb.reserve<T>()`"
#guard has v6_8 "program p : syscall {\n  let r = get_prandom_u32()\n  return 0\n}\n"
  "is the kernel's helper bpf_get_prandom_u32, which koit has no row for yet"
#guard has v6_8 "program p : xdp fail pass {\n  hold rcu { let x = bpf_rcu_read_lock() }\n  pass\n}\n"
  "is a kfunc of the kernel, which koit has no row for yet"
#guard has v6_8 "program p : syscall {\n  let r = redirect(1)?\n  return 0\n}\n"
  "is not available in a `syscall` program on kernel v6.8; it is available in `xdp`, `tc`"
#guard has v6_8 "program p : xdp fail pass {\n  ctx.ingress_ifindex = 1\n  pass\n}\n"
  "is not writable in an `xdp` program; none of its fields is"
#guard has v6_8 "program p : tc fail pass {\n  ctx.priority = 1\n  pass\n}\n"
  "the writable fields are mark"
