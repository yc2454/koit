import Koit.Interface.Rows

/-!
The koit side of the interface, hand-written: how each kernel
operation is typed, and the name of the kernel object it corresponds
to. Nothing the kernel's sources state appears here, no helper number,
no offset, no verdict value, no `gpl_only`: those are the kernel side,
transcribed per tag under `Kernel/`, and `Join.lean` fills them in and
checks every correspondence against the kernel's own prototype. Every
row cites the kernel object it corresponds to. A unit's own
declarations shadow interface names; the interface is the outer
scope.
-/

namespace Koit.Interface

open Koit (Span)
open Koit.Core

/-! ### Program kinds and context fields -/

/-- `enum xdp_action` for the verdicts; `struct xdp_md` fields per
`xdp_is_valid_access`, none writable. -/
def xdpKind : KindSpec :=
  { name := "xdp", progType := "BPF_PROG_TYPE_XDP", section_ := "xdp",
    hasPkt := true, pktWritable := true,
    verdictTy := .named noSpan "XdpAction",
    verdictEnum := some { name := "XdpAction", kernel := "enum xdp_action",
                          width := 32 },
    verdicts := [("ABORTED", "XDP_ABORTED"), ("DROP", "XDP_DROP"),
                 ("PASS", "XDP_PASS"), ("TX", "XDP_TX"),
                 ("REDIRECT", "XDP_REDIRECT")],
    sugar := [("pass", "PASS"), ("drop", "DROP"), ("tx", "TX"),
              ("abort", "ABORTED")],
    defaultExit := .verdict "ABORTED", sleep := false,
    ctx := [{ name := "ingress_ifindex", ty := tU32, writable := false },
            { name := "rx_queue_index", ty := tU32, writable := false }],
    ctxBounds := [("data", false), ("data_end", true)] }

/-- `TC_ACT_*` for the verdicts, `UNSPEC` being the kernel's -1 as a
`u32`; `struct __sk_buff` fields per `tc_cls_act_is_valid_access`,
of which `mark` is writable. -/
def tcKind : KindSpec :=
  { name := "tc", progType := "BPF_PROG_TYPE_SCHED_CLS", section_ := "tc",
    hasPkt := true, pktWritable := true,
    verdictTy := .named noSpan "TcAction",
    verdictEnum := some { name := "TcAction", kernel := "TC_ACT_*",
                          width := 32 },
    verdicts := [("OK", "TC_ACT_OK"), ("SHOT", "TC_ACT_SHOT"),
                 ("UNSPEC", "TC_ACT_UNSPEC"), ("PIPE", "TC_ACT_PIPE"),
                 ("REDIRECT", "TC_ACT_REDIRECT")],
    sugar := [("pass", "OK"), ("drop", "SHOT")],
    defaultExit := .verdict "SHOT", sleep := false,
    ctx := [{ name := "mark", ty := tU32, writable := true },
            { name := "priority", ty := tU32, writable := false },
            { name := "ifindex", ty := tU32, writable := false }],
    ctxBounds := [("data", false), ("data_end", true)] }

/-- `BPF_PROG_TYPE_SYSCALL`: no packet, an `i32` result, opaque
context, sleepable. -/
def syscallKind : KindSpec :=
  { name := "syscall", progType := "BPF_PROG_TYPE_SYSCALL", section_ := "syscall",
    hasPkt := false, verdictTy := tI32, verdicts := [], sugar := [],
    defaultExit := .value (-1), sleep := true, ctx := [] }

/-! ### Calls -/

/-- `redirect(ifindex)` yields `{v: verdict | v == REDIRECT}`: the
verdict type of the kind it is called in, since `xdp` and `tc` have
different ones. -/
def redirectRet : Ty :=
  .refined noSpan "v" (.named noSpan "verdict")
    (.cmp noSpan .eq (.var noSpan "v") (.var noSpan "REDIRECT"))

def sockTuple : Ty := .ref noSpan (.named noSpan "SockTuple")
def ownSock : Ty := .own noSpan (.named noSpan "Sock")

/-- The calls. A layout lists the kernel's arguments in terms of
koit's: `.arg i` is koit's `i`-th argument, `.ctx` the context,
`.argSize i` the byte size of the `i`-th argument's place, `.const k`
a constant the source does not name, typically the flags word every
helper takes last. -/
def callSpecs : List CallSpec := [
  { name := "redirect", sig := .fn [param "ifindex" tU32] (some redirectRet),
    effects := [.call, .fail], fails := some .helper, kinds := ["xdp", "tc"],
    link := .helper "redirect" [.arg 0, .const 0] },
  -- xdp and tc adjust the packet's head through different helpers
  { name := "pkt.adjust_head", sig := .fn [param "delta" tI32] none,
    effects := [.call, .resize, .fail], fails := some .helper, kinds := ["xdp", "tc"],
    link := .helper "xdp_adjust_head" [.ctx, .arg 0],
    linkByKind := [("tc", .helper "skb_change_head" [.ctx, .arg 0, .const 0])] },
  { name := "pkt.adjust_tail", sig := .fn [param "delta" tI32] none,
    effects := [.call, .resize, .fail], fails := some .helper, kinds := ["xdp", "tc"],
    link := .helper "xdp_adjust_tail" [.ctx, .arg 0],
    linkByKind := [("tc", .helper "skb_change_tail" [.ctx, .arg 0, .const 0])] },
  { name := "pkt.len", sig := .fn [] (some tU64), effects := [], kinds := ["xdp", "tc"],
    note := "data_end - data" },
  -- `m.insert(k, v)` and `m.delete(k)`: the map, then places of its
  -- key and value types; typed by rule, laid out by the machine
  { name := "insert", sig := .builtin, effects := [.call, .fail], fails := some .helper,
    note := "bpf_map_update_elem" },
  { name := "delete", sig := .builtin, effects := [.call, .fail], fails := some .helper,
    note := "bpf_map_delete_elem" },
  -- `rb.reserve<T>()` yields `own T`, bound by `hold`
  { name := "reserve", sig := .builtin, effects := [.call, .fail], fails := some .helper,
    acquires := some ⟨"ringbuf"⟩, note := "bpf_ringbuf_reserve" },
  -- the tuple, its size, `BPF_F_CURRENT_NETNS`, and no flags
  { name := "sk_lookup_tcp", sig := .fn [param "tuple" sockTuple] (some ownSock),
    effects := [.call, .fail], fails := some .missing, acquires := some ⟨"sockref"⟩,
    kinds := ["xdp", "tc"],
    link := .helper "sk_lookup_tcp" [.ctx, .arg 0, .argSize 0, .const (-1), .const 0] },
  { name := "sk_lookup_udp", sig := .fn [param "tuple" sockTuple] (some ownSock),
    effects := [.call, .fail], fails := some .missing, acquires := some ⟨"sockref"⟩,
    kinds := ["xdp", "tc"],
    link := .helper "sk_lookup_udp" [.ctx, .arg 0, .argSize 0, .const (-1), .const 0] },
  -- a consuming call: its parameter is a `move` sink
  { name := "sk_release", sig := .fn [param "sk" ownSock] none, effects := [.call],
    kinds := ["xdp", "tc"], link := .helper "sk_release" [.arg 0] },
  -- a format string and at most three scalar arguments
  { name := "printk", sig := .builtin, effects := [.call], note := "bpf_trace_printk" },
  { name := "ktime", sig := .fn [] (some tU64), effects := [.call],
    link := .helper "ktime_get_ns" [] },
  -- `copy(dst, src)` and `fill(dst, byte)` over places of one type
  { name := "copy", sig := .builtin, effects := [], note := "memcpy of a typed extent" },
  { name := "fill", sig := .builtin, effects := [], note := "memset of a typed extent" },
  { name := "csum_add", sig := .fn [param "csum" tU32, param "addend" tU32] (some tU32),
    effects := [], note := "inline arithmetic" },
  { name := "csum_fold", sig := .fn [param "csum" tU32] (some tU16), effects := [],
    note := "inline arithmetic" },
  -- Core forms, listed so that the table names the whole vocabulary
  { name := "hton", sig := .builtin, effects := [], note := "byte swap" },
  { name := "ntoh", sig := .builtin, effects := [], note := "byte swap" },
  { name := "atomic_add", sig := .builtin, effects := [], note := "BPF_ATOMIC BPF_ADD | BPF_FETCH" },
  { name := "atomic_and", sig := .builtin, effects := [], note := "BPF_ATOMIC BPF_AND | BPF_FETCH" },
  { name := "atomic_or", sig := .builtin, effects := [], note := "BPF_ATOMIC BPF_OR | BPF_FETCH" },
  { name := "atomic_xor", sig := .builtin, effects := [], note := "BPF_ATOMIC BPF_XOR | BPF_FETCH" },
  { name := "atomic_xchg", sig := .builtin, effects := [], note := "BPF_ATOMIC BPF_XCHG" },
  { name := "atomic_cmpxchg", sig := .builtin, effects := [], note := "BPF_ATOMIC BPF_CMPXCHG" }
]

/-! ### Resources -/

/-- The kernel functions named here are checked to exist on the tag;
a row whose function the tag lacks is dropped with that reason. -/
def resourceRows : List ResourceRow := [
  { res := ⟨"spinlock"⟩, describe := "a spin lock", acquirers := ["lock"], arg := .place "spinlock",
    yields := false, fails := none,
    normalExit := "bpf_spin_unlock", abnormalExit := "bpf_spin_unlock",
    forbidden := [.call, .resize, .sleep], nesting := .no,
    guards := "the allocation the lock lies in, for moved graph nodes" },
  { res := ⟨"rcu"⟩, describe := "an RCU section", acquirers := ["rcu"], arg := .scope, yields := false,
    acquireKernel := some "bpf_rcu_read_lock",
    fails := none, normalExit := "bpf_rcu_read_unlock",
    abnormalExit := "bpf_rcu_read_unlock", forbidden := [.sleep],
    nesting := .counted,
    guards := "RCU-protected pointers, kernel-memory extension" },
  { res := ⟨"preempt"⟩, describe := "a preempt-off section", acquirers := ["preempt_off"], arg := .scope,
    acquireKernel := some "bpf_preempt_disable",
    yields := false, fails := none, normalExit := "bpf_preempt_enable",
    abnormalExit := "bpf_preempt_enable", forbidden := [.sleep],
    nesting := .counted, guards := "" },
  { res := ⟨"irq"⟩, describe := "an IRQ-off section", acquirers := ["irq_off"], arg := .scope, yields := false,
    acquireKernel := some "bpf_local_irq_save",
    fails := none, normalExit := "bpf_local_irq_restore",
    abnormalExit := "bpf_local_irq_restore", forbidden := [.sleep],
    nesting := .lifo, guards := "" },
  { res := ⟨"ringbuf"⟩, describe := "a ring-buffer record", acquirers := ["reserve"], arg := .call, yields := true,
    fails := some .helper, normalExit := "bpf_ringbuf_submit",
    abnormalExit := "bpf_ringbuf_discard", forbidden := [.sleep],
    nesting := .yes, guards := "" },
  { res := ⟨"sockref"⟩, describe := "a socket reference", acquirers := ["sk_lookup_tcp", "sk_lookup_udp"],
    arg := .call, yields := true, fails := some .missing,
    normalExit := "bpf_sk_release", abnormalExit := "bpf_sk_release",
    forbidden := [.sleep], nesting := .yes, guards := "" }
]

/-! ### Region kinds -/

def regionRows : List RegionRow := [
  { name := "stack", dynamic := false, writable := true, initialized := true,
    guard := none,
    note := "locals and struct literals; frame size reported by the compiler" },
  { name := "map value", dynamic := false, writable := true,
    initialized := true, guard := none,
    note := "array slots and hash lookups; zero-filled; valid for the whole run" },
  { name := "ctx", dynamic := false, writable := false, initialized := true,
    guard := none, note := "fields per kind, table 2; writability per field" },
  -- `MAX_PACKET_OFF`, include/linux/filter.h: the largest offset the
  -- verifier admits for a packet pointer
  { name := "pkt", dynamic := true, writable := true, initialized := true,
    guard := some .layout, maxOffset := some 0xFFFF,
    note := "views; writable per kind; the layout token is dropped by `resize`" }
]

/-! ### Slot types -/

/-- `enum btf_field_type` and `btf_get_field_type`, kernel/bpf/btf.c;
stage 1 has the spin lock, whose size the join checks. -/
def slotRows : List SlotRow := [
  { name := "spinlock", kernel := "bpf_spin_lock", size := 4, align := 4,
    unique := true, homes := [.mapValue], namedBy := "`hold lock(p)`" }
]

/-! ### Constants and types -/

/-- Protocol and ethertype numbers by the kernel's names, untyped so
that they take the type of each use like literals; the ethertypes are
byte-order values. -/
def constSpecs : List ConstSpec := [
  { name := "IPPROTO_ICMP", kernel := "IPPROTO_ICMP" },
  { name := "IPPROTO_TCP", kernel := "IPPROTO_TCP" },
  { name := "IPPROTO_UDP", kernel := "IPPROTO_UDP" },
  { name := "IPPROTO_ICMPV6", kernel := "IPPROTO_ICMPV6" },
  { name := "ETH_P_IP", kernel := "ETH_P_IP", hton := true },
  { name := "ETH_P_IPV6", kernel := "ETH_P_IPV6", hton := true },
  { name := "ETH_P_VLAN", kernel := "ETH_P_8021Q", hton := true },
  { name := "ETH_ALEN", kernel := "ETH_ALEN" }
]

/-- `Sock` is opaque; `SockTuple` is `struct bpf_sock_tuple`'s IPv4
member, the argument of the socket lookups. -/
def typeRows : List TypeDecl := [
  { span := noSpan, name := "spinlock", ty := .slot noSpan "spinlock" },
  { span := noSpan, name := "XdpAction", ty := .enum noSpan "XdpAction" },
  { span := noSpan, name := "TcAction", ty := .enum noSpan "TcAction" },
  { span := noSpan, name := "Sock", ty := .struct noSpan [] },
  { span := noSpan, name := "SockTuple",
    ty := .struct noSpan [field "saddr" tBe32, field "daddr" tBe32,
                          field "sport" tBe16, field "dport" tBe16] }
]

/-- The koit side, for every kernel tag. -/
def koitSide : Spec :=
  { kinds := [xdpKind, tcKind, syscallKind], calls := callSpecs,
    resources := resourceRows, regions := regionRows, slots := slotRows,
    enums := [], consts := constSpecs, types := typeRows }

end Koit.Interface
