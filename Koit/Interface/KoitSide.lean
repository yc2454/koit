import Koit.Interface.Decls

/-!
The koit side of the interface, hand-written: how each kernel
operation is typed, and the name of the kernel object it corresponds
to. Nothing the kernel's sources state appears here, no helper number,
no offset, no verdict value, no `gpl_only`: those are the kernel side,
transcribed per tag under `Kernel/`, and `Join.lean` fills them in and
checks every correspondence against the kernel's own prototype. Every
declaration cites the kernel object it corresponds to. A unit's own
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
    verdicts := [("ABORTED", .kernel "XDP_ABORTED"), ("DROP", .kernel "XDP_DROP"),
                 ("PASS", .kernel "XDP_PASS"), ("TX", .kernel "XDP_TX"),
                 ("REDIRECT", .kernel "XDP_REDIRECT")],
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
    verdicts := [("OK", .kernel "TC_ACT_OK"), ("SHOT", .kernel "TC_ACT_SHOT"),
                 ("UNSPEC", .kernel "TC_ACT_UNSPEC"), ("PIPE", .kernel "TC_ACT_PIPE"),
                 ("REDIRECT", .kernel "TC_ACT_REDIRECT")],
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

/-! ### The cgroup kinds

One kind per hook: the kernel fixes the result's range and the
context table by the expected attach type, which libbpf derives from
the section name, so each section is a kind of its own with the
kernel's shared struct as its context (decision 70). The verdicts are
values the kernel never names, so they are given as numbers; the join
checks each against the range the verifier enforces for the hook.
The socket kinds have no `pass` or `drop`: nothing is dropped, a
rejected `connect` fails with `EPERM`. -/

/-- `struct __sk_buff` fields a cgroup skb program reads: those of the
socket the packet belongs to, with `mark` and `priority` writable;
the packet's bounds readable, the packet never written. -/
def cgroupSkbCtx : List CtxSpec :=
  [{ name := "len", ty := tU32, writable := false },
   { name := "mark", ty := tU32, writable := true },
   { name := "priority", ty := tU32, writable := true },
   { name := "protocol", ty := tU32, writable := false },
   { name := "ifindex", ty := tU32, writable := false },
   { name := "family", ty := tU32, writable := false },
   { name := "remote_ip4", ty := tBe32, writable := false },
   { name := "local_ip4", ty := tBe32, writable := false },
   { name := "remote_ip6", ty := .array noSpan tBe32 (.lit noSpan 4 "4"), writable := false },
   { name := "local_ip6", ty := .array noSpan tBe32 (.lit noSpan 4 "4"), writable := false },
   { name := "remote_port", ty := tU32, writable := false },
   { name := "local_port", ty := tU32, writable := false }]

/-- `cgroup_skb` ingress: [0, 1], a packet's fate. -/
def cgroupSkbIngressKind : KindSpec :=
  { name := "cgroup_skb_ingress", progType := "BPF_PROG_TYPE_CGROUP_SKB",
    section_ := "cgroup_skb/ingress", hasPkt := true, pktWritable := false,
    verdictTy := .named noSpan "SkbVerdict",
    verdictEnum := some { name := "SkbVerdict", kernel := "the range [0, 1]", width := 32 },
    verdicts := [("DROP", .value 0), ("PASS", .value 1)],
    sugar := [("pass", "PASS"), ("drop", "DROP")],
    defaultExit := .verdict "DROP", sleep := false,
    ctx := cgroupSkbCtx, ctxBounds := [("data", false), ("data_end", true)] }

/-- `cgroup_skb` egress: [0, 3], bit 1 the congestion notification. -/
def cgroupSkbEgressKind : KindSpec :=
  { cgroupSkbIngressKind with
    name := "cgroup_skb_egress", section_ := "cgroup_skb/egress",
    verdictTy := .named noSpan "EgressVerdict",
    verdictEnum := some { name := "EgressVerdict", kernel := "[0, 3]; bit 1 BPF_RET_SET_CN", width := 32 },
    verdicts := [("DROP", .value 0), ("PASS", .value 1), ("DROP_CN", .value 2), ("PASS_CN", .value 3)] }

def cgroupVerdictEnum : EnumSpec :=
  { name := "CgroupVerdict", kernel := "the range [0, 1]", width := 32 }

/-- A `cgroup/sock` hook over `struct bpf_sock`: 0 rejects, 1 allows. -/
def cgroupSockKind (name sec : String) (ctx : List CtxSpec) : KindSpec :=
  { name, progType := "BPF_PROG_TYPE_CGROUP_SOCK", section_ := sec,
    hasPkt := false, verdictTy := .named noSpan "CgroupVerdict",
    verdictEnum := some cgroupVerdictEnum,
    verdicts := [("REJECT", .value 0), ("ALLOW", .value 1)],
    sugar := [], defaultExit := .verdict "REJECT", sleep := false, ctx }

def sockCommonCtx : List CtxSpec :=
  [{ name := "family", ty := tU32, writable := false },
   { name := "type", ty := tU32, writable := false },
   { name := "protocol", ty := tU32, writable := false }]

/-- On creation and release the device, mark, and priority are set. -/
def sockCreateCtx : List CtxSpec :=
  sockCommonCtx ++
  [{ name := "bound_dev_if", ty := tU32, writable := true },
   { name := "mark", ty := tU32, writable := true },
   { name := "priority", ty := tU32, writable := true }]

def cgroupSockCreateKind := cgroupSockKind "cgroup_sock_create" "cgroup/sock_create" sockCreateCtx
def cgroupSockReleaseKind := cgroupSockKind "cgroup_sock_release" "cgroup/sock_release" sockCreateCtx
/-- After `bind`, the bound address and port are readable; the port is
in host order. -/
def cgroupPostBind4Kind := cgroupSockKind "cgroup_post_bind4" "cgroup/post_bind4"
  (sockCommonCtx ++ [{ name := "src_ip4", ty := tBe32, writable := false },
                     { name := "src_port", ty := tU32, writable := false }])
def cgroupPostBind6Kind := cgroupSockKind "cgroup_post_bind6" "cgroup/post_bind6"
  (sockCommonCtx ++ [{ name := "src_ip6", ty := .array noSpan tBe32 (.lit noSpan 4 "4"), writable := false },
                     { name := "src_port", ty := tU32, writable := false }])

/-- A `cgroup/sock_addr` hook over `struct bpf_sock_addr`: the address
the process gave, writable, in the family of the hook; `user_port` is
the port in network order in its low half; the message source address
in the UDP `sendmsg` hooks. -/
def sockAddrKind (name sec : String) (v6 sendmsg : Bool) (verdictTy : Ty) (en : EnumSpec)
    (verdicts : List (String × VerdictRef)) (dflt : String) : KindSpec :=
  let ip6 := Ty.array noSpan tBe32 (.lit noSpan 4 "4")
  { name, progType := "BPF_PROG_TYPE_CGROUP_SOCK_ADDR", section_ := sec,
    hasPkt := false, verdictTy, verdictEnum := some en, verdicts,
    sugar := [], defaultExit := .verdict dflt, sleep := false,
    ctx := [{ name := "user_family", ty := tU32, writable := false },
            (if v6 then { name := "user_ip6", ty := ip6, writable := true }
             else { name := "user_ip4", ty := tBe32, writable := true }),
            { name := "user_port", ty := tU32, writable := true }] ++
           sockCommonCtx ++
           (if !sendmsg then [] else if v6 then
              [{ name := "msg_src_ip6", ty := ip6, writable := true }]
            else [{ name := "msg_src_ip4", ty := tBe32, writable := true }]) }

def cgroupVerdict : Ty := .named noSpan "CgroupVerdict"
def allowReject : List (String × VerdictRef) := [("REJECT", .value 0), ("ALLOW", .value 1)]

/-- `bind`: [0, 3], bit 1 asks the kernel to skip the
`CAP_NET_BIND_SERVICE` check (`BPF_RET_BIND_NO_CAP_NET_BIND_SERVICE`);
2 is legal to the kernel and means a rejection with the flag, so it
has no name. -/
def bindVerdictEnum : EnumSpec :=
  { name := "BindVerdict", kernel := "[0, 3]; bit 1 BPF_RET_BIND_NO_CAP_NET_BIND_SERVICE", width := 32 }
def bindVerdicts : List (String × VerdictRef) :=
  allowReject ++ [("ALLOW_PRIVILEGED_PORT", .value 3)]

/-- The hooks that run after the operation: they may rewrite the
address the process sees and cannot reject, so 1 is the only verdict
and a failure leaves the address as the kernel had it. -/
def allowOnlyEnum : EnumSpec := { name := "AllowOnly", kernel := "exactly 1", width := 32 }
def allowOnly : List (String × VerdictRef) := [("ALLOW", .value 1)]

def sockAddrKinds : List KindSpec :=
  [sockAddrKind "cgroup_bind4" "cgroup/bind4" false false (.named noSpan "BindVerdict") bindVerdictEnum bindVerdicts "REJECT",
   sockAddrKind "cgroup_bind6" "cgroup/bind6" true false (.named noSpan "BindVerdict") bindVerdictEnum bindVerdicts "REJECT",
   sockAddrKind "cgroup_connect4" "cgroup/connect4" false false cgroupVerdict cgroupVerdictEnum allowReject "REJECT",
   sockAddrKind "cgroup_connect6" "cgroup/connect6" true false cgroupVerdict cgroupVerdictEnum allowReject "REJECT",
   sockAddrKind "cgroup_sendmsg4" "cgroup/sendmsg4" false true cgroupVerdict cgroupVerdictEnum allowReject "REJECT",
   sockAddrKind "cgroup_sendmsg6" "cgroup/sendmsg6" true true cgroupVerdict cgroupVerdictEnum allowReject "REJECT",
   sockAddrKind "cgroup_recvmsg4" "cgroup/recvmsg4" false false (.named noSpan "AllowOnly") allowOnlyEnum allowOnly "ALLOW",
   sockAddrKind "cgroup_recvmsg6" "cgroup/recvmsg6" true false (.named noSpan "AllowOnly") allowOnlyEnum allowOnly "ALLOW",
   sockAddrKind "cgroup_getpeername4" "cgroup/getpeername4" false false (.named noSpan "AllowOnly") allowOnlyEnum allowOnly "ALLOW",
   sockAddrKind "cgroup_getpeername6" "cgroup/getpeername6" true false (.named noSpan "AllowOnly") allowOnlyEnum allowOnly "ALLOW",
   sockAddrKind "cgroup_getsockname4" "cgroup/getsockname4" false false (.named noSpan "AllowOnly") allowOnlyEnum allowOnly "ALLOW",
   sockAddrKind "cgroup_getsockname6" "cgroup/getsockname6" true false (.named noSpan "AllowOnly") allowOnlyEnum allowOnly "ALLOW"]

def cgroupKinds : List KindSpec :=
  [cgroupSkbIngressKind, cgroupSkbEgressKind, cgroupSockCreateKind, cgroupSockReleaseKind,
   cgroupPostBind4Kind, cgroupPostBind6Kind] ++ sockAddrKinds

/-! ### Calls -/

/-- `redirect(ifindex)` yields `{v: verdict | v == REDIRECT}`: the
verdict type of the kind it is called in, since `xdp` and `tc` have
different ones. -/
def redirectRet : Ty :=
  .refined noSpan "v" (.named noSpan "verdict")
    (.cmp noSpan .eq (.var noSpan "v") (.var noSpan "REDIRECT"))

def sockTuple : Ty := .ref noSpan (.named noSpan "SockTuple")
def ownSock : Ty := .own noSpan (.named noSpan "Sock")
def refSock : Ty := .ref noSpan (.named noSpan "Sock")
def refTcpSock : Ty := .ref noSpan (.named noSpan "TcpSock")

/-- The calls. A layout lists the kernel's arguments in terms of
koit's: `.arg i` is koit's `i`-th argument, `.ctx` the context,
`.argSize i` the byte size of the `i`-th argument's place, `.const k`
a constant the source does not name, typically the flags word every
helper takes last. -/
def callSpecs : List CallSpec := [
  { name := "redirect", sig := .fn [param "ifindex" tU32] (some redirectRet),
    effects := [.call, .fail], fails := some .failed_call, kinds := ["xdp", "tc"],
    link := .helper "redirect" [.arg 0, .const 0] },
  -- xdp and tc adjust the packet's head through different helpers
  { name := "pkt.adjust_head", sig := .fn [param "delta" tI32] none,
    effects := [.call, .resize, .fail], fails := some .failed_call, kinds := ["xdp", "tc"],
    link := .helper "xdp_adjust_head" [.ctx, .arg 0],
    linkByKind := [("tc", .helper "skb_change_head" [.ctx, .arg 0, .const 0])] },
  { name := "pkt.adjust_tail", sig := .fn [param "delta" tI32] none,
    effects := [.call, .resize, .fail], fails := some .failed_call, kinds := ["xdp", "tc"],
    link := .helper "xdp_adjust_tail" [.ctx, .arg 0],
    linkByKind := [("tc", .helper "skb_change_tail" [.ctx, .arg 0, .const 0])] },
  { name := "pkt.len", sig := .fn [] (some tU64), effects := [], kinds := ["xdp", "tc"],
    note := "data_end - data" },
  -- `m.insert(k, v)` and `m.delete(k)`: the map, then places of its
  -- key and value types; typed by rule, laid out by the machine
  { name := "insert", sig := .builtin, effects := [.call, .fail], fails := some .failed_call,
    note := "bpf_map_update_elem" },
  { name := "delete", sig := .builtin, effects := [.call, .fail], fails := some .failed_call,
    note := "bpf_map_delete_elem" },
  -- `rb.reserve<T>()` yields `own T`, bound by `hold`
  { name := "reserve", sig := .builtin, effects := [.call, .fail], fails := some .failed_call,
    acquires := some ⟨"ringbuf"⟩, note := "bpf_ringbuf_reserve" },
  -- the tuple, its size, `BPF_F_CURRENT_NETNS`, and no flags
  { name := "sk_lookup_tcp", sig := .fn [param "tuple" sockTuple] (some ownSock),
    effects := [.call, .fail], fails := some .not_found, acquires := some ⟨"sockref"⟩,
    kinds := ["xdp", "tc"],
    link := .helper "sk_lookup_tcp" [.ctx, .arg 0, .argSize 0, .const (-1), .const 0] },
  { name := "sk_lookup_udp", sig := .fn [param "tuple" sockTuple] (some ownSock),
    effects := [.call, .fail], fails := some .not_found, acquires := some ⟨"sockref"⟩,
    kinds := ["xdp", "tc"],
    link := .helper "sk_lookup_udp" [.ctx, .arg 0, .argSize 0, .const (-1), .const 0] },
  -- a consuming call: its parameter is a `move` sink
  { name := "sk_release", sig := .fn [param "sk" ownSock] none, effects := [.call],
    kinds := ["xdp", "tc"], link := .helper "sk_release" [.arg 0] },
  -- the socket casts: a second name for the socket, derived from it,
  -- nullable on its own, and never released through
  { name := "sk_fullsock", sig := .fn [param "sk" refSock] (some refSock),
    effects := [.call, .fail], fails := some .not_found, derivedFrom := some "sk",
    kinds := ["tc"], link := .helper "sk_fullsock" [.arg 0] },
  { name := "tcp_sock", sig := .fn [param "sk" refSock] (some refTcpSock),
    effects := [.call, .fail], fails := some .not_found, derivedFrom := some "sk",
    kinds := ["tc"], link := .helper "tcp_sock" [.arg 0] },
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
  -- Core forms, listed so that the interface names the whole vocabulary
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
a declaration whose function the tag lacks is dropped with that reason. -/
def resourceDecls : List ResourceDecl := [
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
    fails := some .failed_call, normalExit := "bpf_ringbuf_submit",
    abnormalExit := "bpf_ringbuf_discard", forbidden := [.sleep],
    nesting := .yes, guards := "" },
  { res := ⟨"sockref"⟩, describe := "a socket reference", acquirers := ["sk_lookup_tcp", "sk_lookup_udp"],
    arg := .call, yields := true, fails := some .not_found,
    normalExit := "bpf_sk_release", abnormalExit := "bpf_sk_release",
    forbidden := [.sleep], nesting := .yes, guards := "" }
]

/-! ### Region kinds -/

def regionDecls : List RegionDecl := [
  { name := "stack", dynamic := false, writable := true, initialized := true,
    guard := none,
    note := "locals and struct literals; frame size reported by the compiler" },
  { name := "map value", dynamic := false, writable := true,
    initialized := true, guard := none,
    note := "array slots and hash lookups; zero-filled; valid for the whole run" },
  { name := "ctx", dynamic := false, writable := false, initialized := true,
    guard := none, note := "fields per kind; writability per field" },
  -- `MAX_PACKET_OFF`, include/linux/filter.h: the largest offset the
  -- verifier admits for a packet pointer
  { name := "pkt", dynamic := true, writable := true, initialized := true,
    guard := some .layout, maxOffset := some 0xFFFF,
    note := "views; writable per kind; the layout token is dropped by `resize`" }
]

/-! ### Slot types -/

/-- `enum btf_field_type` and `btf_get_field_type`, kernel/bpf/btf.c;
stage 1 has the spin lock, whose size the join checks. -/
def slotDecls : List SlotDecl := [
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
def typeDecls : List TypeDecl := [
  { span := noSpan, name := "spinlock", ty := .slot noSpan "spinlock" },
  { span := noSpan, name := "XdpAction", ty := .enum noSpan "XdpAction" },
  { span := noSpan, name := "TcAction", ty := .enum noSpan "TcAction" },
  -- the cgroup kinds' verdict types, values the kernel never names
  { span := noSpan, name := "SkbVerdict", ty := .enum noSpan "SkbVerdict" },
  { span := noSpan, name := "EgressVerdict", ty := .enum noSpan "EgressVerdict" },
  { span := noSpan, name := "CgroupVerdict", ty := .enum noSpan "CgroupVerdict" },
  { span := noSpan, name := "BindVerdict", ty := .enum noSpan "BindVerdict" },
  { span := noSpan, name := "AllowOnly", ty := .enum noSpan "AllowOnly" },
  { span := noSpan, name := "Sock", ty := .struct noSpan [] },
  -- `struct bpf_tcp_sock`, read through `tcp_sock`; the kernel admits
  -- loads from its fields and no store
  { span := noSpan, name := "TcpSock", readOnly := true,
    ty := .struct noSpan [field "snd_cwnd" tU32, field "srtt_us" tU32, field "rtt_min" tU32,
                          field "snd_ssthresh" tU32, field "rcv_nxt" tU32, field "snd_nxt" tU32,
                          field "snd_una" tU32, field "mss_cache" tU32, field "ecn_flags" tU32,
                          field "rate_delivered" tU32, field "rate_interval_us" tU32,
                          field "packets_out" tU32, field "retrans_out" tU32,
                          field "total_retrans" tU32, field "segs_in" tU32,
                          field "data_segs_in" tU32, field "segs_out" tU32,
                          field "data_segs_out" tU32, field "lost_out" tU32,
                          field "sacked_out" tU32, field "bytes_received" tU64,
                          field "bytes_acked" tU64] },
  { span := noSpan, name := "SockTuple",
    ty := .struct noSpan [field "saddr" tBe32, field "daddr" tBe32,
                          field "sport" tBe16, field "dport" tBe16] }
]

/-- The koit side, for every kernel tag. -/
def koitSide : Spec :=
  { kinds := [xdpKind, tcKind, syscallKind] ++ cgroupKinds, calls := callSpecs,
    resources := resourceDecls, regions := regionDecls, slots := slotDecls,
    enums := [], consts := constSpecs, types := typeDecls }

end Koit.Interface
