import Koit.Prelude.Tables

/-!
The stage-1 prelude, hand-written for `xdp`, `tc`, and `syscall` and
for the helpers the corpus calls, transcribed from upstream v7.0. Every
row cites the kernel object it transcribes. A unit's own declarations
shadow prelude names; the prelude is the outer scope.
-/

namespace Koit.Prelude

open Koit (Span)
open Koit.Core

/-! ### Program kinds and context fields -/

/-- `enum xdp_action`, include/uapi/linux/bpf.h; `struct xdp_md` fields
per `xdp_is_valid_access`. -/
def xdpRow : KindRow :=
  { name := "xdp", section_ := "xdp", hasPkt := true, pktWritable := true,
    verdictTy := tU32,
    verdicts := [("ABORTED", 0), ("DROP", 1), ("PASS", 2), ("TX", 3),
                 ("REDIRECT", 4)],
    sugar := [("pass", "PASS"), ("drop", "DROP"), ("tx", "TX"),
              ("abort", "ABORTED")],
    defaultExit := .verdict "ABORTED", sleep := false,
    -- the offsets of `struct xdp_md`
    ctx := [{ name := "ingress_ifindex", ty := tU32, offset := 12, writable := false },
            { name := "rx_queue_index", ty := tU32, offset := 16, writable := false }],
    ctxBounds := [{ name := "data", offset := 0, isEnd := false },
                  { name := "data_end", offset := 4, isEnd := true }] }

/-- `TC_ACT_*`, include/uapi/linux/pkt_cls.h; `UNSPEC` is -1 as a
`u32`. `struct __sk_buff` fields per `tc_cls_act_is_valid_access`, of
which `mark` is writable. -/
def tcRow : KindRow :=
  { name := "tc", section_ := "tc", hasPkt := true, pktWritable := true,
    verdictTy := tU32,
    verdicts := [("OK", 0), ("SHOT", 2), ("UNSPEC", 0xFFFFFFFF),
                 ("PIPE", 3), ("REDIRECT", 7)],
    sugar := [("pass", "OK"), ("drop", "SHOT")],
    defaultExit := .verdict "SHOT", sleep := false,
    -- the offsets of `struct __sk_buff`
    ctx := [{ name := "mark", ty := tU32, offset := 8, writable := true },
            { name := "priority", ty := tU32, offset := 32, writable := false },
            { name := "ifindex", ty := tU32, offset := 40, writable := false }],
    ctxBounds := [{ name := "data", offset := 76, isEnd := false },
                  { name := "data_end", offset := 80, isEnd := true }] }

/-- `BPF_PROG_TYPE_SYSCALL`: no packet, an `i32` result, opaque
context, sleepable. -/
def syscallRow : KindRow :=
  { name := "syscall", section_ := "syscall", hasPkt := false,
    verdictTy := tI32, verdicts := [], sugar := [],
    defaultExit := .value (-1), sleep := true, ctx := [] }

/-! ### Calls -/

/-- `redirect(ifindex)` yields `{v | v == REDIRECT}`. -/
def redirectRet : Ty :=
  .refined noSpan "v" tU32
    (.cmp noSpan .eq (.var noSpan "v") (.var noSpan "REDIRECT"))

def callRows : List CallRow := [
  -- the helper numbers and argument layouts are the uapi header's;
  -- a constant is the flags word every helper takes last
  callRow "redirect" (.fn [param "ifindex" tU32] (some redirectRet))
    [.call, .fail] "bpf_redirect" (fails := some .helper)
    (kinds := ["xdp", "tc"]) (impl := .helper 23 [.arg 0, .const 0]),
  callRow "pkt.adjust_head" (.fn [param "delta" tI32] none)
    [.call, .resize, .fail] "bpf_xdp_adjust_head, bpf_skb_change_head"
    (fails := some .helper) (kinds := ["xdp", "tc"])
    (impl := .helper 44 [.ctx, .arg 0])
    (implByKind := [("tc", .helper 43 [.ctx, .arg 0, .const 0])]),
  callRow "pkt.adjust_tail" (.fn [param "delta" tI32] none)
    [.call, .resize, .fail] "bpf_xdp_adjust_tail, bpf_skb_change_tail"
    (fails := some .helper) (kinds := ["xdp", "tc"])
    (impl := .helper 65 [.ctx, .arg 0])
    (implByKind := [("tc", .helper 38 [.ctx, .arg 0, .const 0])]),
  callRow "pkt.len" (.fn [] (some tU64)) [] "data_end - data"
    (kinds := ["xdp", "tc"]),
  -- `m.insert(k, v)` and `m.delete(k)`: the map, then places of its
  -- key and value types; typed by rule
  callRow "insert" .builtin [.call, .fail] "bpf_map_update_elem"
    (fails := some .helper),
  callRow "delete" .builtin [.call, .fail] "bpf_map_delete_elem"
    (fails := some .helper),
  -- `rb.reserve<T>()` yields `own T`, bound by `hold`
  callRow "reserve" .builtin [.call, .fail] "bpf_ringbuf_reserve"
    (fails := some .helper) (acquires := some ⟨"ringbuf"⟩),
  callRow "sk_lookup_tcp"
    (.fn [param "tuple" (.ref noSpan (.named noSpan "SockTuple"))]
      (some (.own noSpan (.named noSpan "Sock"))))
    [.call, .fail] "bpf_sk_lookup_tcp" (fails := some .missing)
    (acquires := some ⟨"sockref"⟩) (kinds := ["xdp", "tc"])
    -- the tuple, its size, `BPF_F_CURRENT_NETNS`, and no flags
    (impl := .helper 84 [.ctx, .arg 0, .argSize 0, .const (-1), .const 0]),
  callRow "sk_lookup_udp"
    (.fn [param "tuple" (.ref noSpan (.named noSpan "SockTuple"))]
      (some (.own noSpan (.named noSpan "Sock"))))
    [.call, .fail] "bpf_sk_lookup_udp" (fails := some .missing)
    (acquires := some ⟨"sockref"⟩) (kinds := ["xdp", "tc"])
    (impl := .helper 85 [.ctx, .arg 0, .argSize 0, .const (-1), .const 0]),
  -- a consuming call: its parameter is a `move` sink
  callRow "sk_release" (.fn [param "sk" (.own noSpan (.named noSpan "Sock"))]
    none) [.call] "bpf_sk_release" (kinds := ["xdp", "tc"])
    (impl := .helper 86 [.arg 0]),
  -- a format string and at most three scalar arguments
  callRow "printk" .builtin [.call] "bpf_trace_printk" (gplOnly := true),
  callRow "ktime" (.fn [] (some tU64)) [.call] "bpf_ktime_get_ns"
    (gplOnly := true) (impl := .helper 5 []),
  -- `copy(dst, src)` and `fill(dst, byte)` over places of one type
  callRow "copy" .builtin [] "memcpy of a typed extent",
  callRow "fill" .builtin [] "memset of a typed extent",
  callRow "csum_add" (.fn [param "csum" tU32, param "addend" tU32]
    (some tU32)) [] "inline arithmetic",
  callRow "csum_fold" (.fn [param "csum" tU32] (some tU16)) []
    "inline arithmetic",
  -- Core forms, listed so that the table names the whole vocabulary
  callRow "hton" .builtin [] "byte swap",
  callRow "ntoh" .builtin [] "byte swap",
  callRow "atomic_add" .builtin [] "BPF_ATOMIC BPF_ADD | BPF_FETCH",
  callRow "atomic_and" .builtin [] "BPF_ATOMIC BPF_AND | BPF_FETCH",
  callRow "atomic_or" .builtin [] "BPF_ATOMIC BPF_OR | BPF_FETCH",
  callRow "atomic_xor" .builtin [] "BPF_ATOMIC BPF_XOR | BPF_FETCH",
  callRow "atomic_xchg" .builtin [] "BPF_ATOMIC BPF_XCHG",
  callRow "atomic_cmpxchg" .builtin [] "BPF_ATOMIC BPF_CMPXCHG"
]

/-! ### Resources -/

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
stage 1 has the spin lock. -/
def slotRows : List SlotRow := [
  { name := "spinlock", kernel := "bpf_spin_lock", size := 4, align := 4,
    unique := true, homes := [.mapValue], namedBy := "`hold lock(p)`" }
]

/-! ### Constants and types -/

def constRow (name : String) (value : Expr) : ConstDecl :=
  { span := noSpan, name, ty := none, value }

def lit (n : Nat) : Expr := .lit noSpan n (toString n)

def hexLit (n : Nat) : Expr :=
  .lit noSpan n ("0x" ++ String.ofList ((Nat.toDigits 16 n).map Char.toUpper))

/-- Protocol and ethertype numbers, untyped so that they take the type
of each use like literals; the ethertypes are byte-order values. -/
def constRows : List ConstDecl := [
  constRow "IPPROTO_ICMP" (lit 1),
  constRow "IPPROTO_TCP" (lit 6),
  constRow "IPPROTO_UDP" (lit 17),
  constRow "IPPROTO_ICMPV6" (lit 58),
  constRow "ETH_P_IP" (.hton noSpan (hexLit 0x0800)),
  constRow "ETH_P_IPV6" (.hton noSpan (hexLit 0x86DD)),
  constRow "ETH_P_VLAN" (.hton noSpan (hexLit 0x8100)),
  constRow "ETH_ALEN" (lit 6)
]

/-- `Sock` is opaque; `SockTuple` is `struct bpf_sock_tuple`'s IPv4
member, the argument of the socket lookups. -/
def typeRows : List TypeDecl := [
  { span := noSpan, name := "spinlock", ty := .slot noSpan "spinlock" },
  { span := noSpan, name := "Sock", ty := .struct noSpan [] },
  { span := noSpan, name := "SockTuple",
    ty := .struct noSpan [field "saddr" tBe32, field "daddr" tBe32,
                          field "sport" tBe16, field "dport" tBe16] }
]

/-- The stage-1 prelude, transcribed from upstream v7.0. -/
def stage1 : Prelude :=
  { kernel := "v7.0", kinds := [xdpRow, tcRow, syscallRow], calls := callRows,
    resources := resourceRows, regions := regionRows, slots := slotRows,
    consts := constRows, types := typeRows }

end Koit.Prelude
