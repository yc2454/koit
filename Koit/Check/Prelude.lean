import Koit.Core.Syntax

/-!
The prelude, per spec/language.md sections 6 and 13 and spec/ISSUES.md
entry 5: the five tables a kernel version supplies to the core, as a
Lean value, hand-written for `xdp`, `tc`, and `syscall` and for the
helpers the corpus calls. The generator of sessions 5 to 8 emits a
value of the same type from the kernel's own sources; until then every
row cites the kernel object it transcribes, keyed by the upstream tag
recorded in spec/verifier-checks.md.

The five tables (mechanisms-draft3.md, E): program kinds; context
fields per kind; calls with signatures, effects, availability, and
license; resources (section 11.2); region kinds (section 7). The
constants section 6 names as prelude constants and the two socket
types of section 11.2 follow.

A unit's own declarations shadow prelude names; the prelude is the
outer scope (spec/ISSUES.md, entry 11).
-/

namespace Koit.Check

open Koit (Span)
open Koit.Core

/-- The span every prelude node carries: a prelude row has no source
position, and a diagnostic about one names the call site instead. -/
def noSpan : Span := Span.point Koit.Pos.origin

/-! ### Type shorthands -/

def tU8  : Ty := .int noSpan false 8
def tU16 : Ty := .int noSpan false 16
def tU32 : Ty := .int noSpan false 32
def tU64 : Ty := .int noSpan false 64
def tI32 : Ty := .int noSpan true 32
def tBe16 : Ty := .be noSpan 16
def tBe32 : Ty := .be noSpan 32

def field (name : String) (ty : Ty) : Field := .mk noSpan name ty none

def param (name : String) (ty : Ty) (pred : Option Expr := none) : Param :=
  { span := noSpan, name, ty, pred }

/-! ### Table 1, program kinds (section 13) -/

/-- What a program returns on a failure of a kind it has no handler
for (section 10.7). -/
inductive DefaultExit where
  | verdict (name : String)
  | value (v : Int)
  deriving Repr, Inhabited

/-- Table 2, one context field (section 13). -/
structure CtxField where
  name     : String
  ty       : Ty
  writable : Bool
  deriving Repr, Inhabited

structure KindRow where
  name    : String
  /-- The libbpf section name the lowering emits. -/
  section_ : String
  /-- Whether the packet region exists, so `pkt` is in scope. -/
  hasPkt  : Bool
  /-- The verdict type: `u32` restricted to `verdicts` for packet
  kinds, `i32` for `syscall`. -/
  verdictTy : Ty
  /-- The named verdicts with the values the kernel gives them. -/
  verdicts : List (String × Nat)
  /-- The verdict statements `pass`, `drop`, `tx`, `abort` as names
  in `verdicts`; a statement with no row is not available. -/
  sugar : List (String × String)
  defaultExit : DefaultExit
  sleep : Bool
  ctx : List CtxField
  deriving Repr, Inhabited

/-- `enum xdp_action`, include/uapi/linux/bpf.h; `struct xdp_md` fields
per `xdp_is_valid_access`. -/
def xdpRow : KindRow :=
  { name := "xdp", section_ := "xdp", hasPkt := true, verdictTy := tU32,
    verdicts := [("ABORTED", 0), ("DROP", 1), ("PASS", 2), ("TX", 3),
                 ("REDIRECT", 4)],
    sugar := [("pass", "PASS"), ("drop", "DROP"), ("tx", "TX"),
              ("abort", "ABORTED")],
    defaultExit := .verdict "ABORTED", sleep := false,
    ctx := [{ name := "ingress_ifindex", ty := tU32, writable := false },
            { name := "rx_queue_index", ty := tU32, writable := false }] }

/-- `TC_ACT_*`, include/uapi/linux/pkt_cls.h; `UNSPEC` is -1 as a
`u32`. `struct __sk_buff` fields per `tc_cls_act_is_valid_access`, of
which `mark` is writable. -/
def tcRow : KindRow :=
  { name := "tc", section_ := "tc", hasPkt := true, verdictTy := tU32,
    verdicts := [("OK", 0), ("SHOT", 2), ("UNSPEC", 0xFFFFFFFF),
                 ("PIPE", 3), ("REDIRECT", 7)],
    sugar := [("pass", "OK"), ("drop", "SHOT")],
    defaultExit := .verdict "SHOT", sleep := false,
    ctx := [{ name := "mark", ty := tU32, writable := true },
            { name := "priority", ty := tU32, writable := false },
            { name := "ifindex", ty := tU32, writable := false }] }

/-- `BPF_PROG_TYPE_SYSCALL`: no packet, an `i32` result, opaque
context, sleepable. -/
def syscallRow : KindRow :=
  { name := "syscall", section_ := "syscall", hasPkt := false,
    verdictTy := tI32, verdicts := [], sugar := [],
    defaultExit := .value (-1), sleep := true, ctx := [] }

/-! ### Table 3, calls (sections 8.3, 8.5, 16) -/

/-- How a call is typed: by a signature, or by a rule of the checker
keyed by the name, for the generic builtins of section 8.5 whose
types depend on their arguments. -/
inductive Sig where
  | fn (params : List Param) (ret : Option Ty)
  | builtin
  deriving Repr, Inhabited

structure CallRow where
  name : String
  sig  : Sig
  /-- The effects of section 12; the write effects of `copy`, `fill`,
  `insert`, `delete`, and the atomics are those of their place or map
  argument and are computed at the call. -/
  effects : List Effect
  /-- The failure kind when the call is fallible (section 8.3). -/
  fails : Option Kind
  /-- The resource the result must be bound to with `hold`. -/
  acquires : Option Resource
  /-- The program kinds where the call is available; empty means all. -/
  kinds : List String
  /-- `gpl_only` in the helper's `bpf_func_proto` (section 6). -/
  gplOnly : Bool
  /-- The kernel helper, kfunc, or instruction behind the call. -/
  kernel : String
  deriving Repr, Inhabited

def callRow (name : String) (sig : Sig) (effects : List Effect)
    (kernel : String) (fails : Option Kind := none)
    (acquires : Option Resource := none) (kinds : List String := [])
    (gplOnly : Bool := false) : CallRow :=
  { name, sig, effects, fails, acquires, kinds, gplOnly, kernel }

/-- `redirect(ifindex)` yields `{v | v == REDIRECT}` (section 14.1). -/
def redirectRet : Ty :=
  .refined noSpan "v" tU32
    (.cmp noSpan .eq (.var noSpan "v") (.var noSpan "REDIRECT"))

def calls : List CallRow := [
  callRow "redirect" (.fn [param "ifindex" tU32] (some redirectRet))
    [.call, .fail] "bpf_redirect" (fails := some .helper)
    (kinds := ["xdp", "tc"]),
  callRow "pkt.adjust_head" (.fn [param "delta" tI32] none)
    [.call, .resize, .fail] "bpf_xdp_adjust_head, bpf_skb_change_head"
    (fails := some .helper) (kinds := ["xdp", "tc"]),
  callRow "pkt.adjust_tail" (.fn [param "delta" tI32] none)
    [.call, .resize, .fail] "bpf_xdp_adjust_tail, bpf_skb_change_tail"
    (fails := some .helper) (kinds := ["xdp", "tc"]),
  callRow "pkt.len" (.fn [] (some tU64)) [] "data_end - data"
    (kinds := ["xdp", "tc"]),
  -- `m.insert(k, v)` and `m.delete(k)`: the map, then places of its
  -- key and value types; typed by rule
  callRow "insert" .builtin [.call, .fail] "bpf_map_update_elem"
    (fails := some .helper),
  callRow "delete" .builtin [.call, .fail] "bpf_map_delete_elem"
    (fails := some .helper),
  -- `rb.reserve<T>()` yields `own (ref T)`, bound by `hold`
  callRow "reserve" .builtin [.call, .fail] "bpf_ringbuf_reserve"
    (fails := some .helper) (acquires := some .ringbuf),
  callRow "sk_lookup_tcp"
    (.fn [param "tuple" (.ref noSpan (.named noSpan "SockTuple"))]
      (some (.own noSpan (.named noSpan "Sock"))))
    [.call, .fail] "bpf_sk_lookup_tcp" (fails := some .missing)
    (acquires := some .sockref) (kinds := ["xdp", "tc"]),
  callRow "sk_lookup_udp"
    (.fn [param "tuple" (.ref noSpan (.named noSpan "SockTuple"))]
      (some (.own noSpan (.named noSpan "Sock"))))
    [.call, .fail] "bpf_sk_lookup_udp" (fails := some .missing)
    (acquires := some .sockref) (kinds := ["xdp", "tc"]),
  -- a consuming call: its parameter is a `move` sink (section 11.5)
  callRow "sk_release" (.fn [param "sk" (.own noSpan (.named noSpan "Sock"))]
    none) [.call] "bpf_sk_release" (kinds := ["xdp", "tc"]),
  -- a format string and at most three scalar arguments
  callRow "printk" .builtin [.call] "bpf_trace_printk" (gplOnly := true),
  callRow "ktime" (.fn [] (some tU64)) [.call] "bpf_ktime_get_ns"
    (gplOnly := true),
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

/-! ### Table 4, resources (section 11.2) -/

inductive Nesting where
  | no | counted | lifo | yes
  deriving Repr, BEq, Inhabited

structure ResourceRow where
  res : Resource
  /-- The surface spellings that acquire it after `hold`. -/
  acquirers : List String
  /-- Whether the acquisition binds a name of type `own T`. -/
  yields : Bool
  fails : Option Kind
  normalExit : String
  abnormalExit : String
  /-- Effects forbidden while held; `sleep` is forbidden under every
  row (section 11.4). -/
  forbidden : List Effect
  /-- Whether another instance of the same resource may be held. -/
  nesting : Nesting
  guards : String
  deriving Repr, Inhabited

def resources : List ResourceRow := [
  { res := .spinlock, acquirers := ["lock"], yields := false, fails := none,
    normalExit := "bpf_spin_unlock", abnormalExit := "bpf_spin_unlock",
    forbidden := [.call, .resize, .sleep], nesting := .no,
    guards := "the allocation the lock lies in, for moved graph nodes" },
  { res := .rcu, acquirers := ["rcu"], yields := false, fails := none,
    normalExit := "bpf_rcu_read_unlock", abnormalExit := "bpf_rcu_read_unlock",
    forbidden := [.sleep], nesting := .counted,
    guards := "RCU-protected pointers, kernel-memory extension" },
  { res := .preempt, acquirers := ["preempt_off"], yields := false,
    fails := none, normalExit := "bpf_preempt_enable",
    abnormalExit := "bpf_preempt_enable", forbidden := [.sleep],
    nesting := .counted, guards := "" },
  { res := .irq, acquirers := ["irq_off"], yields := false, fails := none,
    normalExit := "bpf_local_irq_restore",
    abnormalExit := "bpf_local_irq_restore", forbidden := [.sleep],
    nesting := .lifo, guards := "" },
  { res := .ringbuf, acquirers := ["reserve"], yields := true,
    fails := some .helper, normalExit := "bpf_ringbuf_submit",
    abnormalExit := "bpf_ringbuf_discard", forbidden := [.sleep],
    nesting := .yes, guards := "" },
  { res := .sockref, acquirers := ["sk_lookup_tcp", "sk_lookup_udp"],
    yields := true, fails := some .missing, normalExit := "bpf_sk_release",
    abnormalExit := "bpf_sk_release", forbidden := [.sleep],
    nesting := .yes, guards := "" }
]

/-! ### Table 5, region kinds (sections 7 and 12) -/

structure RegionRow where
  name : String
  /-- Whether places in it are obtained statically or through views. -/
  dynamic : Bool
  guard : Option Guard
  note : String
  deriving Repr, Inhabited

def regions : List RegionRow := [
  { name := "stack", dynamic := false, guard := none,
    note := "locals and struct literals; frame size reported by the compiler" },
  { name := "map value", dynamic := false, guard := none,
    note := "array slots and hash lookups; valid for the whole run" },
  { name := "ctx", dynamic := false, guard := none,
    note := "fields per kind, table 2" },
  { name := "pkt", dynamic := true, guard := some .layout,
    note := "views; the layout token is dropped by `resize`" }
]

/-! ### Constants and types (sections 6, 11.2) -/

def constRow (name : String) (value : Expr) : ConstDecl :=
  { span := noSpan, name, ty := none, value }

def lit (n : Nat) : Expr := .lit noSpan n (toString n)

def hexLit (n : Nat) : Expr :=
  .lit noSpan n ("0x" ++ String.ofList ((Nat.toDigits 16 n).map Char.toUpper))

/-- Protocol and ethertype numbers, untyped so that they take the type
of each use like literals; the ethertypes are byte-order values. -/
def consts : List ConstDecl := [
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
member, the argument of the socket lookups (spec/ISSUES.md, entry 4
proposes it as the tuple's type). -/
def types : List TypeDecl := [
  { span := noSpan, name := "Sock", ty := .struct noSpan [] },
  { span := noSpan, name := "SockTuple",
    ty := .struct noSpan [field "saddr" tBe32, field "daddr" tBe32,
                          field "sport" tBe16, field "dport" tBe16] }
]

/-! ### The prelude value -/

structure Prelude where
  kernel    : String
  kinds     : List KindRow
  calls     : List CallRow
  resources : List ResourceRow
  regions   : List RegionRow
  consts    : List ConstDecl
  types     : List TypeDecl
  deriving Inhabited

namespace Prelude

def kind? (p : Prelude) (name : String) : Option KindRow :=
  p.kinds.find? (·.name == name)

def call? (p : Prelude) (name : String) : Option CallRow :=
  p.calls.find? (·.name == name)

def resource? (p : Prelude) (r : Resource) : Option ResourceRow :=
  p.resources.find? (·.res == r)

/-- The resource a surface acquirer such as `lock` or `sk_lookup_tcp`
denotes. -/
def acquirer? (p : Prelude) (name : String) : Option ResourceRow :=
  p.resources.find? (·.acquirers.contains name)

def const? (p : Prelude) (name : String) : Option ConstDecl :=
  p.consts.find? (·.name == name)

def type? (p : Prelude) (name : String) : Option TypeDecl :=
  p.types.find? (·.name == name)

end Prelude

/-- The stage-1 prelude, transcribed from upstream v7.0. -/
def prelude : Prelude :=
  { kernel := "v7.0", kinds := [xdpRow, tcRow, syscallRow], calls,
    resources, regions, consts, types }

end Koit.Check
