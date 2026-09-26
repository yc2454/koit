import Koit.Interface.Kernel

/-!
What the verifier decides per attach type, transcribed by hand from
the kernel's sources, since it is code there and not data: the range
a program's result must lie in at exit (`return_retval_range` in
kernel/bpf/verifier.c) and the context fields a program may read and
write (the `is_valid_access` callbacks of net/core/filter.c). The join
checks every kind declaration of the koit side against these: each
verdict value inside the range, each context field readable, each
writable field admitted. A program type these tables do not cover is
not checked, which is how the packet kinds, whose result the kernel
leaves free, pass through. The tables hold for `v6.8` and `v7.0-rc1`
alike; a tag that differs gets a table of its own.
-/

namespace Koit.Interface.Verifier

/-- What one attach type admits: the result's range and, per context
field, whether it is readable and writable. Fields not listed are
not accessible. -/
structure Rules where
  range    : Int × Int
  fields   : List (String × Bool × Bool)
  deriving Repr, Inhabited

/-- Readable only. -/
private def r (f : String) : String × Bool × Bool := (f, true, false)
/-- Readable and writable. -/
private def rw (f : String) : String × Bool × Bool := (f, true, true)

/-- `struct __sk_buff` in a cgroup skb program: `cg_skb_is_valid_access`
(net/core/filter.c), which admits the fields below, the packet's bounds
under `CAP_BPF`, and hides `tc_classid`, `data_meta`, `flow_keys`,
`wire_len`, and `tstamp_type`; `bpf_skb_is_valid_access` then admits the
stores to `cb`, `mark`, `priority`, and `tstamp`. -/
private def cgSkbFields : List (String × Bool × Bool) :=
  ["len", "pkt_type", "queue_mapping", "protocol", "vlan_present", "vlan_tci",
   "vlan_proto", "ingress_ifindex", "ifindex", "tc_index", "hash", "napi_id",
   "data", "data_end", "family", "remote_ip4", "local_ip4", "remote_ip6",
   "local_ip6", "remote_port", "local_port", "gso_segs", "gso_size", "sk",
   "hwtstamp"].map r ++ ["cb", "mark", "priority", "tstamp"].map rw

/-- `struct bpf_sock` in a cgroup sock program: `sock_filter_is_valid_access`
and `__sock_filter_check_attach_type` (net/core/filter.c): `bound_dev_if`,
`mark`, and `priority` on socket creation and release only, the source
address and port after `bind` only. -/
private def cgSockFields (attach : String) : List (String × Bool × Bool) :=
  ["family", "type", "protocol"].map r ++
  (match attach with
   | "BPF_CGROUP_INET_SOCK_CREATE" | "BPF_CGROUP_INET_SOCK_RELEASE" =>
     ["bound_dev_if", "mark", "priority"].map rw
   | "BPF_CGROUP_INET4_POST_BIND" => ["src_ip4", "src_port"].map r
   | "BPF_CGROUP_INET6_POST_BIND" => ["src_ip6", "src_port"].map r
   | _ => [])

/-- `struct bpf_sock_addr`: `sock_addr_is_valid_access` (net/core/filter.c).
The IPv4 address in the IPv4 hooks, the IPv6 address in the IPv6 hooks,
the port in every hook, all three writable; the message source address
in the UDP `sendmsg` hooks only; the family, type, protocol, and
socket read-only everywhere. -/
private def sockAddrFields (attach : String) : List (String × Bool × Bool) :=
  let v6 := attach.endsWith "6_BIND" || attach.endsWith "6_CONNECT" ||
            attach.endsWith "6_SENDMSG" || attach.endsWith "6_RECVMSG" ||
            attach.endsWith "6_GETPEERNAME" || attach.endsWith "6_GETSOCKNAME"
  ["user_family", "family", "type", "protocol", "sk"].map r ++
  [rw (if v6 then "user_ip6" else "user_ip4"), rw "user_port"] ++
  (match attach with
   | "BPF_CGROUP_UDP4_SENDMSG" => [rw "msg_src_ip4"]
   | "BPF_CGROUP_UDP6_SENDMSG" => [rw "msg_src_ip6"]
   | _ => [])

/-- The result range of `return_retval_range` (kernel/bpf/verifier.c):
[0, 1] by default for the cgroup types, [0, 3] for `cgroup_skb` egress
and the `bind` hooks, whose bit 1 carries a flag, and exactly 1 for the
hooks that run after the operation and cannot reject it. -/
private def sockAddrRange (attach : String) : Int × Int :=
  if attach.endsWith "_BIND" then (0, 3)
  else if attach.endsWith "_RECVMSG" || attach.endsWith "_GETPEERNAME" ||
          attach.endsWith "_GETSOCKNAME" then (1, 1)
  else (0, 1)

/-- The rules for a program type and attach type, when the tables
cover it. -/
def rules? (progType : String) (attach : Option String) : Option Rules :=
  match progType, attach with
  | "BPF_PROG_TYPE_CGROUP_SKB", some "BPF_CGROUP_INET_INGRESS" =>
    some { range := (0, 1), fields := cgSkbFields }
  | "BPF_PROG_TYPE_CGROUP_SKB", some "BPF_CGROUP_INET_EGRESS" =>
    some { range := (0, 3), fields := cgSkbFields }
  | "BPF_PROG_TYPE_CGROUP_SOCK", some a =>
    some { range := (0, 1), fields := cgSockFields a }
  | "BPF_PROG_TYPE_CGROUP_SOCK_ADDR", some a =>
    some { range := sockAddrRange a, fields := sockAddrFields a }
  | _, _ => none

end Koit.Interface.Verifier
