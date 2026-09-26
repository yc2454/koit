import Koit.Machine.Maps

/-!
The kernel parameter: what each kernel function the interface declares
does on its evaluated arguments, one of the relations the contracts
allow. Every semantics is stated for every kernel within its
contracts, `KernelOk`; the evaluators run the synthetic one below,
whose choices are recorded here.

A kernel receives what it would see through the registers: scalars,
the bytes a memory argument points at, and the objects it owns. It
answers with a value, a failure with the negative return the `helper`
reason defaults to, or an error the contract excludes. It changes
the shared state, the packet on a resize, an object it hands out,
its own clock, and never a level's private state.
-/

namespace Koit.Machine

open Koit.Core (Effect)
open Koit.Interface (KindDecl CallDecl)

/-- What a kernel function does when called. -/
inductive HelperOut where
  | ok (v : Option Val) (st : State)
  | failed (errno : Int) (st : State)
  | err (msg : String)
  deriving Inhabited

/-- A kernel: what each helper does on the evaluated arguments, in
the program kind that calls it, since a helper's answer can depend on
the kind, as `redirect`'s verdict does. -/
structure Kernel where
  helper : KindDecl → CallDecl → List Val → State → HelperOut

/-- The declarations the kernel computes inline, with no call: `pkt.len` is
the packet's length, `csum_add` the 32-bit add with end-around
carry, `csum_fold` the two folds and the complement, as
include/net/checksum.h has them. They are one function at every
level, with no trace event, since the kernel makes no call. -/
def inlineDecl (name : String) (args : List Val) (st : State) : Option Val :=
  match name, args.map Val.toInt with
  | "pkt.len", _ => some (.scalar st.packet.size)
  | "csum_add", [c, a] =>
    let a := toNatMod a 32
    let s := (toNatMod c 32 + a) % 2 ^ 32
    some (.scalar (if s < a then s + 1 else s))
  | "csum_fold", [c] =>
    let s := toNatMod c 32
    let s := (s % 65536) + (s / 65536)
    let s := (s % 65536) + (s / 65536)
    some (.scalar (65535 - (s % 65536)))
  | _, _ => none

/-- Whether a declaration's effect list has the flag `f`; the write effects
are not flags. -/
def hasFlag (es : List Effect) (f : Effect) : Bool :=
  es.any fun e =>
    match e, f with
    | .call, .call | .resize, .resize | .sleep, .sleep | .fail, .fail => true
    | _, _ => false

/-- A kernel within its contracts: a helper never errs, changes the
packet or its token only when its declaration has the `resize` effect,
yields a value exactly when its signature has a result, and fails
only when the declaration is fallible. -/
def KernelOk (K : Kernel) : Prop :=
  ∀ kind decl args st,
    (∀ m, K.helper kind decl args st ≠ .err m) ∧
    (∀ v st', K.helper kind decl args st = .ok v st' →
      (v.isSome ↔ ∃ params ret, decl.sig = .fn params (some ret)) ∧
      (hasFlag decl.effects .resize = false →
        st'.packet = st.packet ∧ st'.layout = st.layout)) ∧
    (∀ errno st', K.helper kind decl args st = .failed errno st' → decl.fails.isSome)

/-! ### The synthetic kernel -/

/-- A socket map's key as bytes: a sockmap's index as four bytes, a
sockhash's key as the bytes the kernel received. -/
def keyBytes : Val → List UInt8
  | .bytes bs => bs
  | v => leBytes (toNatMod v.toInt 32) 4

/-- The socket maps in the synthetic kernel: an update inserts the
context's socket, a fresh kernel object, under the key; a delete
removes the entry; a redirect passes when the key has a socket and
drops otherwise. -/
def socketMaps (kind : KindDecl) (name : String) (args : List Val) (st : State) :
    Option HelperOut :=
  let ofRc : Except String (Int × State) → HelperOut
    | .ok (0, st') => .ok none st'
    | .ok (rc, st') => .failed rc st'
    | .error e => .err e
  match name, args with
  | "sockmap_update", [.map m, key, _] | "sockhash_update", [.map m, key, _] =>
    let (id, st) := st.fresh
    let st := st.setRegion (.kernel id) ByteArray.empty
    some (ofRc ((update m (keyBytes key) (leBytes id 4)).exec st))
  | "sockmap_delete", [.map m, key] | "sockhash_delete", [.map m, key] =>
    some (ofRc ((delete m (keyBytes key)).exec st))
  | "msg_redirect", [.map m, key, _] | "sk_redirect", [.map m, key, _] =>
    let found := match st.maps.lookup m with
      | some ms => ms.entries.any (·.2.1 == keyBytes key)
      | none => false
    some (.ok (some (.scalar ((kind.verdicts.lookup (if found then "PASS" else "DROP")).getD 0))) st)
  | _, _ => none

/-- One behavior each helper of the stage-1 interface may have: a redirect
succeeds with the kind's `REDIRECT`; the resizes grow with zero bytes
and fail past the packet's end; a socket lookup finds a socket, and
the casts a full and a TCP socket with zeroed fields; the
clock advances a microsecond per call. The inline declarations never reach a
kernel. -/
def synthetic : Kernel where
  helper kind decl args st :=
    match socketMaps kind decl.name args st with
    | some out => out
    | none =>
    let ints := args.map Val.toInt
    match decl.name, ints with
    | "redirect", _ =>
      .ok (some (.scalar ((kind.verdicts.lookup "REDIRECT").getD 0))) st
    | "pkt.adjust_head", [delta] =>
      if delta ≤ 0 then
        let grown := ByteArray.mk ((Array.replicate delta.natAbs (0 : UInt8)) ++ st.packet.data)
        .ok none { st with packet := grown, layout := st.layout + 1 }
      else if delta.toNat > st.packet.size then .failed (-22) st
      else
        .ok none { st with packet := st.packet.extract delta.toNat st.packet.size,
                            layout := st.layout + 1 }
    | "pkt.adjust_tail", [delta] =>
      if delta ≥ 0 then
        let grown := ByteArray.mk (st.packet.data ++ Array.replicate delta.toNat (0 : UInt8))
        .ok none { st with packet := grown, layout := st.layout + 1 }
      else if delta.natAbs > st.packet.size then .failed (-22) st
      else
        .ok none { st with packet := st.packet.extract 0 (st.packet.size - delta.natAbs),
                            layout := st.layout + 1 }
    | "sk_lookup_tcp", _ | "sk_lookup_udp", _ =>
      let (id, st) := st.fresh
      let st := st.setRegion (.kernel id) ByteArray.empty
      .ok (some (.object id)) st
    | "sk_release", _ => .ok none st
    -- the casts find a full socket and a TCP socket with zeroed fields,
    -- 96 bytes for `struct bpf_tcp_sock`
    | "sk_fullsock", _ =>
      let (id, st) := st.fresh
      let st := st.setRegion (.kernel id) ByteArray.empty
      .ok (some (.object id)) st
    | "tcp_sock", _ =>
      let (id, st) := st.fresh
      let st := st.setRegion (.kernel id) (ByteArray.mk (Array.replicate 96 (0 : UInt8)))
      .ok (some (.object id)) st
    | "ktime", _ =>
      let st := { st with clock := st.clock + 1000 }
      .ok (some (.scalar st.clock)) st
    | f, _ => .err s!"the synthetic kernel has no rule for `{f}`"

end Koit.Machine
