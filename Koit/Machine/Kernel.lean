import Koit.Machine.State

/-!
The kernel parameter: what each kernel function of the call table
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
open Koit.Prelude (KindRow CallRow)

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
  helper : KindRow → CallRow → List Val → State → HelperOut

/-- Whether a row's effect list has the flag `f`; the write effects
are not flags. -/
def hasFlag (es : List Effect) (f : Effect) : Bool :=
  es.any fun e =>
    match e, f with
    | .call, .call | .resize, .resize | .sleep, .sleep | .fail, .fail => true
    | _, _ => false

/-- A kernel within its contracts: a helper never errs, changes the
packet or its token only when its row has the `resize` effect,
yields a value exactly when its signature has a result, and fails
only when the row is fallible. -/
def KernelOk (K : Kernel) : Prop :=
  ∀ kind row args st,
    (∀ m, K.helper kind row args st ≠ .err m) ∧
    (∀ v st', K.helper kind row args st = .ok v st' →
      (v.isSome ↔ ∃ params ret, row.sig = .fn params (some ret)) ∧
      (hasFlag row.effects .resize = false →
        st'.packet = st.packet ∧ st'.layout = st.layout)) ∧
    (∀ errno st', K.helper kind row args st = .failed errno st' → row.fails.isSome)

/-! ### The synthetic kernel -/

/-- One behavior each helper of the stage-1 table may have: a redirect
succeeds with the kind's `REDIRECT`; the resizes grow with zero bytes
and fail past the packet's end; a socket lookup finds a socket; the
clock advances a microsecond per call; the checksums are the
kernel's own `csum_add` and `csum_fold`. -/
def synthetic : Kernel where
  helper kind row args st :=
    let ints := args.map Val.toInt
    match row.name, ints with
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
    | "pkt.len", _ => .ok (some (.scalar st.packet.size)) st
    | "sk_lookup_tcp", _ | "sk_lookup_udp", _ =>
      let (id, st) := st.fresh
      let st := st.setRegion (.kernel id) ByteArray.empty
      .ok (some (.object id)) st
    | "sk_release", _ => .ok none st
    | "ktime", _ =>
      let st := { st with clock := st.clock + 1000 }
      .ok (some (.scalar st.clock)) st
    -- `csum_add`: a 32-bit add with end-around carry; `csum_fold`:
    -- folded twice and complemented, as include/net/checksum.h has them
    | "csum_add", [c, a] =>
      let a := toNatMod a 32
      let s := (toNatMod c 32 + a) % 2 ^ 32
      .ok (some (.scalar (if s < a then s + 1 else s))) st
    | "csum_fold", [c] =>
      let s := toNatMod c 32
      let s := (s % 65536) + (s / 65536)
      let s := (s % 65536) + (s / 65536)
      .ok (some (.scalar (65535 - (s % 65536)))) st
    | f, _ => .err s!"the synthetic kernel has no rule for `{f}`"

end Koit.Machine
