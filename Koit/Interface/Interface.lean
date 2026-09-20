import Koit.Interface.Join
import Koit.Interface.KoitSide
import Koit.Interface.Kernel.V6_8
import Koit.Interface.Kernel.V7_0_rc1
import Koit.BPF.Syntax

/-!
The interfaces the compiler carries, one per kernel tag: the koit
side joined with each transcribed kernel side. The join runs at
build time, so a correspondence that disagrees with the kernel's
prototypes fails `lake build` with the disagreement.
-/

namespace Koit.Interface

open Koit.BPF (Builtin)

/-- The machine's own layouts by helper name, checked against every
kind's availability and prototype like the rows' correspondences. -/
def builtinLayouts : List (String × List AbiArg) := [
  ("map_lookup_elem", Builtin.lookup.abi),
  ("map_update_elem", Builtin.update.abi),
  ("map_delete_elem", Builtin.delete.abi),
  ("ringbuf_reserve", (Builtin.reserve 0).abi),
  ("ringbuf_submit", Builtin.submit.abi),
  ("ringbuf_discard", Builtin.discard.abi),
  ("spin_lock", Builtin.lock.abi),
  ("spin_unlock", Builtin.unlock.abi),
  ("trace_printk", (Builtin.printk "" 0 "" 0).abi)
]

/-- The join of one tag, or the disagreements as an error. -/
def ofKernel (k : Kernel.Side) : Except String Interface :=
  join koitSide k builtinLayouts

/-- The build stops here, printing the disagreements, when the koit
side and a kernel side do not fit. -/
def checked (k : Kernel.Side) : Interface :=
  match ofKernel k with
  | .ok i => i
  | .error e => panic! e

#eval show IO Unit from do
  for k in [Kernel.v6_8, Kernel.v7_0_rc1] do
    if let .error e := ofKernel k then throw (IO.userError e)

/-- Upstream 6.8, the stock kernel of the first target machines. -/
def v6_8 : Interface := checked Kernel.v6_8

/-- The 7.0 development snapshot, which has the kfuncs of the
preempt-off and IRQ-off resources that 6.8 lacks. -/
def v7_0_rc1 : Interface := checked Kernel.v7_0_rc1

/-- Every tag, the default first. -/
def all : List Interface := [v6_8, v7_0_rc1]

end Koit.Interface
