import Koit.Compile.Lower
import Koit.Compile.Inline
import Koit.Compile.Encode

/-!
The compiler: `compile = fold ; lower ; inline ; flatten ; alloc ;
encode`, a partial function on checked units. A frame over 512
bytes, a jump past 16 bits, or a construct the target cpu lacks is a
reported error, and every theorem of `Rules.lean` is stated for the
`.ok` result. The result keeps every level, so that the runner can
compare them and the theorems can name them.
-/

namespace Koit.Compile

open Koit.BPF (Cpu Reg BIR Bytecode)

/-- Every level of a compiled unit. -/
structure Compiled where
  lir       : LIR.CompUnit
  /-- The read-only data map of the unit's formats, when it prints. -/
  fmtMap    : Option Core.MapDecl
  birs      : List BIR
  allocated : List Allocated
  objects   : List Object
  deriving Inhabited

/-- The unit with the formats' map among its maps, for the machine
and the object. -/
def withFormats (core : Core.CompUnit) (fmtMap : Option Core.MapDecl) : Core.CompUnit :=
  { core with maps := core.maps ++ fmtMap.toList }

/-- The checker's environment of a unit, for the layouts the machine
and the allocation ask. -/
def envOf (pre : Interface) (core : Core.CompUnit) : Check.Env :=
  { interface := pre, license := core.license.map (·.2), types := core.types,
    consts := core.consts, configs := core.configs, maps := core.maps, fns := core.fns,
    contracts := core.contracts }

def sizeOfIn (env : Check.Env) : Core.Ty → Option Nat := fun t =>
  match env.layout t with
  | .ok (n, _) => some n
  | .error _ => none

/-- The pipeline on a checked unit. -/
def compile (pre : Interface) (cpu : Cpu) (core : Core.CompUnit) (checked : Check.Checked) :
    Except String Compiled := do
  let lir ← lower pre (fold pre core checked)
  let lir := inline lir
  LIR.wf pre lir |>.mapError (s!"the lowered unit is not well-formed: " ++ ·)
  let (birs, fmtMap) ← flatten pre cpu lir
  let env := envOf pre (withFormats core fmtMap)
  let allocated ← allocateAll pre (sizeOfIn env) birs
  let objects ← allocated.mapM fun a => encode pre a.prog
  return { lir, fmtMap, birs, allocated, objects }

/-- The machine's environment for a compiled program's bytecode. -/
def Compiled.envFor (C : Compiled) (pre : Interface) (env : Check.Env) (name : String) :
    Option (BPF.Env Reg Int) :=
  match C.allocated.find? (·.prog.name == name) with
  | some a => (bytecodeEnv pre env a.prog).toOption
  | none => none

end Koit.Compile
