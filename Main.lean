import Koit

/-!
`koitc`, the koit command line: `lex`, `parse`, `print`, `desugar`,
`check`, `run`, `lower`, `emit`, `shape`. `run` checks the unit, then
interprets every program of it in order, or the one named, over a
packet given in hex and zero-filled maps, and prints each verdict,
the lines `printk` wrote, and the map state; with `--lir` it runs the
lowered unit instead, so that the two runs can be compared. `lower`
prints the LIR of a checked unit, inlined with `--inline`; `emit`
prints the C the printer makes of it, or the words, or the bytecode
in LLVM's syntax and the words as bytes for the round trip through
`llvm-mc`; `shape` compiles the unit and tests the syntactic part of
Lemma L on every program.
-/

open Koit Koit.Syntax

def usage : String := String.intercalate "\n"
  ["usage: koitc <command> [--kernel TAG] [--smt] FILE.ko",
   "  lex     print the tokens of FILE, one per line",
   "  parse   parse FILE and list its declarations",
   "  print   parse FILE and print it back as source",
   "  desugar parse FILE and print its Core",
   "  check   type-check FILE against the prelude of kernel TAG",
   "          (default and only prelude in stage 1: v7.0); with --smt,",
   "          trace each accepted entailment as an SMT-LIB query on stderr",
   "  run     check FILE, then interpret its programs in order:",
   "          --packet HEX     the input packet (default: empty)",
   "          --program NAME   this program only",
   "          --ctx FIELD=N    a context field's value (default: 0)",
   "          --fuel N         the step budget (default: 100000)",
   "          --lir [--inline] run the lowered unit instead of Core",
   "          --bir            run the flattened unit on the machine",
   "          --bytecode       run the allocated unit on the machine",
   "          --cpu v3|v4      the instruction set the machine offers",
   "  lower   check FILE, then print its LIR; --inline removes the",
   "          functions; --bir prints the flattened unit, --bytecode",
   "          the allocated one",
   "  emit    check FILE, then print the C of its LIR; with --bytecode,",
   "          the words of its programs in hex with their relocations;",
   "          --asm the bytecode in LLVM's syntax, --words the words as",
   "          byte lines for llvm-mc; --cpu v3|v4 as for run",
   "  shape   compile FILE and test the shape of every program: each",
   "          test a conditional jump, each cast an instruction of the",
   "          table, each packet access and index under a test on its",
   "          path; --cpu v3|v4 as for run"] ++ "\n"

/-- Reads a source file, warning when its name does not end in `.ko`. -/
def readSource (path : String) : IO String := do
  let fp : System.FilePath := path
  unless fp.extension == some "ko" do
    IO.eprintln s!"koitc: warning: {path} does not end in .ko"
  try
    IO.FS.readFile fp
  catch e =>
    throw (IO.userError s!"cannot read {path}: {e}")

/-- Parses a file, reporting an error as `file:line:col: message`. -/
def parseFile (path : String) : IO (Option CompUnit) := do
  let src ← readSource path
  match parse src with
  | .ok u => return some u
  | .error e =>
    IO.eprintln s!"{path}:{e}"
    return none

def Koit.Syntax.Item.summary : Item → String
  | .const _ n .. => s!"const {n}"
  | .config _ n .. => s!"config {n}"
  | .type _ n _ => s!"type {n}"
  | .map _ n _ => s!"map {n}"
  | .fn d => s!"fn {d.name}"
  | .contract c => s!"contract {c.name} : {c.kind}"
  | .program p => s!"program {p.name} : {p.kind}"

def notYet (cmd session : String) : IO UInt32 := do
  IO.eprintln s!"koitc {cmd}: not implemented yet ({session})"
  return 2

/-- The preludes the compiler carries, one per kernel tag. -/
def preludes : List Prelude := [Prelude.stage1]

/-- The prelude for a kernel tag; the first one when no tag is given. -/
def preludeFor (tag : Option String) : IO (Option Prelude) := do
  match tag with
  | none => return preludes.head?
  | some t =>
    match preludes.find? (·.kernel == t) with
    | some p => return some p
    | none =>
      IO.eprintln s!"koitc: no prelude for kernel {t}; available: \
        {", ".intercalate (preludes.map (·.kernel))}"
      return none

/-- Splits `[--kernel TAG] [--smt] FILE` into the tag, the flag, and
the file. -/
def kernelOpt : List String → Option (Option String × Bool × String)
  | ["--kernel", t, "--smt", file] | ["--smt", "--kernel", t, file] =>
    some (some t, true, file)
  | ["--kernel", t, file] => some (some t, false, file)
  | ["--smt", file] => some (none, true, file)
  | [file] => some (none, false, file)
  | _ => none

/-- The options of `run`. -/
structure RunOpts where
  kernel  : Option String := none
  packet  : ByteArray := ByteArray.empty
  program : Option String := none
  ctx     : List (String × Nat) := []
  fuel    : Nat := 100000
  lir     : Bool := false
  bir     : Bool := false
  bytecode : Bool := false
  inline  : Bool := false
  cpu     : BPF.Cpu := .v3
  file    : Option String := none

partial def runOpts : List String → RunOpts → Option RunOpts
  | [], o => some o
  | "--kernel" :: t :: rest, o => runOpts rest { o with kernel := some t }
  | "--packet" :: h :: rest, o => do
    let b ← Core.Sem.parseHex h
    runOpts rest { o with packet := b }
  | "--program" :: n :: rest, o => runOpts rest { o with program := some n }
  | "--ctx" :: fv :: rest, o =>
    match fv.splitOn "=" with
    | [f, v] => do
      let n ← v.toNat?
      runOpts rest { o with ctx := o.ctx ++ [(f, n)] }
    | _ => none
  | "--fuel" :: n :: rest, o => do runOpts rest { o with fuel := ← n.toNat? }
  | "--lir" :: rest, o => runOpts rest { o with lir := true }
  | "--bir" :: rest, o => runOpts rest { o with bir := true }
  | "--bytecode" :: rest, o => runOpts rest { o with bytecode := true }
  | "--cpu" :: "v3" :: rest, o => runOpts rest { o with cpu := .v3 }
  | "--cpu" :: "v4" :: rest, o => runOpts rest { o with cpu := .v4 }
  | "--inline" :: rest, o => runOpts rest { o with inline := true }
  | [file], o => if file.startsWith "--" then none else some { o with file := some file }
  | _, _ => none

/-- The options of `emit`: the form printed and the cpu. -/
structure EmitOpts where
  mode : String := "c"
  cpu  : BPF.Cpu := .v3
  rest : List String := []

partial def emitOpts : List String → EmitOpts → EmitOpts
  | "--bytecode" :: r, o => emitOpts r { o with mode := "bytecode" }
  | "--asm" :: r, o => emitOpts r { o with mode := "asm" }
  | "--words" :: r, o => emitOpts r { o with mode := "words" }
  | "--cpu" :: "v3" :: r, o => emitOpts r { o with cpu := .v3 }
  | "--cpu" :: "v4" :: r, o => emitOpts r { o with cpu := .v4 }
  | r, o => { o with rest := r }

/-- A checked unit lowered through passes A and B, and I when asked. -/
def lowerUnit (pre : Prelude) (core : Core.CompUnit) (checked : Check.Checked)
    (inline : Bool) : Except String LIR.CompUnit := do
  let lir ← Compile.lower pre (Compile.fold pre core checked)
  let lir := if inline then Compile.inline lir else lir
  LIR.wf pre lir |>.mapError (s!"the lowered unit is not well-formed: " ++ ·)
  return lir

/-- A checked unit flattened: passes A, B, I, and C, with the
machine's environment for each program. -/
def flattenUnit (pre : Prelude) (core : Core.CompUnit) (checked : Check.Checked)
    (cpu : BPF.Cpu) : Except String (List (BPF.Env BPF.VReg BPF.Label)) := do
  let lir ← lowerUnit pre core checked true
  let birs ← Compile.flatten pre cpu lir
  let env : Check.Env := { prelude := pre, license := core.license.map (·.2),
                           types := core.types, consts := core.consts,
                           configs := core.configs, maps := core.maps, fns := core.fns,
                           contracts := core.contracts }
  birs.mapM fun B => do
    let X ← Compile.birEnv pre env B
    BPF.wf X |>.mapError (s!"the flattened `{B.name}` is not well-formed: " ++ ·)
    return X

/-- A checked unit allocated: pass D on the flattened unit, with the
machine's environment for each program. -/
def allocUnit (pre : Prelude) (core : Core.CompUnit) (checked : Check.Checked)
    (cpu : BPF.Cpu) : Except String (List (BPF.Env BPF.Reg Int)) := do
  let lir ← lowerUnit pre core checked true
  let birs ← Compile.flatten pre cpu lir
  let env := Compile.envOf pre core
  let allocated ← Compile.allocateAll pre (Compile.sizeOfIn env) birs
  allocated.mapM fun a => do
    let X ← Compile.bytecodeEnv pre env a.prog
    BPF.wf X |>.mapError (s!"the allocated `{a.prog.name}` is not well-formed: " ++ ·)
    return X

/-- A checked unit, or its diagnostic. -/
def checkFile (file : String) (pre : Prelude) :
    IO (Option (Core.CompUnit × Check.Checked)) := do
  let some u ← parseFile file | return none
  let core := Core.desugar pre u
  match Check.checkUnit pre core with
  | .ok checked => return some (core, checked)
  | .error d =>
    IO.eprintln s!"{file}:{d}"
    return none

def run (args : List String) : IO UInt32 := do
  match args with
  | ["lex", file] => do
    let src ← readSource file
    match Syntax.lex src with
    | .ok toks =>
      for l in toks do
        IO.println s!"{l.span.start}\t{l.tok.describe}"
      return 0
    | .error e =>
      IO.eprintln s!"{file}:{e}"
      return 1
  | ["parse", file] => do
    match ← parseFile file with
    | some u =>
      for item in u.items do
        IO.println s!"{item.span.line}\t{item.summary}"
      return 0
    | none => return 1
  | ["print", file] => do
    match ← parseFile file with
    | some u =>
      IO.print u.print
      return 0
    | none => return 1
  | "desugar" :: rest => do
    let some (tag, _, file) := kernelOpt rest | do IO.eprint usage; return 2
    let some pre ← preludeFor tag | return 2
    match ← parseFile file with
    | some u =>
      IO.print (Core.desugar pre u).print
      return 0
    | none => return 1
  | "check" :: rest => do
    let some (tag, smt, file) := kernelOpt rest | do IO.eprint usage; return 2
    let some pre ← preludeFor tag | return 2
    match ← parseFile file with
    | some u =>
      match Check.checkUnit pre (Core.desugar pre u) smt with
      | .ok _ =>
        IO.println s!"{file}: ok"
        return 0
      | .error d =>
        IO.eprintln s!"{file}:{d}"
        return 1
    | none => return 1
  | "run" :: rest => do
    let some opts := runOpts rest {} | do IO.eprint usage; return 2
    let some file := opts.file | do IO.eprint usage; return 2
    let some pre ← preludeFor opts.kernel | return 2
    let some (core, checked) ← checkFile file pre | return 1
    let result ← if opts.bytecode then
        match allocUnit pre core checked opts.cpu with
        | .ok progs => pure (BPF.runUnit pre core progs opts.packet opts.ctx opts.program opts.fuel)
        | .error m => pure (.error m)
      else if opts.bir then
        match flattenUnit pre core checked opts.cpu with
        | .ok progs => pure (BPF.runUnit pre core progs opts.packet opts.ctx opts.program opts.fuel)
        | .error m => pure (.error m)
      else if opts.lir then
        match lowerUnit pre core checked opts.inline with
        | .ok lir => pure (LIR.Sem.runUnit pre core lir opts.packet opts.ctx opts.program opts.fuel)
        | .error m => pure (.error m)
      else pure (Core.Sem.runUnit pre core opts.packet opts.ctx opts.program opts.fuel)
    match result with
    | .ok (reports, maps) =>
      for r in reports do
        for l in r.log do IO.println s!"{r.program}: printk: {l}"
        IO.println s!"{r.program}: {r.verdict}"
      for l in maps do IO.println l
      return 0
    | .error m =>
      IO.eprintln s!"{file}: run: {m}"
      return 1
  | "lower" :: rest => do
    let (inline, rest) := match rest with
      | "--inline" :: rest => (true, rest)
      | rest => (false, rest)
    let (bir, rest) := match rest with
      | "--bir" :: rest => (true, rest)
      | rest => (false, rest)
    let (bytecode, rest) := match rest with
      | "--bytecode" :: rest => (true, rest)
      | rest => (false, rest)
    let some (tag, _, file) := kernelOpt rest | do IO.eprint usage; return 2
    let some pre ← preludeFor tag | return 2
    let some (core, checked) ← checkFile file pre | return 1
    if bytecode then
      match allocUnit pre core checked .v3 with
      | .ok progs =>
        for X in progs do IO.print (BPF.Bytecode.print X.prog)
        return 0
      | .error m =>
        IO.eprintln s!"{file}: {m}"
        return 1
    if bir then
      match flattenUnit pre core checked .v3 with
      | .ok progs =>
        for X in progs do IO.print (BPF.BIR.print X.prog)
        return 0
      | .error m =>
        IO.eprintln s!"{file}: {m}"
        return 1
    match lowerUnit pre core checked inline with
    | .ok lir =>
      IO.print lir.print
      return 0
    | .error m =>
      IO.eprintln s!"{file}: {m}"
      return 1
  | "shape" :: rest => do
    let (cpu, rest) := match rest with
      | "--cpu" :: "v4" :: rest => (BPF.Cpu.v4, rest)
      | "--cpu" :: "v3" :: rest => (BPF.Cpu.v3, rest)
      | rest => (BPF.Cpu.v3, rest)
    let some (tag, _, file) := kernelOpt rest | do IO.eprint usage; return 2
    let some pre ← preludeFor tag | return 2
    let some (core, checked) ← checkFile file pre | return 1
    match lowerUnit pre core checked false, Compile.compile pre cpu core checked with
    | .ok openLir, .ok C =>
      let reports := Compile.shapeUnit pre core openLir C
      for r in reports do
        for l in r.print do IO.println l
      return (if Compile.shapeOk reports then 0 else 1)
    | .error m, _ | _, .error m =>
      IO.eprintln s!"{file}: {m}"
      return 1
  | "emit" :: rest => do
    let o := emitOpts rest {}
    let some (tag, _, file) := kernelOpt o.rest | do IO.eprint usage; return 2
    let some pre ← preludeFor tag | return 2
    let some (core, checked) ← checkFile file pre | return 1
    if o.mode == "c" then
      match lowerUnit pre core checked false with
      | .ok lir =>
        IO.print (Compile.emitC pre lir)
        return 0
      | .error m =>
        IO.eprintln s!"{file}: {m}"
        return 1
    match Compile.compile pre o.cpu core checked with
    | .ok C =>
      if o.mode == "bytecode" then
        for ob in C.objects do IO.print (Compile.Object.print ob)
      else if o.mode == "words" then
        for ob in C.objects do IO.print (Compile.Object.printBytes ob)
      else
        for a in C.allocated do
          match Compile.printAsm pre a.prog with
          | .ok s => IO.print s
          | .error m =>
            IO.eprintln s!"{file}: {m}"
            return 1
      return 0
    | .error m =>
      IO.eprintln s!"{file}: {m}"
      return 1
  | _ => do
    IO.eprint usage
    return 2

/-- Every failure is reported as one line on stderr with exit code 1;
a bad command line exits 2. -/
def main (args : List String) : IO UInt32 := do
  try
    run args
  catch e =>
    IO.eprintln s!"koitc: {e}"
    return 1
