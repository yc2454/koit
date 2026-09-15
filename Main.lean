import Koit

/-!
`koitc`, the koit command line: `lex`, `parse`, `print`, `desugar`,
`check`, `run`. Session 1 delivered the first three, session 2
`desugar` and the base `check`; `run` reports that it is not
implemented yet.
-/

open Koit Koit.Syntax

def usage : String := String.intercalate "\n"
  ["usage: koitc <command> [--kernel TAG] FILE.ko",
   "  lex     print the tokens of FILE, one per line",
   "  parse   parse FILE and list its declarations",
   "  print   parse FILE and print it back as source",
   "  desugar parse FILE and print its Core",
   "  check   type-check FILE against the prelude of kernel TAG",
   "          (default and only prelude in stage 1: v7.0)",
   "  run     interpret FILE (from session 3)"] ++ "\n"

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

/-- Splits `[--kernel TAG] FILE` into the tag and the file. -/
def kernelOpt : List String → Option (Option String × String)
  | ["--kernel", t, file] => some (some t, file)
  | [file] => some (none, file)
  | _ => none

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
    let some (tag, file) := kernelOpt rest | do IO.eprint usage; return 2
    let some pre ← preludeFor tag | return 2
    match ← parseFile file with
    | some u =>
      IO.print (Core.desugar pre u).print
      return 0
    | none => return 1
  | "check" :: rest => do
    let some (tag, file) := kernelOpt rest | do IO.eprint usage; return 2
    let some pre ← preludeFor tag | return 2
    match ← parseFile file with
    | some u =>
      match Check.checkUnit pre (Core.desugar pre u) with
      | .ok () =>
        IO.println s!"{file}: ok"
        return 0
      | .error d =>
        IO.eprintln s!"{file}:{d}"
        return 1
    | none => return 1
  | ["run", file] => do
    let _ ← readSource file
    notYet "run" "session 3"
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
