import Koit.Interface.Decls
import Koit.Core.Print

/-!
The printout of a kernel interface's koit side, `koitc interface`:
what a program may refer to on the kernel, in a documentation form
that reuses the surface grammar's signatures and adds, after each
one, the clauses the grammar has no place for, a call's effects,
failure kind, acquisition, availability, and GPL mark. The form is
not source and is not read back. Tables print in a fixed order,
kinds, calls, resources, regions, slots, enumerations, constants,
types, each
alphabetical, so that two kernels diff line by line; the kernel side
never prints, no number, offset, or origin. With a kind, only what
that kind sees.
-/

namespace Koit.Interface

open Koit.Core

def Effect.doc : Effect → String
  | .call => "call" | .resize => "resize" | .sleep => "sleep" | .fail => "fail"
  | .write r => s!"write({r.print})"

def Nesting.doc : Nesting → String
  | .no => "no nesting" | .counted => "nests, counted"
  | .lifo => "nests, last in first out" | .yes => "nests"

def Home.doc : Home → String
  | .mapValue => "map values" | .global => "global data" | .object => "allocated objects"

/-- Phrases joined by a separator into lines of at most eighty
clauses, each indented by `n`. -/
def wrap (n : Nat) (phrases : List String) (sep : String := ", ") : List String :=
  let pad := String.ofList (List.replicate n ' ')
  phrases.foldl (fun (ls : List String) t =>
    match ls.getLast? with
    | some l => if l.length + t.length + sep.length ≤ 80 then ls.dropLast ++ [l ++ sep ++ t]
                else ls ++ [pad ++ t]
    | none => [pad ++ t]) []

/-- A head line and its clauses, on one line when they fit in eighty
clauses, else the clauses on a continuation line, and a trailing
note likewise. -/
def withClauses (head : String) (clauses : List String) (note : String := "") : String :=
  let c := if clauses.isEmpty then "" else "  " ++ " ".intercalate clauses
  let line := if head.length + c.length ≤ 80 then head ++ c else head ++ "\n   " ++ c
  if note == "" then line
  else
    let last := (line.splitOn "\n").getLast!
    if last.length + note.length + 2 ≤ 80 then line ++ "  " ++ note
    else line ++ "\n    " ++ note

def KindDecl.doc (k : KindDecl) : String :=
  let pkt := if !k.hasPkt then "none" else if k.pktWritable then "rw" else "ro"
  let verdicts := match k.verdicts with
    | [] => s!"result {k.verdictTy.print}"
    | vs => s!"verdicts \{ {" ".intercalate (vs.map fun (v : String × Nat) => v.1)} }"
  let dflt := match k.defaultExit with
    | .verdict v => v
    | .value n => toString n
  let sugar := match k.sugar with
    | [] => []
    | ss => [s!"sugar \{ {", ".intercalate (ss.map fun (s, v) => s!"{s} = {v}")} }"]
  let head := s!"kind {k.name} : section \"{k.section_}\", pkt {pkt}, {verdicts},"
  let tail := ["default " ++ dflt] ++ (if k.sleep then ["sleepable"] else []) ++ sugar
  let ctx := if k.ctx.isEmpty then ["  ctx opaque"] else
    let w := k.ctx.foldl (fun m f => max m f.name.length) 0
    k.ctx.map fun f =>
      s!"  ctx {f.name}{String.ofList (List.replicate (w - f.name.length) ' ')} : {f.ty.print}" ++
        (if f.writable then "  writable" else "")
  "\n".intercalate ([head] ++ wrap 4 tail ++ ctx)

def CallDecl.doc (c : CallDecl) : String :=
  let head := match c.sig with
    | .fn params ret =>
      s!"fn {c.name}({", ".intercalate (params.map Param.print)})" ++
        (match ret with | some t => s!" -> {t.print}" | none => "")
    | .builtin => s!"builtin {c.name}"
  let clauses :=
    (if c.effects.isEmpty then [] else [s!"effects \{ {", ".intercalate (c.effects.map Effect.doc)} }"]) ++
    (match c.fails with | some k => [s!"fails {k.spelling}"] | none => []) ++
    (match c.acquires with | some r => [s!"acquires {r.name}"] | none => []) ++
    (if c.kinds.isEmpty then [] else [s!"in {", ".intercalate c.kinds}"]) ++
    (if c.gplOnly then ["gpl"] else []) ++
    (if c.lockSafe then ["lock_safe"] else []) ++
    (if c.requires.isEmpty then [] else [s!"requires {", ".intercalate (c.requires.map (·.name))}"]) ++
    (match c.derivedFrom with | some p => [s!"derived_from {p}"] | none => [])
  let note := match c.sig, c.impl with
    | .builtin, _ => if c.kernel == "" then "" else s!"// {c.kernel}"
    | _, .inline => if c.kernel == "" then "" else s!"// {c.kernel}"
    | _, _ => ""
  withClauses head clauses note

def ResourceDecl.doc (r : ResourceDecl) : String :=
  let acq := match r.arg with
    | .place slot => s!"{", ".intercalate (r.acquirers.map (· ++ "(p)"))}, p a {slot}"
    | .scope => ", ".intercalate r.acquirers
    | .call => ", ".intercalate (r.acquirers.map (· ++ "(...)"))
  let release := if r.normalExit == r.abnormalExit then s!"released by {r.normalExit}"
    else s!"released by {r.normalExit}, or {r.abnormalExit} on an abnormal exit"
  let forbids := if r.forbidden.isEmpty then "forbids nothing"
    else s!"forbids {", ".intercalate (r.forbidden.map Effect.doc)}"
  let guards := if r.guards == "" then [] else [s!"guards {r.guards}"]
  let guards := guards ++ (if r.lockSafe then ["lock_safe"] else []) ++
    (if r.requires.isEmpty then [] else [s!"requires {", ".intercalate (r.requires.map (·.name))}"]) ++
    (match r.derivedFrom with | some p => [s!"derived_from {p}"] | none => []) ++
    (if r.holdsOnFailure then ["holds_on_failure"] else [])
  let cols := [s!"acquired by {acq}"] ++ (if r.yields then ["yields an owned reference"] else []) ++
    (match r.fails with | some k => [s!"fails {k.spelling}"] | none => []) ++
    [release, forbids, r.nesting.doc] ++ guards
  "\n".intercalate ([s!"resource {r.res.name} :"] ++ wrap 4 cols "; ")

def RegionDecl.doc (r : RegionDecl) : String :=
  let cols := [if r.dynamic then "dynamic" else "static",
               if r.writable then "writable" else "read-only",
               if r.initialized then "initialized" else "uninitialized"] ++
    (match r.guard with | some _ => ["guarded by its layout token"] | none => []) ++
    (match r.maxOffset with | some n => [s!"max offset {n}"] | none => [])
  let lines := wrap 4 cols
  let head := s!"region {r.name} : " ++ (lines.head?.getD "").trimAsciiStart
  withClauses ("\n".intercalate (head :: lines.drop 1)) [] (if r.note == "" then "" else s!"// {r.note}")

def SlotDecl.doc (s : SlotDecl) : String :=
  "\n".intercalate ([s!"slot {s.name} :"] ++ wrap 4 ([s!"size {s.size}", s!"align {s.align}"] ++
    (if s.unique then ["one per value"] else []) ++
    [s!"in {", ".intercalate (s.homes.map Home.doc)}", s!"named by {s.namedBy}"]))

def EnumDecl.doc (e : EnumDecl) : String :=
  "\n".intercalate ([s!"enum {e.name} : u{e.width}  // {e.kernel}"] ++
    wrap 4 (e.constants.map fun (n, v) => s!"{n} = {v}"))

def ConstDecl.doc (c : ConstDecl) : String :=
  s!"const {c.name} = {c.value.print}"

def sortByName {α} (name : α → String) (xs : List α) : List α :=
  xs.mergeSort fun a b => name a ≤ name b

/-- The printout, for every kind or for one. -/
def doc (i : Interface) (kind? : Option String := none) : String :=
  let kinds := match kind? with
    | some k => i.kinds.filter (·.name == k)
    | none => i.kinds
  let calls := match kind? with
    | some k => i.calls.filter fun c => c.kinds.isEmpty || c.kinds.contains k
    | none => i.calls
  -- a resource the kind can acquire: by a scope or place declaration, or by a
  -- call it sees
  let resources := match kind? with
    | some _ => i.resources.filter fun r => match r.arg with
      | .call => r.acquirers.any fun a => calls.any (·.name == a)
      | _ => true
    | none => i.resources
  let section_ (title : String) (decls : List String) : List String :=
    if decls.isEmpty then [] else [s!"// {title}"] ++ decls ++ [""]
  -- one line per reason: a dropped resource is recorded under its
  -- acquirers as well
  let missing := (i.missing.foldl (fun (acc : List (String × String)) (n, why) =>
    if acc.any (·.2 == why) then acc else acc ++ [(n, why)]) []).map
    fun (n, why) => s!"// {n}: {why}"
  "\n".intercalate (
    [s!"kernel {i.kernel}", ""] ++
    section_ "kinds" [("\n\n".intercalate ((sortByName (·.name) kinds).map KindDecl.doc))] ++
    section_ "calls" ((sortByName (·.name) calls).map CallDecl.doc) ++
    section_ "resources" [("\n\n".intercalate ((sortByName (·.res.name) resources).map ResourceDecl.doc))] ++
    section_ "regions" ((sortByName (·.name) i.regions).map RegionDecl.doc) ++
    section_ "slots" ((sortByName (·.name) i.slots).map SlotDecl.doc) ++
    section_ "enumerations"
      [("\n\n".intercalate ((sortByName (·.name) i.enums).map EnumDecl.doc))] ++
    section_ "constants" ((sortByName (·.name) i.consts).map ConstDecl.doc) ++
    section_ "types" ((sortByName (·.name) i.types).map TypeDecl.print) ++
    section_ s!"absent on {i.kernel}" missing) ++ "\n"

end Koit.Interface
