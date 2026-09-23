import Lean.Data.Json
import Koit.Compile.Compile
import Koit.Compile.CPrint

/-!
The interchange form from `koitc` to the kernel-facing tools, `koitc
emit --json`: one self-contained document per unit, so that the
loader, the ELF writer, and the runner's kernel stage never read Lean
or the interface. The header names the kernel tag, the cpu, the unit,
and its license; the named types carry their layouts as the checker
computed them, what a BTF encoder needs; each map its koit kind, the
kernel's map type by name and number, its key and value types with
their byte sizes, its entries, whether the compiler marked it for
direct value access, and where its value holds a spin lock; each
program its kind, the kernel's program type by name and number, its
section, the words as sixteen-digit hex strings so that no reader
rounds a 64-bit value, the relocations, and the notes. The numbers a
tool needs come from the kernel side of the interface here, so a
tool never re-derives a kernel fact.
-/

namespace Koit.Compile

open Lean (Json ToJson toJson)
open Koit.Core

/-- The layout of a type as a JSON description: ints with sign and
width, big-endian ints, arrays with element and length, structs with
fields at their offsets, slot types with the kernel's name, size,
and alignment, and references to named types by name. -/
partial def typeJson (env : Check.Env) : Ty → Except String Json
  | .int _ s w => pure <| Json.mkObj [("kind", "int"), ("signed", Json.bool s), ("bits", toJson w)]
  | .be _ w => pure <| Json.mkObj [("kind", "be"), ("bits", toJson w)]
  | .bool _ => pure <| Json.mkObj [("kind", "bool")]
  | .named _ n => pure <| Json.mkObj [("kind", "named"), ("name", n)]
  | .refined _ _ t _ => typeJson env t
  | .slot s n =>
    match env.interface.slot? n with
    | some decl => pure <| Json.mkObj [("kind", "slot"), ("name", n), ("kernel", decl.kernel),
                                      ("size", toJson decl.size), ("align", toJson decl.align)]
    | none => throw s!"{s.start}: unknown slot type `{n}`"
  | t@(.array s elem n) => do
    let some len := env.evalConst n | throw s!"{s.start}: the array length is not a constant"
    let (size, align) ← layoutOf env t
    pure <| Json.mkObj [("kind", "array"), ("elem", ← typeJson env elem), ("len", toJson len),
                        ("size", toJson size), ("align", toJson align)]
  | t@(.struct _ fields) => do
    let (size, align) ← layoutOf env t
    let mut off := 0
    let mut fs : Array Json := #[]
    for f in fields do
      let (sz, al) ← layoutOf env f.ty
      off := (off + al - 1) / al * al
      fs := fs.push (Json.mkObj [("name", f.name), ("offset", toJson off), ("type", ← typeJson env f.ty)])
      off := off + sz
    pure <| Json.mkObj [("kind", "struct"), ("size", toJson size), ("align", toJson align),
                        ("fields", Json.arr fs)]
  | t => throw s!"{t.span.start}: `{t.print}` names a place, not data"
where
  layoutOf (env : Check.Env) (t : Ty) : Except String (Nat × Nat) :=
    match env.layout t with
    | .ok r => pure r
    | .error d => throw d.msg

/-- Two hex digits of a byte. -/
def hex2 (n : Nat) : String :=
  let d := "0123456789abcdef".toList
  String.ofList [d[n / 16 % 16]!, d[n % 16]!]

/-- The byte offset of the spin lock in a map value, when it holds
one at the top level, where the kernel looks for it. -/
def spinLockOffset (env : Check.Env) (t : Ty) : Option Nat :=
  match env.norm t with
  | .ok (.struct _ fields) =>
    let rec go (fields : List Field) (off : Nat) : Option Nat :=
      match fields with
      | [] => none
      | f :: rest =>
        match env.layout f.ty with
        | .ok (sz, al) =>
          let off := (off + al - 1) / al * al
          match env.norm f.ty with
          | .ok (.slot _ "spinlock") => some off
          | _ => go rest (off + sz)
        | .error _ => none
    go fields 0
  | _ => none

def mapJson (pre : Interface) (env : Check.Env) (direct : List String) (d : MapDecl) :
    Except String Json := do
  let sizeOf (t : Ty) : Except String Nat :=
    match env.layout t with
    | .ok (n, _) => pure n
    | .error e => throw e.msg
  let entries (n : Expr) : Except String Int :=
    match env.evalConst n with
    | some k => pure k
    | none => throw s!"{d.span.start}: the size of map `{d.name}` is not a constant"
  let typeName := C.mapTypeName d.kind
  let some typeId := pre.side.mapTypes.lookup typeName
    | throw s!"{pre.kernel} has no {typeName}"
  let u32 : Ty := .int d.span false 32
  let (kind, key, value, n) ← match d.kind with
    | .array n v => pure ("array", some u32, some v, n)
    | .percpu n v => pure ("percpu", some u32, some v, n)
    | .hash n k v => pure ("hash", some k, some v, n)
    | .ringbuf n => pure ("ringbuf", none, none, n)
    | .progArray n _ => pure ("prog_array", some u32, some u32, n)
  let keyJson ← match key with
    | some k => pure (← typeJson env k)
    | none => pure Json.null
  let valueJson ← match value with
    | some v => pure (← typeJson env v)
    | none => pure Json.null
  pure <| Json.mkObj [
    ("name", d.name), ("kind", kind), ("type", typeName), ("type_id", toJson typeId),
    ("key", keyJson), ("key_size", toJson (← match key with | some k => sizeOf k | none => pure 0)),
    ("value", valueJson),
    ("value_size", toJson (← match value with | some v => sizeOf v | none => pure 0)),
    ("entries", toJson (← entries n)), ("flags", toJson d.access.flags),
    ("access", match d.access with | .rw => "rw" | .ro => "ro" | .wo => "wo"),
    -- the contents the object holds: the compiler's bytes, or the
    -- initializer's constants entry by entry; absent for a zero-filled
    -- map
    ("data", ← do
      if !d.bytes.isEmpty then
        pure (Json.str (String.join (d.bytes.map fun b => hex2 b.toNat)))
      else if d.init.isEmpty || (match d.kind with | .progArray .. => true | _ => false) then
        pure Json.null
      else
        let size ← match value with
          | some v => sizeOf v
          | none => throw s!"`{d.name}` has no value type to initialize"
        let mut out := ""
        for e in d.init do
          match env.evalConst e with
          | some x =>
            out := out ++ String.join ((Machine.leBytes (Machine.toNatMod x (8 * size)) size).map fun b => hex2 b.toNat)
          | none => throw s!"the initializer of `{d.name}` is not constant"
        pure (Json.str out)),
    ("direct", Json.bool (direct.contains d.name)),
    -- a program array's entries, by slot
    ("programs", Json.arr ((d.init.filterMap fun e => match e with
      | .var _ p => some (Json.str p)
      | _ => none).toArray)),
    ("spin_lock", match value.bind (spinLockOffset env) with
      | some o => toJson o
      | none => Json.null)]

/-- A relocation; a kfunc's carries the prototype the kernel side
transcribed, so that the ELF writer can declare the extern in BTF. -/
def relocJson (pre : Interface) (r : Reloc) : Json :=
  match r.kind with
  | .mapFd m => Json.mkObj [("index", toJson r.index), ("kind", "map_fd"), ("map", m)]
  | .mapValue m off =>
    Json.mkObj [("index", toJson r.index), ("kind", "map_value"), ("map", m), ("offset", toJson off)]
  | .kfunc n =>
    let proto := match pre.side.kfunc? n with
      | some kf => [("ret", Json.str kf.ret),
                    ("args", Json.arr (kf.args.map fun (t, a) => Json.arr #[Json.str t, Json.str a]).toArray)]
      | none => []
    Json.mkObj ([("index", toJson r.index), ("kind", "kfunc"), ("name", n)] ++ proto)

def objectJson (pre : Interface) (o : Object) : Except String Json := do
  let some decl := pre.kind? o.kind | throw s!"unknown kind `{o.kind}`"
  let some pt := pre.side.progType? decl.progType | throw s!"{pre.kernel} has no {decl.progType}"
  let result := match decl.verdictTy with
    | .int _ true w => s!"i{w}"
    | .int _ false w => s!"u{w}"
    | t => t.print
  pure <| Json.mkObj [
    ("name", o.name), ("kind", o.kind), ("prog_type", pt.name), ("prog_type_id", toJson pt.id),
    ("section", o.section_), ("result", result),
    ("verdicts", Json.mkObj (decl.verdicts.map fun (n, v) => (n, toJson v))),
    ("words", Json.arr (o.words.map fun w => Json.str (hex16 w))),
    ("relocs", Json.arr (o.relocs.map (relocJson pre)).toArray),
    ("subprograms", Json.arr (o.subs.map fun (n, i) =>
      Json.mkObj [("name", n), ("insn", toJson i)]).toArray),
    ("notes", Json.arr (o.notes.map fun n =>
      Json.mkObj [("index", toJson n.index), ("callee", n.callee.print)]).toArray)]

/-- The document of a compiled unit. -/
def unitJson (pre : Interface) (unit : String) (cpu : BPF.Cpu) (core : CompUnit) (C : Compiled) :
    Except String Json := do
  let env := envOf pre core
  -- the interface's types first, so that a unit's own shadow them; an
  -- enumeration is a value type, never a map value, a view, or a
  -- field, so nothing a tool builds needs its layout
  let named := (pre.types ++ core.types).filter fun d =>
    match d.ty with
    | .enum .. => false
    | _ => true
  let types ← named.mapM fun d => do
    pure <| Json.mkObj [("name", d.name), ("type", ← typeJson env d.ty)]
  let core := withFormats core C.fmtMap
  let env := envOf pre core
  let maps ← core.maps.mapM (mapJson pre env (C.lir.direct ++ (C.fmtMap.map (·.name)).toList))
  -- the global functions' prototypes, for the object's function
  -- information: scalars and references, the references non-null
  let fns ← (core.fns.filter (·.global)).mapM fun f => do
    let params ← f.params.mapM fun p => do
      let (kind, t) ← match p.ty with
        | .ref _ t => pure ("ref", t)
        | t => pure ("scalar", t)
      pure (Json.mkObj [("name", p.name), ("kind", kind), ("type", ← typeJson env t)])
    let ret ← match f.ret with
      | some t => typeJson env t
      | none => pure Json.null
    pure (Json.mkObj [("name", f.name), ("params", Json.arr params.toArray), ("ret", ret)])
  let programs ← C.objects.mapM (objectJson pre)
  pure <| Json.mkObj [
    ("koit", toJson (1 : Nat)), ("kernel", pre.kernel),
    ("fns", Json.arr fns.toArray),
    ("cpu", match cpu with | .v3 => "v3" | .v4 => "v4"),
    ("unit", unit),
    ("license", match core.license with | some (_, l) => Json.str l | none => Json.null),
    ("types", Json.arr types.toArray), ("maps", Json.arr maps.toArray),
    ("programs", Json.arr programs.toArray)]

end Koit.Compile
