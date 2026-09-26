import Koit.LIR.Wf
import Koit.Core.State

/-!
The printer P, from LIR with functions to C: one C construct per LIR
construct, through the total-arithmetic shim `koit.h`, so that no C
undefined behavior is reachable, and readable enough to be compared
with the source. It is outside every theorem: the C path is the
portable one through clang and libbpf, validated per program like
everything the compiler emits.

Printer policy, recorded here as the design document asks: `block`,
`loop`, and `br` are labels and `goto`; a `fails` or `T ?` function
returns a status, 0 for a value, 1 for absence, 2 plus the kind for a
failure with the reason in an out-parameter, and a call site tests
it; a `raise` in a program body sets `reason` and jumps to the
handler of its kind; a map read by direct value access is looked up
once at entry with a null test that returns the kind's failure
verdict, since C has no direct value access for a declared map; a
frame is an aligned object and a pointer to it; a kernel function is
called by its declaration's correspondence, the layout of the kernel's
arguments in terms of koit's, and declared at its number with the C
prototype the kernel side transcribed, as are the context structs,
each field pinned to its transcribed offset by a static assertion,
so that the shim `koit.h` declares nothing the kernel states.
-/

namespace Koit.Compile

open Koit.Core (Kind)
open Koit.Interface (AbiArg CallDecl)
open Koit.Interface.Kernel (CtxStruct CtxField Helper Kfunc)

namespace C

/-- Lines of output with a counter for labels. -/
abbrev PM := StateM Nat

def freshLabel (base : String) : PM String := do
  let n ← get
  set (n + 1)
  return s!"{base}_{n}"

def ity (s : Bool) (w : Nat) : String := (if s then "s" else "u") ++ toString w

/-- The names C reserves, and the ones the printer itself uses: a koit
name among them gets a trailing underscore. -/
def cReserved : List String :=
  ["auto", "break", "case", "char", "const", "continue", "default", "do",
   "double", "else", "enum", "extern", "float", "for", "goto", "if", "inline",
   "int", "long", "register", "restrict", "return", "short", "signed",
   "sizeof", "static", "struct", "switch", "typedef", "union", "unsigned",
   "void", "volatile", "while", "NULL", "out", "ctx", "koit_st", "koit_kind",
   "koit_zero", "koit_irq_flags", "u8", "u16", "u32", "u64", "s8", "s16",
   "s32", "s64"]

def cname (x : String) : String :=
  if cReserved.contains x || x.startsWith "koit_" || x.startsWith "bpf_" then x ++ "_" else x

def cty : LIR.Ty → String
  | .int s w => ity s w
  | .ptr => "void *"

/-- The C type of a Core data type, in a declarator for `name`. -/
partial def cdecl (types : List Core.TypeDecl) (t : Core.Ty) (name : String) : String :=
  match t with
  | .int _ s w => s!"{ity s w} {name}"
  | .be _ w => s!"u{w} {name}"
  | .bool _ => s!"u8 {name}"
  | .slot _ "spinlock" => s!"struct bpf_spin_lock {name}"
  | .slot _ n => s!"u8 {name}[0] /* {n} */"
  | .named _ n =>
    match types.find? (·.name == n) with
    | some d =>
      match d.ty with
      | .struct .. => s!"struct {cname n} {name}"
      | t' => cdecl types t' name
    | none => s!"struct {cname n} {name}"
  | .struct _ fields =>
    "struct { " ++ String.join (fields.map fun f => cdecl types f.ty (cname f.name) ++ "; ") ++
      "} " ++ name
  | .array _ elem n =>
    let len := match n with
      | .lit _ v _ => toString v
      | e => e.print
    cdecl types elem s!"{name}[{len}]"
  | .refined _ _ base _ => cdecl types base name
  | t => s!"void *{name} /* {t.print} */"

/-- A literal with the suffix its width needs. -/
def clit (w : Nat) (k : Nat) : String :=
  if w == 64 then s!"{k}ULL" else if w == 32 then s!"{k}U" else s!"((u{w}){k})"

mutual

partial def cexpr (inFn : Bool) : LIR.Expr → String
  | .lit w k => clit w k
  | .var x => cname x
  | .arith op s w l r =>
    let a := cexpr inFn l
    let b := cexpr inFn r
    let u := s!"u{w}"
    let t := ity s w
    match op with
    | .add => s!"(({t})(({u})({a}) + ({u})({b})))"
    | .sub => s!"(({t})(({u})({a}) - ({u})({b})))"
    | .mul => s!"(({t})(({u})({a}) * ({u})({b})))"
    | .band => s!"(({t})(({u})({a}) & ({u})({b})))"
    | .bor => s!"(({t})(({u})({a}) | ({u})({b})))"
    | .bxor => s!"(({t})(({u})({a}) ^ ({u})({b})))"
    | .div => s!"koit_div_{t}({a}, {b})"
    | .mod => s!"koit_mod_{t}({a}, {b})"
    | .shl => s!"koit_shl_{t}({a}, {b})"
    | .shr => s!"koit_shr_{t}({a}, {b})"
  | .cast s w s' w' e => s!"(({ity s' w'})({ity s w})({cexpr inFn e}))"
  | .bswap w e => s!"__builtin_bswap{w}({cexpr inFn e})"
  | .load s w a => s!"(*({ity s w} *)({caddr inFn a}))"
  | .ctx f => s!"ctx->{f}"
  | .addr a => caddr inFn a
  | .mapPtr m => s!"&{cname m}"

partial def caddr (inFn : Bool) : LIR.Addr → String
  | .var x => cname x
  | .plus a k => s!"((u8 *)({caddr inFn a}) + {k})"
  | .index a e k => s!"((u8 *)({caddr inFn a}) + ({cexpr inFn e}) * {k})"
  | .pktData => if inFn then "pkt_data" else "((void *)(long)ctx->data)"
  | .pktEnd => if inFn then "pkt_end" else "((void *)(long)ctx->data_end)"
  | .mapval m k => s!"((u8 *)({cname m}__val) + {k})"

end

def isPtrExpr : LIR.Expr → Bool
  | .addr _ | .mapPtr _ => true
  | _ => false

def ccond (inFn : Bool) (Γ : List (String × LIR.Ty)) (c : LIR.Cond) : String :=
  let ptrSide (e : LIR.Expr) : Bool :=
    isPtrExpr e || match e with
      | .var x => Γ.lookup x == some .ptr
      | _ => false
  let isZero : LIR.Expr → Bool
    | .lit _ 0 => true
    | _ => false
  if ptrSide c.l && isZero c.r then
    (if c.op == .eq then s!"!({cexpr inFn c.l})" else s!"({cexpr inFn c.l}) != NULL")
  else if ptrSide c.l || ptrSide c.r then
    s!"((u8 *)({cexpr inFn c.l}) {c.op.spelling} (u8 *)({cexpr inFn c.r}))"
  else
    let t := ity c.signed c.w
    s!"(({t})({cexpr inFn c.l}) {c.op.spelling} ({t})({cexpr inFn c.r}))"

/-- The type of an expression under the printer's environment, for
`printk`'s formats. -/
def exprTy (Γ : List (String × LIR.Ty)) : LIR.Expr → LIR.Ty
  | .lit w _ => .int false w
  | .var x => (Γ.lookup x).getD .u64
  | .arith _ s w .. => .int s w
  | .cast _ _ s' w' _ => .int s' w'
  | .bswap w _ => .int false w
  | .load s w _ => .int s w
  | .ctx _ => .u32
  | .addr _ | .mapPtr _ => .ptr

/-- The status protocol of a `fails` or `T ?` function: 0 for a value,
1 for absence, `2 + k` for a failure of kind `k`. -/
def kindIndex : Kind → Nat
  | .short_packet => 0 | .not_found => 1 | .bad_value => 2 | .failed_check => 3
  | .failed_call => 4 | .fail => 5 | .no_program => 6

/-- Whether a function uses the status protocol. -/
def statusFn (f : LIR.Fn) : Bool := f.fails || f.opt

/-- The C context struct of a kind: the uapi struct the kernel side
names for its program type. -/
def ctxType (pre : Interface) (kind : String) : String :=
  match (pre.kind? kind).bind fun r => (pre.side.progType? r.progType).bind (·.ctx) with
  | some s => s
  | none => "void"

/-- A C type of the kernel's prototypes as the shim spells it: every
pointer is `void *`, since the emitted C never dereferences one. -/
def kernelCTy (t : String) : String :=
  if (t.splitOn "*").length > 1 then
    -- a pointer to constant bytes stays constant, so that a string
    -- literal passes without a cast
    if (t.splitOn "const").length > 1 then "const void *" else "void *"
  else t

/-- The C call of a kernel function declaration, from its correspondence in
the kind: the kernel's arguments laid out from koit's, the context,
the constants the source does not name, and the size of a place
argument as `sizeof` of its C type. An inline declaration prints its C form. -/
def kernelCall (pre : Interface) (types : List Core.TypeDecl) (kind : String) (decl : CallDecl)
    (args : List String) (mapKind : Option Core.MapKind := none) : String :=
  let a (i : Nat) := (args[i]?).getD "0"
  let byLayout (name : String) (abi : List AbiArg) : String :=
    let params := match decl.sig with
      | .fn ps _ => Core.Param.resolveKeys ps mapKind
      | .builtin => []
    let one : AbiArg → String
      | .arg i => a i
      -- a scalar the kernel reads through a pointer: a compound literal
      | .argPtr i =>
        match params[i]? with
        | some p => s!"&({(cdecl types p.ty "").trimAsciiEnd})\{{a i}}"
        | none => a i
      | .ctx => "ctx"
      | .const k => if k < 0 then s!"({k})" else toString k
      | .fmt => "0"
      | .argSize i =>
        match params[i]? with
        | some p =>
          let pointee := match p.ty with
            | .ref _ t | .view _ t => t
            | t => t
          s!"sizeof({(cdecl types pointee "").trimAsciiEnd})"
        | none => "0"
    s!"{name}({", ".intercalate (abi.map one)})"
  match decl.implIn kind (mapKind.map (·.spelling)) with
  | .helper id abi =>
    match pre.side.helpers.find? (·.id == id) with
    | some h => byLayout s!"bpf_{h.name}" abi
    | none => s!"/* no helper {id} on {pre.kernel} */ 0"
  | .kfunc name abi => byLayout name abi
  | .inline =>
    match decl.name with
    | "pkt.len" => "((u64)((long)ctx->data_end - (long)ctx->data))"
    | "csum_add" => s!"koit_csum_add({a 0}, {a 1})"
    | "csum_fold" => s!"koit_csum_fold({a 0})"
    | h => s!"{h}({", ".intercalate args})"

/-- The C calls that enter and leave a scope resource. -/
def scopeCall (r : Core.Resource) (enter : Bool) : String :=
  match r.name, enter with
  | "rcu", true => "bpf_rcu_read_lock()"
  | "rcu", false => "bpf_rcu_read_unlock()"
  | "preempt", true => "bpf_preempt_disable()"
  | "preempt", false => "bpf_preempt_enable()"
  | "irq", true => "bpf_local_irq_save(&koit_irq_flags)"
  | "irq", false => "bpf_local_irq_restore(&koit_irq_flags)"
  | n, true => s!"koit_enter_{n}()"
  | n, false => s!"koit_leave_{n}()"

/-- What the printer knows while printing a body. -/
structure PCtx where
  pre    : Interface
  types  : List Core.TypeDecl
  fns    : List LIR.Fn
  /-- The unit's maps, for the map kind a map-pointer argument selects a
  kernel function by. -/
  maps   : List Core.MapDecl := []
  /-- The program's kind, or empty in a function, whose calls take
  each declaration's default correspondence. -/
  kind   : String
  /-- Inside a function using the status protocol. -/
  status : Bool
  /-- Inside a program body or handler. -/
  program : Bool
  /-- The default verdict, for the dead branches of direct maps. -/
  defaultVerdict : String
  /-- The functions that take the packet's bounds as parameters. -/
  bounded : List String := []
  /-- Labels of the enclosing constructs, innermost first. -/
  labels : List String := []
  Γ      : List (String × LIR.Ty) := []

def ind (n : Nat) : String := String.ofList (List.replicate n ' ')

def fmtOf : LIR.Ty → String
  | .int true 64 => "%lld"
  | .int false 64 => "%llu"
  | .int true _ => "%d"
  | .int false _ => "%u"
  | .ptr => "%p"

/-- `printk`'s `{}` rewritten to the format of each argument. -/
def cfmt (fmt : String) (tys : List LIR.Ty) : String :=
  let parts := fmt.splitOn "{}"
  let rec go : List String → List LIR.Ty → String
    | [], _ => ""
    | [p], _ => p
    | p :: ps, t :: ts => p ++ fmtOf t ++ go ps ts
    | p :: ps, [] => p ++ "{}" ++ go ps []
  go parts tys

mutual

partial def cstmts (c : PCtx) (n : Nat) : List LIR.Stmt → PM (List String × PCtx)
  | [] => return ([], c)
  | s :: rest => do
    let (ls, c') ← cstmt c n s
    let (rs, c'') ← cstmts c' n rest
    return (ls ++ rs, c'')

/-- One statement as lines at indentation `n`, and the environment
after it. -/
partial def cstmt (c : PCtx) (n : Nat) (s : LIR.Stmt) : PM (List String × PCtx) := do
  let line (t : String) : List String := [ind n ++ t]
  let bind (x : String) (t : LIR.Ty) : PCtx := { c with Γ := (x, t) :: c.Γ }
  match s with
  | .«let» _ x t e =>
    return (line s!"{cty t}{if t == .ptr then "" else " "}{cname x} = {cexpr (!c.program) e};", bind x t)
  | .assign _ x e => return (line s!"{cname x} = {cexpr (!c.program) e};", c)
  | .store _ w a e => return (line s!"*(u{w} *)({caddr (!c.program) a}) = {cexpr (!c.program) e};", c)
  | .ctxStore _ f e => return (line s!"ctx->{f} = {cexpr (!c.program) e};", c)
  | .frame _ x sz src =>
    let obj := match src with
      | some t => cdecl c.types t s!"{cname x}__obj"
      | none => s!"u8 {cname x}__obj[{sz}]"
    return (line s!"{obj} __attribute__((aligned(8))) = \{0};" ++
            line s!"void *{cname x} = &{cname x}__obj;", bind x .ptr)
  | .ite _ cnd t e =>
    let (tl, _) ← cstmts c (n + 4) t
    let (el, _) ← cstmts c (n + 4) e
    if e.isEmpty then
      return (line s!"if ({ccond (!c.program) c.Γ cnd}) \{" ++ tl ++ line "}", c)
    else
      return (line s!"if ({ccond (!c.program) c.Γ cnd}) \{" ++ tl ++ line "} else {" ++ el ++ line "}", c)
  | .block _ body =>
    let l ← freshLabel "L"
    let (bl, _) ← cstmts { c with labels := l :: c.labels } (n + 4) body
    return (line "{" ++ bl ++ line "}" ++ line s!"{l}: ;", c)
  | .loop _ body =>
    let l ← freshLabel "L"
    let (bl, _) ← cstmts { c with labels := l :: c.labels } (n + 4) body
    return (line "for (;;) {" ++ line s!"{l}: ;" ++ bl ++ line "}", c)
  | .br _ k =>
    match c.labels[k]? with
    | some l => return (line s!"goto {l};", c)
    | none => return (line s!"/* br {k} outside its constructs */", c)
  | .ret _ none =>
    if c.status then return (line "return 1;", c) else return (line "return;", c)
  | .ret _ (some e) =>
    if c.status then return (line s!"*out = {cexpr (!c.program) e}; return 0;", c)
    else return (line s!"return {cexpr (!c.program) e};", c)
  | .raise _ k e =>
    if c.program then
      return (line s!"reason = {cexpr (!c.program) e}; goto handler_{k.spelling};", c)
    else
      return (line s!"*reason = {cexpr (!c.program) e}; return {2 + kindIndex k};", c)
  | .call _ x f args u a =>
    -- a callee that mentions the packet's bounds receives them
    let boundArgs := if c.bounded.contains f then
        if c.program then ["((void *)(long)ctx->data)", "((void *)(long)ctx->data_end)"]
        else ["pkt_data", "pkt_end"]
      else []
    let cargs := args.map (cexpr (!c.program)) ++ boundArgs
    let some d := c.fns.find? (·.name == f)
      | return (line s!"/* unknown function {f} */", c)
    if !statusFn d then
      match x, d.ret with
      | some x, some t =>
        return (line s!"{cty t}{if t == .ptr then "" else " "}{cname x} = {cname f}({", ".intercalate cargs});",
                bind x t)
      | _, _ => return (line s!"{cname f}({", ".intercalate cargs});", c)
    -- the status protocol
    let (decl, outArg, c') := match x, d.ret with
      | some x, some t =>
        (line s!"{cty t}{if t == .ptr then "" else " "}{cname x};", [s!"&{cname x}"], bind x t)
      | _, _ => ([], [], c)
    let reasonArg := if d.fails then [if c.program then "&reason" else "reason"] else []
    let call := s!"{cname f}({", ".intercalate (cargs ++ outArg ++ reasonArg)})"
    let (ul, _) ← cstmts c' (n + 8) (u.getD [])
    let propagate := if c.program then
        line (ind 8 ++ "koit_kind = koit_st - 2; goto handler_dispatch;")
      else line (ind 8 ++ "return koit_st;")
    let failPart := if d.fails then
        line (ind 4 ++ "if (koit_st > 1) {") ++ ul ++ propagate ++ line (ind 4 ++ "}")
      else []
    let (al, _) ← cstmts c' (n + 8) (a.getD [])
    let absentPart := if d.opt then
        line (ind 4 ++ "if (koit_st == 1) {") ++ al ++ line (ind 4 ++ "}")
      else []
    return (decl ++ line "{" ++ line (ind 4 ++ s!"int koit_st = {call};") ++
            failPart ++ absentPart ++ line "}", c')
  | .builtin _ x b args =>
    let cargs := args.map (cexpr (!c.program))
    let a (i : Nat) := (cargs[i]?).getD "0"
    let res (t : LIR.Ty) (call : String) : List String × PCtx :=
      match x with
      | some x => (line s!"{cty t}{if t == .ptr then "" else " "}{cname x} = {call};", bind x t)
      | none => (line s!"{call};", c)
    match b with
    | .lookup m => return res .ptr s!"bpf_map_lookup_elem(&{cname m}, {a 0})"
    | .update m =>
      return res .i64 s!"(s64)bpf_map_update_elem(&{cname m}, {a 0}, {a 1}, BPF_ANY)"
    | .delete m => return res .i64 s!"(s64)bpf_map_delete_elem(&{cname m}, {a 0})"
    | .reserve m sz => return res .ptr s!"bpf_ringbuf_reserve(&{cname m}, {sz}, 0)"
    | .submit => return (line s!"bpf_ringbuf_submit({a 0}, 0);", c)
    | .discard => return (line s!"bpf_ringbuf_discard({a 0}, 0);", c)
    | .lock => return (line s!"bpf_spin_lock({a 0});", c)
    | .unlock => return (line s!"bpf_spin_unlock({a 0});", c)
    | .enter r => return (line s!"{scopeCall r true};", c)
    | .leave r => return (line s!"{scopeCall r false};", c)
    | .copy sz => return (line s!"__builtin_memcpy({a 0}, {a 1}, {sz});", c)
    | .tail m => return (line s!"bpf_tail_call(ctx, &{cname m}, {a 0});", c)
    | .fill sz => return (line s!"__builtin_memset({a 0}, {a 1}, {sz});", c)
    | .printk fmt =>
      let tys := args.map (exprTy c.Γ)
      let casts := (args.zip tys).map fun (e, t) =>
        match t with
        | .int _ 64 => s!"(long long)({cexpr (!c.program) e})"
        | .int true _ => s!"(int)({cexpr (!c.program) e})"
        | .int false _ => s!"(unsigned)({cexpr (!c.program) e})"
        | .ptr => cexpr (!c.program) e
      return (line s!"bpf_printk({Core.strLit (cfmt fmt tys)}{String.join (casts.map (", " ++ ·))});", c)
    | .atomic op s w fetch =>
      let p := s!"({ity s w} *)({a 0})"
      let call := match op with
        | .add => s!"__sync_fetch_and_add({p}, {a 1})"
        | .band => s!"__sync_fetch_and_and({p}, {a 1})"
        | .bor => s!"__sync_fetch_and_or({p}, {a 1})"
        | .bxor => s!"__sync_fetch_and_xor({p}, {a 1})"
        | .xchg => s!"__sync_lock_test_and_set({p}, {a 1})"
        | .cmpxchg => s!"__sync_val_compare_and_swap({p}, {a 1}, {a 2})"
      if fetch then return res (.int s w) call
      else return (line s!"(void){call};", c)
  | .kernel _ x h args =>
    let some decl := c.pre.call? h
      | return (line s!"/* unknown kernel function {h} */", c)
    let mk := args.findSome? fun
      | .mapPtr m => (c.maps.find? (·.name == m)).map (·.kind)
      | _ => none
    let call := kernelCall c.pre c.types c.kind decl (args.map (cexpr (!c.program))) mk
    match x with
    | some x =>
      -- a declaration yielding a reference or an owned object yields a pointer
      let t := match decl.sig with
        | .fn _ (some (.own ..)) | .fn _ (some (.ref ..)) | .fn _ (some (.view ..)) => LIR.Ty.ptr
        | _ => .i64
      if t == .ptr then return (line s!"void *{cname x} = {call};", bind x t)
      else return (line s!"s64 {cname x} = (s64){call};", bind x t)
    | none => return (line s!"{call};", c)

end

/-- The direct maps a program mentions, for the lookups at entry. -/
partial def directMapsIn (direct : List String) : List LIR.Stmt → List String
  | [] => []
  | s :: rest =>
    let inExpr : LIR.Expr → List String := fun e =>
      let str := e.print
      direct.filter fun m => (str.splitOn s!"mapval {m} +").length > 1
    let own := match s with
      | .«let» _ _ _ e | .assign _ _ e | .ctxStore _ _ e | .ret _ (some e) | .raise _ _ e => inExpr e
      | .store _ _ a e => inExpr (.addr a) ++ inExpr e
      | .ite _ c t e => inExpr c.l ++ inExpr c.r ++ directMapsIn direct t ++ directMapsIn direct e
      | .block _ b | .loop _ b => directMapsIn direct b
      | .call _ _ _ args u a =>
        args.flatMap inExpr ++ directMapsIn direct (u.getD []) ++ directMapsIn direct (a.getD [])
      | .builtin _ _ _ args | .kernel _ _ _ args => args.flatMap inExpr
      | _ => []
    own ++ directMapsIn direct rest

/-- Whether statements mention the packet's bounds, or call one of
the functions named. -/
partial def mentionsBounds (calls : List String) : List LIR.Stmt → Bool
  | [] => false
  | s :: rest =>
    let inExpr (e : LIR.Expr) : Bool :=
      let str := e.print
      (str.splitOn "pkt_data").length > 1 || (str.splitOn "pkt_end").length > 1
    let own := match s with
      | .«let» _ _ _ e | .assign _ _ e | .ctxStore _ _ e | .ret _ (some e) | .raise _ _ e => inExpr e
      | .store _ _ a e => inExpr (.addr a) || inExpr e
      | .ite _ c t e =>
        inExpr c.l || inExpr c.r || mentionsBounds calls t || mentionsBounds calls e
      | .block _ b | .loop _ b => mentionsBounds calls b
      | .call _ _ f args u a =>
        calls.contains f || args.any inExpr || mentionsBounds calls (u.getD []) ||
          mentionsBounds calls (a.getD [])
      | .builtin _ _ _ args | .kernel _ _ _ args => args.any inExpr
      | _ => false
    own || mentionsBounds calls rest

/-- The functions that take the packet's bounds as parameters: those
that mention them, for the element test of a view, and those that
call one of them. -/
partial def boundedFns (fns : List LIR.Fn) (acc : List String := []) : List String :=
  let acc' := fns.filterMap fun f =>
    if acc.contains f.name then none
    else if mentionsBounds acc f.body then some f.name else none
  if acc'.isEmpty then acc else boundedFns fns (acc ++ acc')

def cfn (pre : Interface) (types : List Core.TypeDecl) (fns : List LIR.Fn) (maps : List Core.MapDecl)
    (bounded : List String)
    (direct : List String) (f : LIR.Fn) : PM String := do
  let params := f.params.map fun p =>
    if p.ty == .ptr then s!"void *{cname p.name}" else s!"{cty p.ty} {cname p.name}"
  let params := params ++ (if bounded.contains f.name then ["void *pkt_data", "void *pkt_end"] else [])
  let extra := (match f.ret with
      | some t => if statusFn f then [s!"{cty t}{if t == .ptr then "" else " "}*out"] else []
      | none => []) ++ (if f.fails then ["u32 *reason"] else [])
  let ret := if statusFn f then "int" else match f.ret with
    | some t => cty t
    | none => "void"
  let c : PCtx := { pre, types, fns, maps, kind := "", status := statusFn f, program := false,
                    defaultVerdict := "0", bounded,
                    Γ := f.params.map fun p => (p.name, p.ty) }
  let (body, _) ← cstmts c 4 f.body
  let ps := if (params ++ extra).isEmpty then "void" else ", ".intercalate (params ++ extra)
  -- a global function is not inlined into a program's prologue, so
  -- it looks its direct maps up itself
  let lookups := if !f.global then [] else
    (directMapsIn direct f.body).eraseDups.flatMap fun m =>
      [s!"    void *{cname m}__val = bpf_map_lookup_elem(&{cname m}, &koit_zero);",
       s!"    if (!{cname m}__val) return{if ret == "void" then "" else " 0"};"]
  let zero := if lookups.isEmpty then [] else ["    u32 koit_zero = 0; (void)koit_zero;"]
  let head := if f.global then s!"__attribute__((noinline)) {ret}" else s!"static __always_inline {ret}"
  return s!"{head} {cname f.name}({ps})\n\{\n" ++
    "\n".intercalate (zero ++ lookups ++ body) ++ "\n}\n"

def cprogram (pre : Interface) (u : LIR.CompUnit) (p : LIR.Program) : PM String := do
  let decl := pre.kind? p.kind
  let hasPkt := (decl.map (·.hasPkt)).getD false
  let vt := match decl.map (·.verdictTy) with
    | some (.int _ s w) => LIR.Ty.int s w
    | _ => .u32
  let dflt : Nat := match decl with
    | some decl =>
      match decl.defaultExit with
      | .verdict name => (decl.verdicts.lookup name).getD 0
      | .value v => Machine.toNatMod v (LIR.Ty.width vt)
    | none => 0
  let dv := clit (LIR.Ty.width vt) dflt
  let c : PCtx := { pre, types := u.types, fns := u.fns, maps := u.maps, kind := p.kind, status := false,
                    program := true, defaultVerdict := dv, bounded := boundedFns u.fns,
                    Γ := [("reason", .u32)] }
  let ctxTy := ctxType pre p.kind
  let direct := (directMapsIn u.direct (p.body ++ p.handlers.flatMap (·.body))).eraseDups
  let lookups := direct.flatMap fun m =>
    [s!"    void *{cname m}__val = bpf_map_lookup_elem(&{cname m}, &koit_zero);",
     s!"    if (!{cname m}__val) return {dv};"]
  let (body, _) ← cstmts c 8 p.body
  let mut handlers : List String := []
  for h in p.handlers do
    let (hb, _) ← cstmts c 8 h.body
    handlers := handlers ++ [s!"handler_{h.kind.spelling}: \{"] ++ hb ++ ["    }"]
  -- the dispatch exists only where a failure reaches it, so that the
  -- label is never unused
  let reached := (body ++ handlers).any fun l => (l.splitOn "goto handler_dispatch").length > 1
  -- and the handlers when nothing jumps to one, dispatch or direct
  let anyHandler := body.any fun l => (l.splitOn "goto handler_").length > 1
  if !anyHandler && !reached then handlers := []
  -- the fall-off return stays either way
  let dispatch := if !reached then [s!"    return {dv};"] else
    ["handler_dispatch:", "    switch (koit_kind) {"] ++
    (Kind.all.map fun k => s!"    case {kindIndex k}: goto handler_{k.spelling};") ++
    ["    }", s!"    return {dv};"]
  let _ := hasPkt
  return s!"SEC(\"{(decl.map (·.section_)).getD p.kind}\")\n" ++
    s!"int {cname p.name}({ctxTy} *ctx)\n\{\n" ++
    "    u32 reason = 0; int koit_kind = 0; u32 koit_zero = 0;\n" ++
    "    (void)reason; (void)koit_kind; (void)koit_zero;\n" ++
    "\n".intercalate lookups ++ (if lookups.isEmpty then "" else "\n") ++
    "    {\n" ++ "\n".intercalate body ++ "\n    }\n" ++
    "\n".intercalate (handlers ++ dispatch) ++ "\n}\n"

/-- The named struct types in an order that defines each before its
first use. -/
partial def orderedTypes (types : List Core.TypeDecl) : List Core.TypeDecl :=
  let rec names : Core.Ty → List String
    | .named _ n => [n]
    | .struct _ fs => fs.flatMap fun f => names f.ty
    | .array _ e _ => names e
    | .refined _ _ b _ => names b
    | _ => []
  let rec go (done pending : List Core.TypeDecl) (fuel : Nat) : List Core.TypeDecl :=
    match fuel with
    | 0 => done ++ pending
    | fuel + 1 =>
      let ready := pending.filter fun d => (names d.ty).all fun n =>
        done.any (·.name == n) || !pending.any (·.name == n)
      if ready.isEmpty then done ++ pending
      else go (done ++ ready) (pending.filter fun d => !ready.any (·.name == d.name)) fuel
  go [] types types.length

/-- The kernel's map type of a map declaration, by its enum name. -/
def mapTypeName : Core.MapKind → String
  | .array .. => "BPF_MAP_TYPE_ARRAY"
  | .percpu .. => "BPF_MAP_TYPE_PERCPU_ARRAY"
  | .hash .. => "BPF_MAP_TYPE_HASH"
  | .ringbuf .. => "BPF_MAP_TYPE_RINGBUF"
  | .progArray .. => "BPF_MAP_TYPE_PROG_ARRAY"
  | .sockmap .. => "BPF_MAP_TYPE_SOCKMAP"
  | .sockhash .. => "BPF_MAP_TYPE_SOCKHASH"

def cmap (types : List Core.TypeDecl) (d : Core.MapDecl) : String :=
  let count (n : Core.Expr) : String := match n with
    | .lit _ v _ => toString v
    | e => e.print
  let valueName := s!"koit_{d.name}_v"
  let keyName := s!"koit_{d.name}_k"
  let mname := cname d.name
  let typeDef (name : String) (t : Core.Ty) : String :=
    match t with
    | .named .. | .int .. | .be .. | .bool .. => ""
    | t => s!"struct {name} \{ " ++
        (match t with
         | .struct _ fs => String.join (fs.map fun f => cdecl types f.ty (cname f.name) ++ "; ")
         | t => cdecl types t "v" ++ "; ") ++ "};\n"
  let typeRef (name : String) (t : Core.Ty) : String :=
    match t with
    | .named _ n => s!"struct {cname n}"
    | .int _ s w => ity s w
    | .be _ w => s!"u{w}"
    | .bool _ => "u8"
    | _ => s!"struct {name}"
  match d.kind with
  | .array n v =>
    typeDef valueName v ++
    s!"struct \{ __uint(type, {mapTypeName d.kind}); __uint(max_entries, {count n}); \
      __type(key, u32); __type(value, {typeRef valueName v}); } {mname} SEC(\".maps\");\n"
  | .percpu n v =>
    typeDef valueName v ++
    s!"struct \{ __uint(type, {mapTypeName d.kind}); __uint(max_entries, {count n}); \
      __type(key, u32); __type(value, {typeRef valueName v}); } {mname} SEC(\".maps\");\n"
  | .hash n k v =>
    typeDef keyName k ++ typeDef valueName v ++
    s!"struct \{ __uint(type, {mapTypeName d.kind}); __uint(max_entries, {count n}); \
      __type(key, {typeRef keyName k}); __type(value, {typeRef valueName v}); } {mname} \
      SEC(\".maps\");\n"
  | .ringbuf n =>
    s!"struct \{ __uint(type, {mapTypeName d.kind}); __uint(max_entries, {count n}); } \
      {mname} SEC(\".maps\");\n"
  | .progArray n _ =>
    s!"struct \{ __uint(type, {mapTypeName d.kind}); __uint(max_entries, {count n}); \
      __uint(key_size, 4); __uint(value_size, 4); } {mname} SEC(\".maps\");\n"
  -- the sockets are the kernel's; the value is the socket's word
  | .sockmap n =>
    s!"struct \{ __uint(type, {mapTypeName d.kind}); __uint(max_entries, {count n}); \
      __uint(key_size, 4); __uint(value_size, 4); } {mname} SEC(\".maps\");\n"
  | .sockhash n k =>
    typeDef keyName k ++
    s!"struct \{ __uint(type, {mapTypeName d.kind}); __uint(max_entries, {count n}); \
      __type(key, {typeRef keyName k}); __uint(value_size, 4); } {mname} \
      SEC(\".maps\");\n"

/-- Whether the text calls a C function by name. -/
def calls (text name : String) : Bool := (text.splitOn s!"{name}(").length > 1

/-- The declarations the kernel side supplies for a unit's C: the
context struct of each kind its programs have, laid out from the
transcribed offsets with a static assertion per field; the helpers
the body calls, each at its number with its transcribed prototype;
and the kfuncs it calls as `__ksym` externs. The shim's `bpf_printk`
expands to `bpf_trace_printk`, which is declared whenever the macro
is used. -/
def kernelDecls (pre : Interface) (u : LIR.CompUnit) (body : String) : String :=
  let kinds := (u.programs.map (·.kind)).eraseDups
  let ctxs := kinds.filterMap fun k =>
    (pre.kind? k).bind fun r => (pre.side.progType? r.progType).bind fun t =>
      t.ctx.bind pre.side.ctx?
  let ctxDecl (s : CtxStruct) : String :=
    let field (f : CtxField) (i : Nat) : String :=
      let name := if f.name == "" then s!"koit_pad_{i}" else f.name
      -- the wider fields of the context structs are IPv6 addresses
      -- and `cb`, arrays of `__u32`
      let decl := match f.size with
        | 1 => s!"u8 {name}" | 2 => s!"u16 {name}" | 4 => s!"u32 {name}" | 8 => s!"u64 {name}"
        | n => if n % 4 == 0 && f.name != "" then s!"u32 {name}[{n / 4}]" else s!"u8 {name}[{n}]"
      s!"\t{decl};\n"
    let asserts := s.fields.filter (·.name != "") |>.map fun f =>
      s!"_Static_assert(__builtin_offsetof({s.name}, {f.name}) == {f.offset}, \"{s.name}.{f.name}\");\n"
    -- fields at one offset are the members of an anonymous union
    let groups := s.fields.zipIdx.foldl (fun (gs : List (List (CtxField × Nat))) fi =>
      match gs with
      | g :: rest =>
        if g.any (·.1.offset == fi.1.offset) then (g ++ [fi]) :: rest else [fi] :: g :: rest
      | [] => [[fi]]) [] |>.reverse
    let group (g : List (CtxField × Nat)) : String :=
      match g with
      | [(f, i)] => field f i
      | _ => "\tunion {\n" ++ String.join (g.map fun (f, i) => "\t" ++ field f i) ++ "\t};\n"
    s!"/* {s.name}, include/uapi/linux/bpf.h of {pre.kernel} */\n{s.name} \{\n" ++
      String.join (groups.map group) ++ "};\n" ++
      s!"_Static_assert(sizeof({s.name}) == {s.size}, \"{s.name}\");\n" ++ String.join asserts
  let helperDecl (h : Helper) : String :=
    let args := h.args.map fun (t, n) => if t == "..." then "..." else s!"{kernelCTy t} {n}"
    let ps := if args.isEmpty then "void" else ", ".intercalate args
    s!"static {kernelCTy h.ret} (*bpf_{h.name})({ps}) = (void *){h.id};\n"
  let used (h : Helper) : Bool :=
    calls body s!"bpf_{h.name}" || (h.name == "trace_printk" && calls body "bpf_printk")
  let helpers := pre.side.helpers.filter used
  let kfuncDecl (k : Kfunc) : String :=
    let args := k.args.map fun (t, n) => s!"{kernelCTy t} {n}"
    let ps := if args.isEmpty then "void" else ", ".intercalate args
    s!"extern {kernelCTy (if k.ret == "" then "void" else k.ret)} {k.name}({ps}) __ksym;\n"
  let kfuncs := pre.side.kfuncs.filter fun k => calls body k.name
  let mapTypes := pre.side.mapTypes.filter fun (n, _) =>
    (u.maps.map fun d => C.mapTypeName d.kind).contains n
  let values := ["BPF_ANY"].filterMap fun n => (pre.side.value? n).map (n, ·)
  s!"/* enum bpf_map_type and the flags, include/uapi/linux/bpf.h of {pre.kernel} */\nenum \{\n" ++
  String.join (mapTypes.map fun (n, v) => s!"\t{n} = {v},\n") ++
  String.join (values.map fun (n, v) => s!"\t{n} = {v},\n") ++ "};\n\n" ++
  String.join (ctxs.map (· |> ctxDecl |>.push '\n')) ++
  (if helpers.isEmpty then "" else
    s!"/* the helpers, by their numbers in enum bpf_func_id of {pre.kernel} */\n" ++
    String.join (helpers.map helperDecl) ++ "\n") ++
  (if kfuncs.isEmpty then "" else
    s!"/* the kfuncs of {pre.kernel} */\n" ++ String.join (kfuncs.map kfuncDecl) ++ "\n")

end C

/-- The C of a unit's LIR, before inlining. -/
def emitC (pre : Interface) (u : LIR.CompUnit) : String :=
  let types := C.orderedTypes (u.types.filter fun d => match d.ty with
    | .struct _ (_ :: _) => true
    | _ => false)
  let typeDefs := types.map fun d =>
    match d.ty with
    | .struct _ fs =>
      s!"struct {C.cname d.name} \{\n" ++
        String.join (fs.map fun f => "    " ++ C.cdecl u.types f.ty (C.cname f.name) ++ ";\n") ++ "};\n"
    | _ => ""
  let go : C.PM (List String × List String) := do
    let bounded := C.boundedFns u.fns
    let fns ← u.fns.mapM (C.cfn pre u.types u.fns u.maps bounded u.direct)
    let progs ← u.programs.mapM (C.cprogram pre u)
    return (fns, progs)
  let ((fns, progs), _) := go.run 0
  let body := String.join (fns.map (· ++ "\n")) ++ String.join (progs.map (· ++ "\n"))
  "/* emitted by koitc from LIR; the total-arithmetic shim is koit.h */\n" ++
  "#include \"koit.h\"\n\n" ++
  C.kernelDecls pre u body ++
  String.join (typeDefs.map (· ++ "\n")) ++
  String.join (u.maps.map fun d => C.cmap u.types d ++ "\n") ++
  body ++
  s!"char _license[] SEC(\"license\") = \"{u.license.getD "GPL"}\";\n"

end Koit.Compile
