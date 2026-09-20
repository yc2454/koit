# koit language definition, draft 3

Status: draft 3, 2026-09-12. Supersedes draft 2 (2026-09-11), whose
text is kept verbatim at `archive/language-draft2.md`. Draft 3 folds
in the decisions of `mechanisms-draft3.md`, which
re-derived the mechanisms against the kernel's own state
(`verifier-checks.md`, upstream v7.0). Changes from draft 2:

1. One runtime coercion, `e as T?` for a refinement type `T`, is the
   only way to establish a fact at runtime; `check P` is sugar for it
   (sections 8.3, 10.4, 18.4).
2. `with` is renamed `hold`; resource constructors after it are prelude
   names, not keywords (sections 5, 11).
3. Ownership: `own T` in prelude signatures, and `move x` as the one
   sanctioned escape of a place, with join consistency instead of
   runtime flags (sections 7, 11.5, 18.4).
4. Guards: a place's validity may be tied to a held resource or to the
   packet layout; view invalidation is the first row of that table
   (section 12).
5. Views are the one operation for any region of dynamic extent; the
   packet is the instance this draft defines (section 7).
6. Places are second class: never stored, returned, or compared
   (sections 7, 8.3).
7. Loops: the cap is the bound's type, as before, now stated as such;
   iterator loops `for x in it bounded N` with `?` making the cap a
   failure (sections 9, 18.4). `bpf_loop`, open-coded iterators, and
   `may_goto` are lowering targets, never source constructs.
8. The `sleep` effect; sleepability is a column of the kind table
   (sections 12, 13).
9. The reason of a `helper` failure defaults to the helper's negative
   return (section 10.5).
10. Principle P9, elide only what the verifier will see; the entailment
    fragment is fixed by acceptance, not expressiveness; no solver in
    the type system; the path-fact lemma (sections 3, 18.5, 20).
11. `license` declaration per unit (section 6).
12. Slot types: the storage side of M3 is a table like the acquisition
    side; `spinlock` is its one stage-1 row, not a keyword (sections
    5, 7, 11, 18.1).
13. The prelude's six tables are specified: kinds, context fields,
    calls, resources, regions, slots; the target kernel is a compiler
    input; `const` parameters; sleepable kinds as rows; the trusted
    columns (sections 6, 7, 12, 13, 16, 20).
14. `own T` uniformly; the acquisition's argument form is a column;
    lexical scoping of resources stated as a non-claim (sections 7,
    8.3, 11).
15. The callback-loop rules recorded with the deferral of iterator
    and map loops (section 22).
16. Lemma L's two lowering obligations (section 20).

Changes from draft 1 to draft 2, for the record:

1. Arithmetic is total, with the kernel's semantics for division,
   modulo, and shifts (section 8.1); the divisor and shift-amount
   demands are gone and `check` is the only source of the `bound` kind.
2. Views carry their offset as a fact (section 7); stores through them
   carry region-indexed write effects (section 12).
3. Contracts: verdict sets, preserved regions, named contracts a program
   implements (section 14).
4. Configuration constants supplied at build time (section 15).
5. Atomic updates on map places (section 8.5).
6. The safety theorem is split into named properties with the mechanism
   that provides each, and the corollary about verifier bugs is stated
   with its condition (section 20).
7. Entailment is treated as soundness-critical: a solver cross-check
   mode and a mechanization plan (section 18.5).
8. Sections 2 and 3 are rewritten around the thesis, with the
   correspondence between the verifier's checks and the language.
9. Closed questions: `fails` is explicit; reasons are `u32`; the marker
   is `?`; signed division follows the kernel; packet byte writes use
   the two-line form. Deferred extensions are collected in section 22.

Revisions after draft 3, folded on 2026-09-13 from `ISSUES.md` (the
entry numbers are that file's):

1. Core is the one typed language; the surface desugars to it
   syntactically, and functions, constant conditionals, and `for` stay
   in Core until checked (entry 8; sections 3, 18.1, 18.4, 20).
2. Struct literals with scalar fields are stack places; Q2 closed
   (entry 3; sections 8.2, 21).
3. A `syscall` body may fall off its end and returns 0; a packet body
   must exit (entry 1; sections 9, 13).
4. A function body may end in an expression, its result (entry 7;
   sections 9, 16).
5. The prelude is a table the compiler carries, hand-written for stage
   1; protocol numbers are prelude constants (entry 5; section 6).
6. The newline rule's scope, `else` placement, and `abort` (entry 6;
   sections 5, 9).

Revisions folded on 2026-09-14 from `ISSUES.md`:

1. Twelve points of Core representation the grammar of 18.1 left open,
   decided in the implementation and now part of the definition (entry
   11; sections 6, 8.2, 8.4, 16, 18.1).
2. Iterator loops range over the resource table's iterator rows, which
   this draft leaves to the extensions; the form is parse-only until
   then (entry 12; sections 9, 11.2).
3. A `T?` function returns absence with a bare `return`; `T` is a
   scalar (entry 9; sections 7, 16).
4. One spelling of the header fields across the documents, the
   kernel's (`protocol`, `source`, `dest`); the socket lookups take the
   tuple only, of the prelude type `SockTuple` (entry 4; sections 11.2,
   11.5, 23.3).
5. The `except` list of `preserve maps` runs to the end of the clause;
   a block comment spanning lines counts as a newline (entry 10;
   sections 5, 14.1).

Revision folded on 2026-09-18 from `ISSUES.md`:

1. The dynamic semantics is a big-step relation over a machine,
   parameterized by a kernel that stands for the helpers' choices;
   the frames of the earlier small-step account are the enclosing
   rules, and T1 quantifies over every kernel within its contracts
   (entry 20; sections 19, 20).

Revisions folded on 2026-09-19 from `ISSUES.md` entries 25 to 27:

1. Two fact rules the lowering's view-offset demand needed: an
   increment bound at a loop head and the preservation of what a
   killed equation said of its other side (section 18.4).
2. The machine's trace and held stack in the form every level of the
   lowering shares (section 19.1).

Reading guide. Sections 2 to 17 are the surface language and can become
the manual. Sections 18 to 20 are the formal part. Section 23 gives the
program template and examples.

## 1. The core and the extensions

koit is a core language plus an extension per program type.

The core is independent of program type: the four mechanisms, the
failure model, contracts, configuration, functions, maps, and the formal
semantics of sections 18 to 20. Everything a program type contributes is
a set of tables the core consumes: its region kinds, what memory the
program can see and how a place in it is obtained; its context type; its
verdict type and default failure verdict; the resources it may hold;
and the kernel functions it may call, with their signatures and effects.
The verifier is organized the same way, by program type, and the tables
are generated from its own.

Defined in this draft: the packet extension, for XDP and TC programs,
whose region is the packet, obtained through views, and whose resources
are spin locks, RCU sections, ring-buffer records, and socket
references; and the syscall extension, for control-path programs, with
no packet and an `i32` verdict.

Designed but not defined, in section 22: the kernel-memory extension
for tracing and LSM programs, and the struct-ops extension for
schedulers. Deferred features that are not tied to a program type: tail
calls, separately verified global functions, the userspace boundary,
user-defined resources, conditional verdicts, contracts on functions.

Reserved syntax with no semantics yet: `invariant`.

## 2. The thesis

The kernel verifier accepts a program only after establishing four kinds
of fact about its bytecode: every memory access lies in a known region,
every loop is bounded, every acquired resource is released, and every
kernel call respects its contract. It infers those facts from
instructions and checks each instruction's premises against them.

The verifier is thus an abstract interpreter doing a type checker's
job without a source language: it infers a typing the programmer was
never allowed to write, then checks every instruction against it
(`motivation.md`, section 1).

koit's thesis is that the conditions the verifier checks can be stated
as a type system at the source, and koit is that type system. Its types
express the premises, and the program supplies the facts by
declaration, each written once where the programmer already knows it.
The verifier still checks; it no longer has to discover.

| the verifier | type theory | koit |
|---|---|---|
| register kinds: scalar, packet, map value, stack, context | base and region types | integers, `view`, `ref`, `ctx` |
| bounds and known bits on a scalar | refinement types | `where`, loop index types |
| a packet pointer's valid range after a comparison | a refinement established by a test | carving a view |
| pointer-or-null kinds and the required null test | option types | fallible operations, `?`, `if let` |
| acquired references that must be released | linear types | `hold` blocks |
| a held spin lock and the calls forbidden under it | typestate, effect restrictions | resource table |
| packet pointers invalidated by a resize | capability revocation | view invalidation |
| bounded loops walked to convergence | termination checking | declared bounds |
| helper prototypes | function types with effects | prelude signatures |
| branch refinement | path-sensitive typing | facts from conditions |
| pruning by state subsumption | subtyping | entailment |

The verifier's system and koit's are two systems, not one. The
verifier's works on bytecode with inferred refinements and path
enumeration; koit's works on source with declared refinements, merges
facts at joins, and is compositional. koit's soundness is its own
theorem (section 20). The link between them, that a well-typed program
compiles to bytecode satisfying the verifier's premises, is a property
of the compiler, established by construction of the lowering and
validated empirically; it is outside this definition.

## 3. Principles

- **P1, declare once.** A safety fact is stated in one declaration and
  every use governed by it is checked against it.
- **P2, no unmarked failure.** Every operation that can fail at runtime
  is marked at its site, and every failure reaches a handler declared
  once per program. The compiler never inserts control flow the source
  does not show, except a branch the verifier requires on a path the
  kernel's contract makes unreachable, such as the null test after an
  array-map lookup whose index is in range; such a branch ends in the
  kind's default failure verdict, so that a violation of the contract
  stays visible.
- **P3, scalars are values, aggregates are places.** Structs and arrays
  are never copied implicitly; binding one names its location.
- **P4, no implicit conversions.** Width, signedness, and byte order
  change only through explicit operations.
- **P5, total arithmetic, the kernel's way.** Every arithmetic operation
  is defined on every input, with exactly the semantics the kernel's
  instruction set gives it. There is no undefined behavior to exclude.
- **P6, structured and bounded.** No goto, no unbounded loop, no
  recursion. Termination holds by construction.
- **P7, small core.** The surface desugars to Core (section 18); the
  typing rules and the theorems are about Core.
- **P8, the environment is untrusted.** Packet bytes, and map contents
  written by userspace or other programs, are data. A fact about them
  exists only after this program has tested it.
- **P9, elide only what the verifier will see.** The checker discharges
  a demand silently only when the verifier will re-establish the same
  fact from the emitted code. Every fact the checker uses lowers to a
  branch in the bytecode (Lemma L, section 20), and the entailment
  fragment decides only what the verifier's domain re-derives from
  such branches (section 18.5). A stronger fragment would elide tests
  the verifier cannot see and produce safe programs that do not load.

## 4. The mechanisms

**M1, refinement types over fixed-width integers.** An integer has a
base type and optionally a predicate over its value and other names in
scope, written `{v: u32 | v < 16}`. The checker carries a set of facts
along each path, from branch conditions, from declared types, from
marked loads, and from `check`. Positions that demand a refinement, an
array index, a store into a predicated field, an argument with a
precondition, a return under a verdict set, are accepted when the facts
entail the demand and are type errors otherwise. Sections 7, 16, 17.

**M2, places with typed extents.** A place is a location the program can
read or write; its type fixes its extent; every place lies in a region:
the stack frame, a map value, a context, or the packet. Regions with a
static layout yield places statically. A region of dynamic extent, the
packet in this draft, yields a place only through a view, which tests
at runtime that a window of the view's type exists and remembers where.
Scalars are values, aggregates are places, and references and views are
names of places. Places are second class: they are never stored,
returned, or compared, and the one sanctioned escape is the typed
ownership transfer of M3. Sections 7, 8.

**M3, effects, ownership, and protocols.** Each function has an effect
set: whether it may call the kernel, resize the packet, sleep, fail,
and which regions it may write. Three parts share one resource table.
A scoped resource is acquired at the entry of a `hold` block and
released on every exit of it, with an action that depends on the
resource and on whether the exit was normal; while it is held, some
effects are forbidden. An owned reference bound by `hold` may instead
be handed away with `move`, the one escape a place has, and the scope
then does not release it. A guarded place is valid only while its
guard is held: a packet view until a resize, an RCU pointer until the
outermost unlock, a graph node until its lock is released. Sections
11, 12.

**M4, bounded structured control.** Conditionals, loops, break,
continue, return, and calls in an acyclic call graph. A loop's cap is
the type of its bound: a constant, a configuration constant, or a
refined runtime value; the one declaration is the termination measure,
the index's refinement, and the constant the verifier needs to
converge. Iterator loops carry a cap. The kernel's loop mechanisms,
`bpf_loop`, open-coded iterators, and `may_goto`, are forms the
compiler chooses from the cap, never constructs the programmer writes.
Section 9.

**F, the failure model.** Failures have six kinds fixed by the language,
one per party to blame. A fallible operation appears only on the right
of a binding, marked with `?` or with an `else` block that must exit;
the runtime coercion `e as T?` is one such operation. A failure carries
a reason and goes to the handler its program declared for its kind, or
to the program's default. `fail` is an effect and the handlers are its
one, abortive, handler per entry point. Section 10.

**Why these four.** They are the classes of judgment the verifier
makes. `verifier-checks.md` classifies every rejection message of the
verifier's source by what is judged: of the 293 that concern a
program's behavior, 187 judge a value, a region, a protocol, or the
control structure, one per mechanism, and the remaining 106 judge an
interface that typed signatures compose from the four. The failure
model is not a fifth class: it is the language's answer to what a
runtime test does when it fails, which the verifier has no notion of
because it has no source.

## 5. Lexical structure and keywords

Identifiers: `[A-Za-z_][A-Za-z0-9_]*`. Integer literals: decimal, `0x`
hexadecimal, `0b` binary, with `_` separators. Character literals `'a'`,
`'\n'`, `'\x20'` denote `u8`. String literals appear only as the format
argument of `printk`. Comments: `//` to end of line and `/* ... */`
without nesting. A newline ends a statement or declaration unless the
line ends with a token that cannot end one: an operator, a comma, `of`,
`->`, `=`, or an opening bracket. `;` is accepted as a separator. The
rule applies inside blocks and between top-level items; inside
brackets, in a program header up to its body, and in a contract, a
newline is whitespace. An `else` follows its `}` on the same line. A
block comment that spans lines counts as a newline.

Reserved keywords:

```
as  bounded  break  check  config  const  continue  contract  drop  else
except  fail  fails  false  fn  for  hold  if  implements  in  let
license  map  move  of  on  own  pass  preserve  program  ref  repeat
return  true  tx  type  var  verdict  view  where
```

Reserved for later drafts: `invariant extern struct enum while match
global import unsafe resource defer`.

Contextual names, ordinary identifiers whose meaning is fixed by
position: map kinds `array percpu_array hash ringbuf`; program kinds
`xdp tc syscall`; failure kinds `short_packet missing invariant bound
helper program`; resource constructors `lock rcu preempt_off irq_off
reserve` and the acquiring kernel functions, all from the resource
table, so that a new kernel resource adds a row and not a keyword; slot
types such as `spinlock`, from the slot table, likewise; the verdict
`abort`, which is the verdict statement when it stands alone in
statement position; the region name `maps`; the implicit objects `pkt ctx reason`;
the primitive types.

Operators and precedence, tightest first: postfix `.f` `[e]` `(args)`;
unary `!` `-` `*`; `as`; `* / %`; `+ -`; `<< >>`; `&`; `^`; `|`;
comparisons, non-associative; `&&`; `||`.

## 6. Compilation units and declarations

A file is one compilation unit and compiles to one object whose programs
share the unit's maps. A prelude of header types, kernel function
signatures, slot types, and the six tables of section 13 is generated
from the kernel and supplied by the compiler for the kernel the unit is
compiled for, named by the compiler's `--kernel` option; stage 1 has
one, `v7.0`. A call, kind, or slot the target kernel lacks is a type
error naming that kernel. The prelude is a table the compiler carries,
not a source file: for stage 1 it is written by hand for `xdp`, `tc`,
and `syscall` and the helpers the examples call, and the generator
later emits the same table. Protocol and ethertype numbers such as
`IPPROTO_UDP` and `ETH_P_IP` are prelude constants. Declarations are
visible throughout the unit. The prelude is an outer scope: a
declaration of the unit with the same name as a prelude constant or
type shadows it.

```
Unit      ::= LicenseDecl? Item*
Item      ::= ConstDecl | ConfigDecl | TypeDecl | MapDecl | FnDecl
            | ContractDecl | ProgDecl

LicenseDecl ::= 'license' String
ConstDecl ::= 'const' Ident (':' Type)? '=' Expr
ConfigDecl ::= 'config' Ident ':' Type ('=' Expr)?
TypeDecl  ::= 'type' Ident '=' Type
MapDecl   ::= 'map' Ident ':' MapType
MapType   ::= 'array' '[' Expr ']' 'of' Type
            | 'percpu_array' '[' Expr ']' 'of' Type
            | 'hash' '[' Expr ']' 'of' Type '->' Type
            | 'ringbuf' '[' Expr ']'
FnDecl    ::= 'fn' Ident '(' Params? ')' ('->' RetType)? 'fails'? Block
Params    ::= Param (',' Param)*
Param     ::= Ident ':' Type ('where' Pred)?
RetType   ::= Type | Type '?' | Ident ':' Type 'where' Pred
ContractDecl ::= 'contract' Ident ':' ProgKind '{' Clause* '}'
Clause    ::= 'verdict' 'in' '{' Ident (',' Ident)* '}'
            | 'preserve' Region (',' Region)*
Region    ::= 'pkt' ('[' Expr '..' Expr ')')?
            | 'maps' ('except' Ident (',' Ident)*)?
            | Ident | 'ctx' '.' Ident
ProgDecl  ::= 'program' Ident ':' ProgKind ('implements' Ident)?
              Clause* ('fail' Exit)? Handler* Block
Handler   ::= 'on' KindList Block
KindList  ::= Kind (',' Kind)* | '_'
Kind      ::= 'short_packet' | 'missing' | 'invariant' | 'bound'
            | 'helper' | 'program'
ProgKind  ::= 'xdp' | 'tc' | 'syscall'
```

`license "GPL"` declares the unit's license; kernel functions the
kernel marks GPL-only are available only under a GPL-compatible
license, and a call to one otherwise is a type error naming the
function. A `const` without a type annotation takes its type from each
use, like a literal; with an annotation it is monomorphic. A `config`
is a constant whose value is supplied at build time (section 15).
Constant expressions (section 8.4) may use both.

## 7. Types

```
Type      ::= IntType | 'bool' | Ident
            | '{' Field (',' Field)* ','? '}'
            | '{' Ident ':' Type '|' Pred '}'
            | Type '[' Expr ']'
            | 'ref' Type | 'view' Type | Type '?'
            | 'own' Type                      -- prelude signatures only
Field     ::= Ident ':' Type ('where' Pred)?
IntType   ::= 'u8' | 'u16' | 'u32' | 'u64' | 'i8' | 'i16' | 'i32' | 'i64'
            | 'be16' | 'be32' | 'be64'
```

An `Ident` names a declared type, a prelude type such as `Sock`, or a
slot type such as `spinlock`.

**Integers.** `uN` and `iN` are fixed-width with wrapping arithmetic
modulo 2^N. No implicit widening or narrowing.

**Byte-order integers.** `be16`, `be32`, `be64` hold network byte order.
They support `==`, `!=`, loads, and stores, and nothing else. `ntoh`
converts to the host-order unsigned type, `hton` converts from it, and
`hton(k)` on a constant is folded.

**Booleans.** `bool` is distinct from integers; `b as uN` is 0 or 1.

**Structs.** Fields in declaration order at natural alignment, no
reordering, so a declaration matches the C layout the kernel uses.
Every place, a local, a map value, or a view, is aligned to its type's
natural alignment, and `copy` and `fill` are typed by the extent of
their operands; a wide access through a misaligned stack object, a
recurring verifier rejection in production C, cannot be written.
`T.size` is the padded size. A field may carry a `where` predicate
(section 17) that may mention sibling fields. A field may have a slot
type, subject to the slot's row.

**Slot types.** The kernel recognizes a family of special fields in a
map value, a global-data section, or an allocated object: locks,
timers, work queues, list and tree heads and nodes, reference counts,
and kernel-pointer fields. koit calls them slot types. A slot type is an
opaque type supplied by the prelude's slot table and named like any
type. It has a size and an alignment; it is not data, so a place of a
slot type is never read, written, copied, compared, viewed, or refined;
it appears only where its row allows; a row marked unique admits one
such field per value; and a value holds at most eleven slots in all,
the kernel's limit. What names a slot is the acquisition, `move` sink,
or program kind its row points to: a spin lock is named by `lock(p)`.

| column | meaning |
|---|---|
| name, kernel name | the koit spelling and the BTF type the kernel recognizes |
| size, alignment | its layout |
| homes | where a field of the type may live: a map value, global data, an allocated object |
| unique | at most one per value |
| named by | the resource row, `move` sink, or program kind that uses it |

Stage 1 has one row, `spinlock`: `bpf_spin_lock`, 4 bytes at 4, in map
values, unique, named by `lock(p)`. The extensions add
`bpf_res_spin_lock` (unique; `lock(p)?`), `bpf_timer`, `bpf_wq`, and
`bpf_task_work` (unique; the asynchronous callback kinds),
`bpf_list_head` and `bpf_rb_root` (`move` insertion sinks, guarded by
the value's lock), `bpf_list_node`, `bpf_rb_node`, and `bpf_refcount`
(fields of allocated object types), and the kernel-pointer fields
(exchange sinks), all as rows and none as keywords. The kernel's other
protocol storage, dynptrs, iterators, and IRQ flags, lives in stack
slots the verifier types; koit has no user type for those, because
they are `hold`-bound names (section 11).

**Arrays.** `T[n]` for constant `n`. Indexing demands `i < n` of an
unsigned index.

**Refinements.** `x: T where P` gives `x` the type `{v: T | P[x := v]}`.
Refinements appear on struct fields, function parameters and results,
local declarations, and, written as `{v: T | P}`, as the target of the
runtime coercion `e as {v: T | P}?` (section 8.3).

**References.** `ref T` names a place of type `T` in the stack or in a
map value. References arise from binding an aggregate place and from
`ref` parameters. A reference into a map value stays valid for the
whole run.

**Places are second class.** References and views are names of places,
not values: they cannot be stored into maps or aggregates, cannot be
returned from a program, and cannot be compared, not even for
equality. The kernel's leak, null-identity, and pointer-comparison
checks have nothing to apply to. The one sanctioned escape is `move`
on an owned reference (section 11.5).

**Views.** `view T` names a place in a region of dynamic extent whose
window has been tested; the packet is the one such region this draft
defines, and dynptr slices and runtime-sized memory are instances the
extensions add with the same construct. `T` must be
packet-representable: integers, byte-order integers, arrays and structs
of those, without slot types, `ref`, `view`, `own`, or optionals.
Carving `let h = pkt.view<T>(e)` also records the fact `off(h) = e`,
the view's offset, which the write effects of section 12 use. A view
is guarded by its region's layout token (section 12): any statement
with the `resize` effect drops the token and kills every live view.

**Owned references.** `own T` is the type of a reference the program is
responsible for releasing: the result of a kernel function the kernel
marks as acquiring. It appears only in prelude signatures. User code
obtains one by binding it with `hold` (section 11) and disposes of it
either by letting the scope release it or by handing it to a sink with
`move` (section 11.5). `T` is the type of the place the reference
names, `own Sock`, `own Event`; `ref` is never written under `own`.

**Optionals.** `T?` is the result type of a fallible operation whose
failure kind is `missing`: a hash lookup, or a function declared to
return `T?`, where `T` is a scalar, since places are never returned.
An optional is consumed only by a binding with a failure marker
(section 10); a function produces absence with a bare `return`
(section 16).

**Map types.** `array[n] of V`, `percpu_array[n] of V`, `hash[n] of
K -> V`, and `ringbuf[n]` for a ring buffer of `n` bytes. `K` and `V`
are packet-representable, `V` may contain slot types per their rows.
For a per-CPU
array, `m[i]` is the current CPU's slot.

## 8. Expressions and places

```
Expr      ::= Or
Or        ::= And ('||' And)*
And       ::= Cmp ('&&' Cmp)*
Cmp       ::= BitOr (CmpOp BitOr)?
BitOr     ::= BitXor ('|' BitXor)*
BitXor    ::= BitAnd ('^' BitAnd)*
BitAnd    ::= Shift ('&' Shift)*
Shift     ::= Add (('<<' | '>>') Add)*
Add       ::= Mul (('+' | '-') Mul)*
Mul       ::= Cast (('*' | '/' | '%') Cast)*
Cast      ::= Unary ('as' Type)*
Unary     ::= ('!' | '-' | '*') Unary | 'move' Ident | Postfix
Postfix   ::= Primary Suffix*
Suffix    ::= '.' Ident | '[' Expr ']' | '(' Args? ')'
            | '.' 'view' '<' Type '>' '(' Expr ')'
            | '.' 'reserve' '<' Type '>' '(' ')'
            | '.' 'size'
Primary   ::= Literal | Ident | 'pkt' | 'ctx' | 'reason' | '(' Expr ')'
            | '{' FieldInit (',' FieldInit)* ','? '}'
FieldInit ::= Ident ':' Expr
Place     ::= Ident ('.' Ident | '[' Expr ']')* | '*' Ident
```

### 8.1 Arithmetic, comparison, casts

Binary arithmetic and bitwise operators take two operands of one integer
type and yield it. Every operation is total, with the semantics of the
kernel's instruction set (P5):

| operation | on `uN` | on `iN` |
|---|---|---|
| `x / 0` | `0` | `0` |
| `x % 0` | `x` | `x` |
| `MIN / -1` | | `MIN` |
| `MIN % -1` | | `0` |
| `x << s`, `x >> s` | amount masked to `s & (N - 1)` | same; `>>` is arithmetic on `iN` |
| all others | wrap modulo 2^N | wrap modulo 2^N |

A programmer who wants a zero divisor to be a failure writes
`check d != 0` first. Comparison takes two operands of one type and
yields `bool`; byte-order types compare only with `==` and `!=`. `e as T`
converts between integer types: truncation to a narrower width, zero
extension from unsigned, sign extension from signed. `bool as uN` is 0
or 1.

### 8.2 Places, loads, binding

A place denotes memory: a local, a map slot `m[i]` of an array kind, a
field, an element, or `*x` for a reference or view `x` of scalar type.
Reading a scalar place loads it. Binding an aggregate place with `let`
names it (P3). A load from a field with a `where` predicate yields the
base type; the predicate becomes a fact only through a marked load
(section 10.2).

A struct literal `{ f: e, ... }` names a new place on the stack. Its
type is the declared type of the binding when the `let` gives one,
`let k: Flow = { ... }`, and otherwise the one declared struct type
with exactly those field names in that order; a literal that matches
no declared type, or several, is a type error naming the annotation
form. Every field is given, every field is a scalar, and each
initializer is checked against the field's predicate as a store is
(section 17). It appears only as the initializer of `let`; being a
place, it is never a value, and its use is to build the key of a hash
lookup or the value of an `insert` from parts.

### 8.3 Fallible expressions

The following are fallible and may appear only in the positions section
10.2 allows:

| expression | result | failure kind |
|---|---|---|
| `e as {v: T \| P}` | `{v: T \| P}` | `bound` |
| `pkt.view<T>(off)`, and `r.view<T>(off)` for any region `r` of dynamic extent an extension defines | `view T` | `short_packet` |
| `pkt[off]` | `u8` | `short_packet`, sugar for a one-byte view read |
| `m[k]` for a hash map, `k` a place of type `K` | `ref V` | `missing` |
| `f(args)` for `f` returning `T?` | `T` | `missing` |
| `p.f` where `f` has a `where` clause | `{v: T \| P}` | `invariant` |
| `m.insert(k, v)`, `m.delete(k)` | none | `helper` |
| `pkt.adjust_head(d)`, `pkt.adjust_tail(d)` | none | `helper` |
| `redirect(ifindex)` | verdict | `helper` |
| `rb.reserve<T>()` | `own T`, a resource | `helper` |
| `sk_lookup_tcp(tuple)`, `sk_lookup_udp(tuple)` | `own Sock`, a resource | `missing` |

The coercion `e as {v: T | P}` is the one way to establish a fact at
runtime: after `let x = e as {v: T | P}?`, `x` has the refined type and
`P[v := x]` is a fact. `check P` is sugar for it (section 10.4), and
the marked load of a `where` field is the same coercion with the
predicate taken from the declaration. There is no `assume`.

### 8.4 Constant expressions

Literals, constants, configuration constants, `T.size`, `hton` of a
constant, and arithmetic over these, evaluated at compile time in the
type of the context; a configuration constant evaluates to its value
for the build (section 15). Loop bounds, array sizes, and map capacities are
constant expressions. A map capacity, an array length, and a `repeat`
count have no type of their own: there, a constant expression of any
unsigned integer type is accepted and evaluated in that type.

### 8.5 Other builtins

`pkt.len : u64`; `ktime() : u64` with effect `call`; `csum_add`,
`csum_fold` pure; `copy(dst, src)` for `dst: ref T` and `src` a `ref T`
or `view T`, with the write effect of `dst`; `fill(dst, byte)`;
`printk(fmt, args...)` with effect `call`, at most three arguments;
`hton`, `ntoh`; `T.size`. Atomic updates on a scalar place `p` of a
32- or 64-bit integer type in a map value or on the stack, since the
instruction set has no narrower atomic operation: `atomic_add(p, v)`,
`atomic_and(p, v)`, `atomic_or(p, v)`, `atomic_xor(p, v)`,
`atomic_xchg(p, v)`, and `atomic_cmpxchg(p, old, new)`, which yield the
previous value; they are single instructions with no `call` effect and
carry the write effect of `p`. `ctx` fields per program kind are listed
in section 13.

## 9. Statements

```
Block     ::= '{' Stmt* Expr? '}'
Stmt      ::= 'let' Ident (':' Type ('where' Pred)?)? '=' Expr Tail?
            | 'var' Ident (':' Type ('where' Pred)?)? '=' Expr Tail?
            | Place AssignOp Expr
            | 'if' Expr Block ('else' (Block | IfStmt))?
            | 'if' 'let' Ident '=' Expr Block ('else' Block)?
            | 'repeat' Expr Block
            | 'for' Ident 'in' Expr '..' Expr Block
            | 'for' Pattern 'in' Expr 'bounded' Expr '?'? Block
            | 'hold' (Ident '=')? Expr Tail? Block
            | 'check' Expr Tail?
            | Expr Tail
            | 'break' | 'continue'
            | 'return' Expr? | 'pass' | 'drop' | 'tx' | 'abort'
            | 'fail' Expr?
Tail      ::= '?' | 'else' (Block | Exit)
Exit      ::= 'fail' Expr? | 'pass' | 'drop' | 'tx' | 'abort'
            | 'return' Expr? | 'break' | 'continue'
AssignOp  ::= '=' | '+=' | '-=' | '*=' | '&=' | '|=' | '^=' | '<<=' | '>>='
Pattern   ::= Ident | '(' Ident ',' Ident ')'
```

`let` binds an immutable name, `var` a mutable one, both block scoped.
`repeat n` runs its body at most `n` times for a constant `n`. `for i in
a..b` binds `i` with the fact `a <= i < b`; its cap is the type of `b`,
which must have a finite upper bound `n`, because `b` is a constant, a
configuration constant, or a refined value `{v | v <= n}`. That one
declaration is the termination measure, the index's refinement, and
the constant the verifier needs. `for x in it bounded N` iterates a
kernel iterator or a map, binding each element (a key and value pair
for a map), and ends when the iterator drains or after `N` elements,
whichever is first, as `bpf_loop` does for its count; with `bounded
N?` reaching the cap before the iterator drains is a `bound` failure.
The iterators it ranges over are rows of the resource table (section
11.2), which this draft leaves to the extensions: the form parses and
desugars, and the checker rejects it until a row exists.
Which bytecode form a loop becomes, an unrolled or counted loop, an
open-coded iterator, `bpf_loop`, or `may_goto`, is the compiler's
choice from the cap, the body, and the held set, and is not part of
the language; a form that could end the loop before its cap, such as
the kernel's timed `may_goto`, is never chosen for a loop whose cap
is exact. A bare expression statement must be a
call, except that a function body may end in an expression, which is
its result (section 16). A conditional whose condition is a constant
expression is folded by the compiler; both branches are type-checked
(section 15).

## 10. Failure

### 10.1 Kinds

| kind | raised by | blames |
|---|---|---|
| `short_packet` | a view or byte read outside the packet | the input |
| `missing` | a hash lookup, socket lookup, or `T?` function with no value | the environment |
| `invariant` | a marked load of a `where` field whose predicate is false | whoever wrote the map |
| `bound` | a coercion `e as T?`, or its sugar `check`, whose predicate is false; an iterator loop marked `bounded N?` reaching its cap | the program's assumptions |
| `helper` | a kernel call that reported failure; the reason defaults to the call's negative return | the kernel or resources |
| `program` | a `fail` statement outside an `else` block | the program's own logic |

The kind of a fallible operation is fixed by the operation (section
8.3). A failure carries a reason, an unsigned 32-bit value chosen by the
site, 0 when none is given.

### 10.2 Where fallible operations may appear

```
let x = e?                     // bind, or fail with this operation's kind
let x = e else { block }       // bind, or run the block, which must exit
var x = e else fail R          // same, with a reason
if let x = e { s1 } else { s2 }   // handle absence in code; nothing raised
let x = e as T?                // coerce to a refinement type, else bound
hold x = e? { body }           // acquire a resource (section 11)
e?                             // a fallible call used for its effect
check P                        // sugar for the coercion (section 10.4)
```

A fallible expression anywhere else is a type error. There is one
fallible operation per statement; a nested form such as
`backends[0][policy[0].cur]` is written as two bindings.

A marked load of a predicated field, `let cur = policy[0].cur?`, gives
`cur` the refined type. It loads once into a temporary, tests the
temporary, and every later use of `cur` is the temporary. The unmarked
read is allowed and yields the base type with no fact.

### 10.3 Else blocks and exits

The block after `else` runs when the operation fails. It may read
locals, count, or log, and it must end in an exit: a verdict statement,
`fail`, `return`, `break`, or `continue`. A block that can fall through
is a type error. `else <Exit>` abbreviates the one-statement block.

### 10.4 `check`, sugar for the coercion

`check P` abbreviates `let _ = P as {b: bool | b}?` and records `P` as a
fact for the rest of the enclosing block, raising `bound` when it is
false; `check P else { block }` runs the block instead. `P` is a
predicate over variables in scope. The general form `let x = e as
{v: T | P}?` gives `e` the refined type under the name `x`. Either form
is the way to satisfy a demand the facts do not entail: an index
computed by arithmetic the fragment does not track, a precondition on
a value read from the environment, a length that is the difference of
two positions, or a divisor the programmer wants nonzero. There is no
way to add a fact without a test; the language has no `assume`.

### 10.5 `fail` and reasons

`fail` inside an `else` block raises the kind of the operation that
failed. `fail` anywhere else raises the kind `program`. `fail R`
attaches the reason `R`, an expression of type `u32`. The marker `?` is
`else fail` with reason 0, except for the `helper` kind, where the
reason defaults to the helper's negative return value, so a handler
can log the errno without the site naming it.

### 10.6 Handlers

```
program p : xdp fail drop
  on short_packet { stats[0].short += 1; pass }
  on invariant, bound { stats[0].corrupt += 1; abort }
{ ... }
```

`on k1, k2 { block }` handles the listed kinds; `on _ { block }` handles
every kind not listed elsewhere; `fail v` in the header abbreviates
`on _ { v }`. At most one handler per kind. In a handler block the
variable `reason: u32` holds the reason the site gave. The block must
exit, and it is a non-failing context: no marker and no `fail` may
appear in it. No resource is held and no view is live when a handler
runs.

### 10.7 Defaults

A kind with no handler and no `fail v` uses the default of the program
kind (section 13): abort for XDP, drop for TC, minus one for syscall
programs. XDP's default is abort because the kernel fires the
`xdp_exception` tracepoint on it, so failures stay observable.

### 10.8 Functions

A function marked `fails` may contain markers, `check`, and `fail`, and
may call other `fails` functions; a failure inside it goes to the
handler of the program that called it, with the same kind and reason. A
function not marked `fails` may not. Programs are always failing
contexts. A function returning `T?` is a fallible operation of kind
`missing` at its call sites.

### 10.9 What is not a failure

Absence handled with `if let` raises nothing. Ordinary conditions such
as "not our traffic" are branches that end in a verdict; they are not
failures. A failure is an anomaly the program cannot proceed from at
that site.

## 11. Scoped resources and ownership

### 11.1 The `hold` statement

```
hold lock(e.lk) { ... }
hold rcu { ... }
hold ev = events.reserve<Event>() else drop { ... }
hold sk = sk_lookup_tcp(tuple)? { ... }
```

`hold x = acq Tail? { body }` acquires the resource `acq` denotes, binds
`x` to it for the body when the resource carries a value, and releases
it on every exit of the body unless the body has moved it (section
11.5). Scope-only resources bind nothing: `hold rcu { }`, `hold
lock(p) { }`. Acquisitions that can fail take a `Tail`; the `Tail`
covers acquisition only, and a refused acquisition, such as a resilient
lock that would deadlock, goes to the handler of its kind. The bound
name cannot escape the block. `hold` is the kernel's own word: the
verifier speaks of the held set and of what is forbidden while held.
What an acquisition takes is a column of its row, one of three shapes:
a place of a slot type (`lock(p)`), nothing (`rcu`), or the parameters
of the acquiring kernel function (`sk_lookup_tcp(t)`).

### 11.2 The resource table

Everything after `hold` is a row of this table, supplied by the
prelude for the kernel version the unit targets; the core knows only
the columns. Rows in this draft:

| resource | acquisition | argument | can fail | normal exit | abnormal exit | forbidden while held | nesting | class | guards |
|---|---|---|---|---|---|---|---|---|---|
| spin lock | `lock(p)` | a place of the slot type `spinlock`, in a map value | no | unlock | unlock | `call`, `resize`, `sleep`, another spin lock, calls to separately verified functions | no | | the allocation `p` lies in, for graph nodes moved into it |
| RCU section | `rcu` | none | no | unlock | unlock | `sleep` | yes, counted | | RCU-protected pointers, in the kernel-memory extension |
| preempt-off | `preempt_off` | none | no | enable | enable | `sleep` | yes, counted | | |
| IRQ-off | `irq_off` | none | no | restore | restore | `sleep` | yes, LIFO | native or lock; a flag saved by one class cannot be restored by the other | |
| ring-buffer record | `rb.reserve<T>()`, yields `own T` | the ring buffer and the record type | yes, `helper` | submit | discard | none | yes | | |
| socket reference | `sk_lookup_tcp(t)`, `sk_lookup_udp(t)`, yields `own Sock` | the call's parameters: `t` a place of the prelude type `SockTuple` (`saddr`, `daddr`, `sport`, `dport`) | yes, `missing` | release | release | none | yes | | |

Rows the extensions add with no change to the core: resilient locks,
whose acquisition can fail; kernel iterators, generic over the iterated
type, with states active and drained; dynptrs, whose slices are views
guarded by the dynptr's layout token; references to tasks, cgroups,
and other kernel objects. Release order is last-acquired-first because
blocks nest, which is the order the kernel enforces for resilient
locks and IRQ flags.

### 11.3 Release on every exit

A normal exit is falling off the end of the body. Every other way out is
abnormal: `break`, `continue`, `return`, a verdict statement, `fail`, and
a marker that fails. On an abnormal exit the abnormal release runs for
every resource held, innermost first, before control continues. A
failure reaches its handler with nothing held.

Resources are lexically scoped, and two shapes the kernel accepts
cannot be written: a resource taken on one branch and released after
the join, and a resource held across a loop back-edge. The surveyed
datapaths do neither, and the trade buys release on every exit and
last-acquired-first order by construction.

### 11.4 Restrictions while held

Statements with an effect the table forbids are type errors in the
body, reported with the resource named. Functions called in the body
must have effect sets the table allows. Nesting a resource whose row
says no inside another instance of itself is a type error. `sleep` is
forbidden under every row, which is the kernel's rule that nothing
sleeps while anything is held.

### 11.5 Ownership and `move`

A name bound by a value-yielding `hold` has type `own T`. The scope
releases it on every exit, unless the body hands it away with the
expression `move x`, which has type `own T`, consumes the name, and
cancels the scope's release on that path. Its sinks are the kernel's
own operations, and only they: a kernel function whose parameter is
`own T`, a consuming call; an exchange into a map field of kernel
pointer type, never a plain store, because exchange is the kernel's
only operation there and the old value comes back owned and nullable;
insertion into a kernel list or tree, after which the returned place is
guarded by that structure's lock; and, in the struct_ops extension, a
return.

```
hold sk = sk_lookup_tcp(tuple)? {
  // a consuming call; the scope no longer releases sk
  sk_release(move sk)
}

hold sk = sk_lookup_tcp(tuple)? {
  if keep { sk_release(move sk) }
  // error: sk moved on one branch and held on the other at this join
  count = count + 1
}
```

Three rules make it one pass. After `move x` the name is dead, and a
later use is a type error. At every join the moved-or-not state of
each owned name must agree, or the program is rejected; there are no
runtime flags, so the verifier sees a release or a transfer on every
path and never a conditional release. Only names bound by a
value-yielding `hold` can be moved; locks, RCU, preemption, and IRQ
state are not values. `move` emits no code; the sink emits the
transfer and the scope omits the release.

## 12. Effects, regions, and guards

Every builtin and function has an effect set drawn from
`{call, resize, sleep, fail}` together with write effects `write(r)` on
regions:

```
Region r ::= pkt[a..b) | m | ctx.f
```

- `call`: invokes a kernel helper or kfunc.
- `resize`: may move or resize the packet; implies `call`. It drops the
  packet's layout token, the guard of every view (below).
- `sleep`: may sleep; implies `call`. Permitted only in program kinds
  whose table says so (section 13) and forbidden while any resource is
  held.
- `fail`: may raise a failure. Requires `fails` on a function.
- `write(pkt[a..b))`: a store through a view `h` to a field at offset
  `k` of size `s` has `write(pkt[off(h) + k .. off(h) + k + s))`; a
  helper that writes the packet has the effect its signature declares.
- `write(m)`: a store through a reference into a map value of `m`, an
  `insert` or `delete` on `m`, an atomic update on `m`.
- `write(ctx.f)`: a store to a context field.

Function effects are the union over the body, with write ranges over
the function's parameters and constants. Resources are not effects of
functions, because a resource cannot be held across a function
boundary; they are context flags used by section 11.4.

**Guards.** A place may carry a guard: a resource in the held set, or a
stability token. Reading or writing through the place demands that
its guard be held. An operation that drops the guard kills every place
it guards, and a later use is a type error at the use, naming the
statement that dropped it. The guard column of the region and resource
tables supplies the rows; this draft has one, and the extensions add
the other two with no new rule:

| place | guard | dropped by |
|---|---|---|
| a packet view | the packet's layout token | any statement with the `resize` effect |
| an RCU-protected pointer, kernel-memory extension | the RCU section | the outermost `hold rcu` exit |
| a graph node after `move` into a list or tree, kernel-memory extension | the lock of that allocation | that lock's `hold` exit |

The first row is what draft 2 called view invalidation. The kernel
implements the three as separate rules: packet-pointer clearing on
packet-changing helpers, demotion of RCU pointers to untrusted at
unlock, and the requirement that a graph node be accessed under the
lock of its allocation.

**The region table.** A region is a row the prelude supplies; the core
knows only the columns:

| column | meaning |
|---|---|
| obtained | statically, or through a view |
| readable, writable | whether places in it may be loaded and stored; the packet's writability is per program kind (section 13) |
| initialized | whether a place is defined before its first read: locals at declaration, map values zero-filled, context and packet by the kernel |
| nullable at entry | whether a place may be absent until coerced (kernel-memory extension) |
| trusted | whether the kernel vouches for the pointer (kernel-memory extension) |
| guard | the token or resource a place carries |
| max offset | for a region of dynamic extent, the largest offset a view may lie under, since the verifier bounds a pointer's variable offset before it sees the test; the packet's is the kernel's maximum packet offset, 65535 |

Stage-1 rows: the stack, static, read-write, initialized, no guard; map
values, static, read-write, zero-filled, no guard; the context, static,
writable per field from the kind table, no guard; the packet, by view,
readable, writable in the kinds whose row says `rw`, guarded by its
layout token, max offset 65535. A store through a view in a kind whose
packet is read-only is a type error at the store.

## 13. Programs, contexts, verdicts

`program name : kind [implements C] clause* [fail exit] handler* { body }`.
The body sees `pkt` in packet kinds and `ctx` in all kinds. `ctx` field
tables are generated from the kernel's context-access rules.

| kind | `pkt` | `ctx` fields in this draft | verdicts | sugar | default failure | `sleep` |
|---|---|---|---|---|---|---|
| `xdp` | `rw` | `ingress_ifindex: u32`, `rx_queue_index: u32` | `ABORTED DROP PASS TX REDIRECT` | `abort drop pass tx` | `abort` | no |
| `tc` | `rw` | `mark: u32` writable, `priority: u32`, `ifindex: u32` | `OK SHOT UNSPEC PIPE REDIRECT` | `pass` = OK, `drop` = SHOT | `drop` | no |
| `syscall` | none | opaque | `i32` | none | `-1` | yes |

A kind's row is one of six tables the prelude carries for a kernel:
kinds, context fields per kind, calls with their signatures and effects
and availability per kind, resources, regions, and slots. The `pkt`
column says whether the packet exists and whether views into it may be
written (`rw`, `ro`, none). The verdict range is the one the kernel
enforces at every exit. A call, kind, or slot the target kernel lacks is
a type error naming the kernel. A kind the kernel offers in a sleepable
variant selected by section name, `fentry` and `fentry.s`, `lsm` and
`lsm.s`, is two rows differing in the `sleep` column and the section,
not one kind with an attribute. An asynchronous callback, a timer or
workqueue body, is a kind in this sense, with its own context, verdict
range, and an empty held set; the extensions define those rows.

Verdict statements and `return` end the program, releasing held
resources on the way. A `syscall` body may also fall off its end,
which returns 0; the body of a packet kind must end in an exit, as a
handler must. The verdict type of a kind is `u32` restricted to
the kind's named constants, so a verdict can be computed and compared
like an integer; `return e` demands that `e` lie in the kind's set,
further restricted by the program's verdict set if it has one (section
14).

## 14. Contracts

A contract states what a program does at its boundary: which verdicts it
may return, which regions it leaves untouched. It is the program's type
signature, and the same object is what a party relying on the program
would state without reading it.

### 14.1 Clauses

**Verdict set.** `verdict in { PASS, DROP }` refines the program's
return type to `{v : Verdict | v in S}`. Every exit is a demand: a
verdict statement is a constant and checks syntactically; `return e`
demands `e in S` from the facts; a verdict loaded from a map gets its
fact from the marked load. Every handler's exit and the default failure
verdict are exits, so both are checked against `S` in the header: a
contract cannot be satisfied by failing. A `redirect` call yields
`{v | v == REDIRECT}`, so a contract without REDIRECT rejects the call.

**Preserved region.** `preserve R` for a region `R` is the demand that
no statement in the program, including the functions it calls, carries
a write effect intersecting `R`. For `pkt[a..b)` the demand is
disjointness of every packet write range from `[a, b)`, decided by
entailment over the ranges of section 12. `preserve pkt` abbreviates the
whole packet; a program that preserves any packet range may not have the
`resize` effect, since a resize moves every byte. `preserve m` is the
absence of `write(m)`; `preserve maps except m1, m2` preserves every
map but the named ones, and the `except` list extends to the end of
the clause, so a further region needs its own `preserve`. `preserve
ctx.f` is the absence of `write(ctx.f)`.

### 14.2 Inline and named

Inline clauses in a program header state the developer's own
properties. A named contract states properties supplied by someone else
and is a file the compiler is pointed at:

```
contract Monitor : xdp {
  verdict in { PASS }
  preserve pkt
  preserve maps except stats
}

program observe : xdp implements Monitor fail pass { ... }
```

A program may both implement a named contract and add inline clauses;
the demands are the union. New reserved words: `contract`,
`implements`, `verdict`, `preserve`, `except`.

### 14.3 Map value predicates as contracts

A `where` clause on a map value type (section 17) is the third clause
kind of the proposal's contracts and needs no new syntax. When the
kernel enforces a map's predicate on userspace writes, a marked load's
test can never fail; the language is unchanged, the marker stays, and
the compiler may omit the test, since a test that cannot fail is a
no-op. The `invariant` kind is then unreachable for that map.

### 14.4 Shipping

A contract compiles to a section of the object the kernel can read and
re-check at effect sites, which is the proposal's mechanism for
contracts on C programs. For a koit program the checker has already
established every clause, so the kernel's check is its independent
confirmation, as for safety.

## 15. Configuration

Production programs are built in variants: an address family enabled or
not, a feature compiled in or out, a table sized for a deployment. C
does this with the preprocessor. koit does it with configuration
constants:

```
config ENABLE_IPV6 : bool = false
config SLOTS : u32 = 65536
```

A `config` is a constant whose value is supplied at build time, with an
optional default. It is usable wherever a constant expression is: map
capacities, array sizes, loop bounds, conditions. A conditional whose
condition is a constant expression is folded by the compiler and the
dead branch is not emitted, which preserves meaning because the branch
could not run. Both branches are type-checked, so a program is checked
with the dead branch of every constant conditional included. Entailment
(section 18.5), by contrast, uses the value of each configuration
constant for the build being checked, the default where the build
supplies none: the checker runs per build, as the compiler does, and
the facts it uses are the ones the lowering folds to immediates. So
`cache[h % SLOTS]` is accepted for every build whose `SLOTS` is
nonzero and rejected, at that index, by a build that sets it to zero.
A configuration constant with neither a default nor a build value has
no value to check with, and the declaration is an error. This draft
does not allow declarations, maps or functions, to be conditional;
every item exists in every variant.

## 16. Functions

`fn f(x: T where P, ...) -> r: U where Q [fails] { ... }`.

- Parameters pass by value for scalars and by reference for `ref` and
  `view` types. A refinement on a parameter is a precondition, checked
  at each call site against the facts there. A refinement on the result
  is a postcondition, checked at each `return` and a fact at the call
  site.
- A function body may end in an expression, which is its result;
  `return e` is the same thing written as a statement. A function with
  a result type ends in `return` or in such an expression on every
  path; a body that can fall off its end is a type error.
- A function declared `-> T?`, with `T` a scalar, returns absence with
  a bare `return`, and a value with `return e`; at its call sites it is
  the fallible operation of kind `missing` that `?`, `else`, and
  `if let` consume. A bare `return` elsewhere is an early exit of a
  function with no result.
- `fails` is explicit: a function that may raise says so in its
  signature, and a call to it is allowed only in a failing context.
- The call graph must be acyclic. Whether a call is inlined or compiled
  to a subprogram is not part of the language.
- A function may be called inside a resource block only if its effect
  set is allowed there.
- In prelude signatures, a parameter of type `own T` is a `move` sink
  and a result of type `own T` must be bound by `hold` at the call
  site; a parameter written `const n: T` takes a constant expression
  (section 8.4) at every call, which is how the kernel's constant-size
  and `__k` arguments are stated. User functions take `ref` and `view`
  parameters and never `own` or `const`.
- Prelude parameters carry refinements like any parameter, and the
  kernel's argument constraints are stated as such: a length paired
  with a memory argument is `len: u32 where 0 < len && len <= size(buf)`
  (or `0 <= len` for the `_OR_ZERO` kinds), so a zero or negative
  length, or one exceeding the place, is a demand at the call. A
  parameter's region kind is part of its type, so passing packet
  memory to a helper that admits only stack or map memory is a type
  error.

## 17. Predicates

```
Pred ::= Expr
```
restricted to integer literals, constants, and configuration constants;
the refined name; sibling field names on a struct field; parameters on a
result; arithmetic, bitwise, and comparison operators; `&&`, `||`, `!`.
No calls, no map or packet access, no byte-order casts. Every predicate
is a quantifier-free bit-vector formula, so a runtime test compiles to a
few instructions and a proof needs nothing beyond bit-vector reasoning.

A field predicate is an invariant of every value stored by this unit. A
store `p.f = e` demands `P[f := e]` with sibling fields read from `p`; a
struct literal passed to `insert` demands every field's predicate. A load
relies on the predicate only through a marked load (section 10.2), since
other writers exist (P8). Array maps are zero-filled at creation, so a
predicate on an array map's value must hold of the all-zero value; the
declaration is rejected otherwise.

## 18. Static semantics

### 18.1 Core syntax

Core is the target of desugaring and the one language the typing
rules are stated on. Every demand the source marked is an explicit
`raise`, every optional is consumed by an explicit branch, every
governed load goes through a temporary, and every handler table is
total. Three surface forms stay in Core because handling them needs
types: functions, with their signatures, since section 16 checks each
once against its signature; constant conditionals, since section 15
checks both branches; and `for i in a..b`, whose cap is the type of
the bound under the facts. Inlining and folding are Core-to-Core
passes after checking.

```
kinds        k ::= short_packet | missing | invariant | bound | helper | program
resources    R ::= a row of the resource table
                   (stage 1: spinlock rcu preempt irq ringbuf sockref)
guards       g ::= layout(pkt) | R
regions      r ::= pkt[a..b) | m | ctx.f
types        T ::= int(s,w) | be(w) | bool | S | T[n]
                 | ref T | view T | own T | slot(row)
                 | {v: T | P} | T?
expressions  e ::= c | x | e op e | e cmp e | !e | e && e | e || e
                 | e as T | hton e | ntoh e | rd p | size T | move x
                 | call f(a...) | errno | invalid
arguments    a ::= e | p | m
places       p ::= x | p.f | p[e] | m[e] | deref x
initializers i ::= e | p | { f: e, ... }
fallible     F ::= view(e, T) | lookup(m, p) | loadw(p.f) | call h(a...)
                 | acquire R (a...) | callopt f(a...) | coerce(e, P)
statements   s ::= skip | s ; s | let x [: T] = i | var x [: T] = i
                 | p := e
                 | if e then s else s | loop n s | break | continue
                 | for x in e..e s
                 | return e | raise k e
                 | try x = F then s else s          [else exits]
                 | hold R x = F then s else s
                 | hold R x = acquire R (a...) s
                 | [x =] atomic op p e...
programs     P ::= program(S, W, H, s)
                 S the verdict set, W the preserved regions,
                 H : k -> handler block, total
```

Fine print of the grammar, each point a decision of the
implementation (`ISSUES.md`, entry 11):

- A binding keeps the declared type of its source, `let x : T = i`,
  since `var n: u64 where n <= MAX_KEY = 0` supplies a type and a fact
  that the initializer cannot.
- The right side of a binding is an expression, a place, or a struct
  literal. Whether a place is read into the name (a scalar) or named by
  it (an aggregate) depends on its type, so the desugaring keeps the
  place and the typing rule decides; this is the same criterion that
  keeps `call` in Core.
- An argument of a call is a value, a place, or, for `insert`,
  `delete`, and `reserve`, the map; whether a place argument is read
  or passed by reference depends on the parameter.
- `try` records whether its `else` came from a tail, which must exit,
  or from `if let`, which need not; both elaborate to the same form.
- A call used for its effect is `let _ = call f(a...)`: `_` binds
  nothing and may take only a call's result, which is the surface rule
  that a bare expression statement is a call.
- `errno` is the negative return of the helper whose `try` failed, the
  default reason of the `helper` kind; it is defined only in the `else`
  of such a `try`.
- `size T` is typed as a literal, representable in the type of the
  context; `pkt.len` is a prelude call; `-e` is `0 - e`, the kernel's
  negation under total arithmetic.
- A surface form outside its positions (a fallible operation in a
  value position, a struct literal elsewhere than a `let` initializer,
  a field of a non-place, a verdict statement of another kind)
  desugars to `invalid`, a node carrying the diagnostic, which has no
  typing rule. Desugaring is therefore total, as T3 states.
- The atomic updates take an optional binder for the previous value
  they yield.


### 18.2 Environments

- `G` maps variables to types, structs to declarations, maps to kinds,
  configuration constants to values.
- `F` is the set of facts on the current path; refinements of variables
  in `G` and offsets `off(h)` of views are in `F`.
- `K` records: the program kind and verdict type refined by `S`; whether
  the context may fail; whether inside a loop; the held set `H` of
  resources and tokens, with, for each owned name, whether it has been
  moved on this path; the kind of the enclosing `else` block, if any.
  Draft 2's live views `V` are the places whose guard `layout(pkt)` is
  in `H`.
- `E` is the effect set accumulated for the statement or function under
  check.

### 18.3 Expression and place typing

Bidirectional: `G;F |- e => T` synthesizes, `G;F |- e <= T` checks. A
premise of the form `F |= P` is a demand: `F` must entail `P` (section
18.5) or the rule does not apply and the program is ill-typed.

```
(Var)
    x : T in G
    ---------------
    G;F |- x => T

(Lit)
    c representable in int(s,w)
    ---------------------------
    G;F |- c <= int(s,w)

(LitDef)
    no expected type
    ------------------------
    G;F |- c => int(u,64)

(Arith)   op in {+ - * / % & | ^ << >>}
    G;F |- e1 <= int(s,w)
    G;F |- e2 <= int(s,w)
    ----------------------------
    G;F |- e1 op e2 => int(s,w)

(Cmp)
    G;F |- e1 => int(s,w)
    G;F |- e2 <= int(s,w)
    -------------------------
    G;F |- e1 cmp e2 => bool

(CmpBe)   cmp in {== !=}
    G;F |- e1 => be(w)
    G;F |- e2 <= be(w)
    -------------------------
    G;F |- e1 cmp e2 => bool

(Cast)
    G;F |- e => int(s,w)
    --------------------------------------
    G;F |- e as int(s',w') => int(s',w')

(Hton)
    G;F |- e <= int(u,w)
    -----------------------
    G;F |- hton e => be(w)

(Ntoh)
    G;F |- e => be(w)
    ---------------------------
    G;F |- ntoh e => int(u,w)

(Sub)
    G;F |- e => T'
    T' <: T under F
    ----------------
    G;F |- e <= T

(Read)
    G;F |- p : T place
    T scalar
    ------------------------
    G;F |- rd p => base(T)

(PVar)
    x : T in G    T not ref or view
    ------------------------------------
    G;F |- x : T place    [mut if var]

(PDeref)
    x : ref T in G,  or  x : view T in G and guard(x) in K.H
    ---------------------------------------------------------
    G;F |- deref x : T place    [mut]

(PGuard)
    G;F |- p : T place    guard(p) = g
    g in K.H
    ----------------------------------
    p may be read or written
    (otherwise: error at the use, naming the statement that dropped g)

(Move)
    x : own T in G    x not moved in K.H
    ------------------------------------
    G;F |- move x => own T
    and K.H marks x moved; a later use of x is an error

(PField)
    G;F |- p : S place
    f : T in S
    ----------------------
    G;F |- p.f : T place

(PIndex)
    G;F |- p : T[n] place
    G;F |- e <= int(u,w)
    F |= e < n
    -----------------------
    G;F |- p[e] : T place

(PArr)
    map m : array(n) V  or  percpu(n) V
    G;F |- e <= int(u,w)
    F |= e < n
    -----------------------
    G;F |- m[e] : V place
```

Subtyping is refinement weakening: `{v:T | P} <: T`, and `{v:T | P} <:
{v:T | Q}` when `F, P |= Q`. (Arith) has no demand: every operation is
total (section 8.1). (Cmp) applies to integers only: two places are
never compared, so a `==` between references or views is ill-typed.

### 18.4 Statement typing and elaboration

The judgment is `G;F;K |- s' -| F' ; E`: Core `s'` is well-typed with
facts `F'` afterwards and effect set `E`. Each rule below is written
with a surface form on the left of `~>` and its Core form on the
right, so that it reads as two things at once: the `~>` part is the
desugaring, a syntactic rewrite performed with no premises and using
only the unit's declarations, and the premises are the typing rule of
the Core form on the right. Sequencing, conditionals, and
loops are as expected, with `kill(F, p)` removing facts about `p` after
a store, `inv(F, s)` keeping facts about variables not assigned in `s`
at a loop head, and `meet` intersecting the facts of two branches.
Effects are unioned along the way.

The three operations, precisely. A fact is about the places it
mentions, with a reference bound by `let r = p` read as the place `p`
it names. `kill(F, p)` removes every fact mentioning a place that is
`p`, lies inside `p`, or contains `p`, two indexes being taken as
possibly equal unless both are literals that differ; and, since the
checker does not compute aliasing between them, a store through a
`ref` parameter removes every fact about every `ref` parameter of the
function, and a store through a view every fact about every view.
When a fact `kill` removes mentions another stack place, as `voff =
off` mentions `voff` when `off` is stored to, what was known of that
place, its bounds and known bits, is kept as facts of its own, since
the store did not change it; and a store `x = e` whose `e` reads `x`
itself, `x += c`, records the bounds the state had for `e` before the
store in place of the circular equation. Any
`call` removes every fact about a place off the stack: a map value,
the context, the packet, a `ref` parameter, a kernel object. `inv(F,
s)` removes the facts about what `s` may assign, including every place
passed to a call in `s`, and every fact about a place off the stack,
then restores the refinements of the locals in scope, which every
store re-establishes; and, when the loop's iteration count is known,
a constant for `repeat` and the cap for `for`, an unsigned stack
local that `s` changes only by `x += e`, each increment outside the
nested loops and each addend bounded above before the loop by values
`s` does not change, keeps the bound `x <= x_0 + count * sum of the
addends' bounds` and its lower bound when the total stays within its
type, since it cannot wrap; the verifier re-derives the same bound by
walking the loop to its count, so the fact is one it will see (P9).
`meet(F1, F2)` keeps the facts present in both
and, for each variable, the hull of what each side knew about it as
new facts, so that `x < 5` on one path and `x < 7` on the other leave
`x <= 6`; a path that has exited contributes nothing. Facts about a
block's locals end with the block.

A branch condition and a `check` establish facts about stack places
only: a conjunct that reads a place in a map, the context, the packet,
a `ref` parameter, or a kernel object yields nothing, since the place
may change between the test and the use and the fragment of section
17 excludes such reads from predicates. A value read from a shared
place is given a fact by reading it into a name and testing the name,
or by a marked load. The one fact source that mentions a shared place
is the view offset `off(h) = e`, which is about where the view is,
not what it holds.

```
(Mark)
    e fallible of kind k with result type T
    K may fail
    G,x:T; F + facts(e,x); K |- rest ~> rest' -| F1
    -------------------------------------------------------
    G;F;K |- let x = e? ; rest
        ~> try x = e then rest' else raise k 0      -| F1

(Else)
    e fallible of kind k with result type T
    G,x:T; F + facts(e,x); K |- rest ~> rest' -| F1
    G;F;K[else = k] |- b ~> b' -| _
    b ends in an exit
    -------------------------------------------------------
    G;F;K |- let x = e else b ; rest
        ~> try x = e then rest' else b'             -| F1

(IfLet)
    e fallible with result type T
    G,x:T; F + facts(e,x); K |- s1 ~> s1' -| F1
    G;F;K |- s2 ~> s2' -| F2
    -------------------------------------------------------
    G;F;K |- if let x = e s1 else s2
        ~> try x = e then s1' else s2'              -| F1 meet F2

(LoadW)
    p.f : T place    f : T where P
    -------------------------------------------
    facts(loadw(p.f), x) = {P[f := x]}
    and the elaboration reads p.f once into x

(View)
    G;F |- e <= int(u,w)
    F |= e + size(T) <= max offset of the region
    facts(view(e, T), h) = {off(h) = e}
    h joins K.V in the then-branch
    The demand is the verifier's: it bounds a packet pointer's
    variable offset before it reads the comparison that follows, so an
    offset the facts do not bound is a program that does not load. A
    constant offset is entailed trivially; a loop-carried one needs a
    `check` at the head of the body. The byte read `pkt[off]` demands
    the same with size 1.

(Lookup)
    facts(lookup(m, k), r) = {}

(Coerce)
    G;F |- e => T        T' = {v: T | P}
    K may fail
    G,x:T'; F + {P[v := x]}; K |- rest ~> rest' -| F1
    -------------------------------------------------------
    G;F;K |- let x = e as T'? ; rest
        ~> let x = e ; if P[v := x] then rest' else raise bound 0  -| F1

(CoerceE)
    as (Coerce), with the elaborated else block b' in place of
    raise bound 0, where b ends in an exit

(Check)   sugar
    check P ; rest      ==   let _ = P as {b: bool | b}? ; rest
    and the fact recorded is P itself

(Fail)
    K may fail
    G;F |- R <= int(u,32)
    k = K.else if set, else program
    -----------------------------------
    G;F;K |- fail R ~> raise k R -| F

(Hold)
    acq : resource R, yielding own T or nothing, fallible of kind k or not
    G,x:own T; F; K[H += R(x)] |- body ~> body' -| F1 ; E
    E disjoint from forbidden(R)
    R nests per the table
    moved(x) agrees on every path reaching the end of body
    -------------------------------------------------------
    G;F;K |- hold x = acq Tail body
        ~> hold R x = acq then body' else <tail'>   -| F1
    the release at exit is emitted on the paths where x is not moved

(Meet)
    meet(F1, F2) is defined only when, for every owned x in scope,
    moved(x) is the same in both; otherwise the join is a type error
    naming x and the two branches

(ForIter)
    it : iterator resource I over T;  N a constant expression
    G,x:T; inv(F, s); K[loop, H += I] |- s ~> s' -| _
    -------------------------------------------------------
    G;F;K |- for x in it bounded N s
        ~> hold I h = new(it)
             (var i = 0 ;
              loop N (try x = next(h) then (s' ; i := i + 1) else break))
        -| inv(F, s)
    with `bounded N?`: after the loop, if i = N then one more next(h);
    a value there is raise bound 0

(Handler)
    G, reason:int(u,32); F0; K[may fail = false, held = [], V = {}]
        |- b ~> b'
    b ends in an exit v    F0 |= v in S
    -------------------------------
    H(k) = b'    for each k listed

(Program)
    every kind has a handler after defaults are filled in
    the default verdict d satisfies d in S
    G; F0; K[may fail = true] |- body ~> body' -| _ ; E
    every write(r) in E is disjoint from every region in W
    resize not in E when W mentions pkt
    ----------------------------------------------------
    |- program(S, W, H, body')

(Return)
    G;F |- e <= K.ret            (K.ret refined by S)
    ------------------------------------
    G;F;K |- return e ~> return e -| F

(StoreView)
    h : view T'    G;F |- h.f : T place [mut]    G;F |- e <= T
    guard(h) in K.H
    f at offset k of size s in T'
    ------------------------------------------------------------
    G;F;K |- h.f = e ~> h.f := e
        -| kill(F, h.f) ; {write(pkt[off(h)+k .. off(h)+k+s))}

(For)
    the type of b has upper bound n, or a and b are constants:
    the cap is n
    G,i:int(u,64); inv(F, s) + {a <= i, i < b}; K[loop] |- s ~> s' -| _
    -------------------------------------------------------
    G;F;K |- for i in a..b s
        ~> var i = a ;
           loop n (if i < b then (s' ; i := i + 1) else break)
        -| inv(F, s) + {i = b} on the fall-through path (see note)

(Repeat)
    n constant
    G; inv(F, s); K[loop] |- s ~> s'
    ----------------------------------------------
    G;F;K |- repeat n s ~> loop n s' -| inv(F, s)

(Assign)
    G;F |- p : T place [mut]
    G;F |- e <= T
    ---------------------------------------------------
    G;F;K |- p = e ~> p := e -| kill(F, p) + {p = e} ; writes(p)

(AssignW)
    p.f : T place [mut]    f : T where P
    G;F |- e <= T
    F |= P[f := e, g := rd p.g for each sibling g]
    ---------------------------------------------------------
    G;F;K |- p.f = e ~> p.f := e -| kill(F, p.f) + {p.f = e} ; writes(p.f)

(IfConst)
    c a constant expression evaluating to true
    G;F;K |- s1 ~> s1' -| F1     G;F;K |- s2 ~> _ -| _
    ----------------------------------------------------
    G;F;K |- if c s1 else s2 ~> s1' -| F1
```

Note on (For): the exit fact `i = b` holds only on the fall-through
path; the two paths are met. `writes(p)` is `write(m)` when `p` lies in
a map value of `m`, `write(ctx.f)` for a context field, and nothing for
the stack. The fact `p = e` after a store is recorded when `p` lies on
the stack, and is killed by a store through an alias and at loop
heads. A store to a shared place leaves no fact: the place may be
written by another party before it is read again (P8), and the
lowering reloads it, so a fact about it would discharge a test the
verifier cannot re-derive. A value stored to shared memory that is
needed again is held in a name.

### 18.5 Entailment

`F |= P` is decided by a procedure that is sound and restricted to:
syntactic membership and constant comparison against a fact about the
same variables, with equal names substituted for each other; and
abstract interpretation of `P` over a state computed forward from `F`
in the reduced product of intervals and known bits, with exact
treatment of `%` and `/` by constants and `&` with a constant mask. No
solver. The state gives each variable one interval, read in the
signedness of its type, and its known bits, kept consistent with each
other; a cast between widths is exact, as the verifier tracks it. It
is computed from the facts in the order they entered, each narrowing
with what was known when it arrived and no iteration to a fixpoint,
which is what a verifier re-derives at the branches in that order;
the join of two paths is the hull, written back as facts by `meet`.
`F` itself is the list of facts, not the state: the state is built
when a demand is checked and discarded after, so that membership,
`kill`, `meet`, and the soundness statement all speak of predicates. The restriction is not provisional: it is principle P9. The
procedure decides exactly the facts the verifier's own domain
re-derives from the branches the lowering emits, so a fact it proves
can be elided without loss of acceptance, and a fact it cannot prove
is discharged by the coercion of section 10.4, which the verifier then
reads as a branch. A stronger procedure would elide tests the verifier
cannot see. The solver appears in two places only, neither of them the
type system: the testing cross-check below, and the compiler's
elimination of redundant coercions when it targets a kernel with a
proof checker, where the kernel re-checks each elision from the path
condition.

The procedure is the one component of the checker whose soundness
decides whether an elided test was safe to elide, and it works in the
same family of domains in which the kernel verifier has had soundness
bugs. Two safeguards are part of the design: a cross-check mode in
which every entailment the procedure accepts is confirmed by a solver,
used in testing; and the mechanization of the procedure's soundness
(T2) alongside the core's.

### 18.6 Type inference

Inferred: types of `let` and `var` from initializers; literal and
untyped-constant types from context; effect sets of functions; the
facts `F`, by forward abstract interpretation with path facts from
branches, marked loads, and checks, with loops handled at the head by
`inv`, which drops what the body may change and so stabilizes in one
step. Never inferred: map types,
field types, signatures, contracts, loop bounds, program kinds, failure
policy, `fails`. Refinements are checked, not searched for.

## 19. Dynamic semantics of Core

### 19.1 The machine and the kernel

A run acts on a state `st` with the frame `sigma`, the names in scope
bound to a value, to a place, or marked moved; the map store `mu`;
the packet `B` with its layout token; the held set, innermost first,
each entry with the name it binds and the object it releases; the
negative return of the last helper that failed, which `errno` reads;
and the trace, the kernel calls made so far in order, each with its
row, its arguments, and its answer, and each `printk` with its format
and arguments, an untyped argument settled to `u64`; a held spin lock
carries the lock's map slot and offset as its object, as a record or
a socket carries its kernel object, and a memory argument is traced
as the bytes the kernel received. The map store, the packet and its
token, the kernel objects, the held set read as rows and objects,
and the trace are the part of the state every level of the lowering
shares as one definition; the frame, the named context, and `errno`
are Core's own (decision 54). A row with no effects that reads the context, such as
`pkt.len`, goes through the kernel like any other, so that the trace
lists every row called. Values are scalars: a fixed-width integer reduced to
its type's range, a byte-order value, a boolean, or the location of a
place. A byte-order value is the bit pattern as stored, so `hton` and
`ntoh` are byte swaps and equality compares patterns. A location
carries its region, its offset, and the layout token it was made
under; a location into the packet is usable only while its token is
the current one. A literal or an untyped constant carries no width
until it meets an operand or a place, as it takes its type from the
context in section 18. Places are bytes in a region: a map slot, the
packet, a struct literal's frame, or an object the kernel handed out.
Memory is little-endian, as on the architectures the lowering
targets. Arithmetic is the total function of section 8.1. The frame a
field predicate is evaluated in, at a marked load, is built from the
fields of the place: the loaded field bound to its value and every
scalar sibling to the value at the place.

Helpers are nondeterministic relations constrained by their
contracts. The semantics takes them as a parameter: a kernel `K` says,
for each row of the call table and its evaluated arguments, what the
call does, a result and a new state, or a failure with the negative
return the `helper` reason defaults to. How the failure reaches the
program is a rule of the lowering read off the row's result type: a
negative return for a scalar result, null for a location; a row that
needs an exception gets a column then. A kernel is within its
contracts when it never errs, yields a value exactly when the row's
signature has a result, changes the packet or its token only when the
row has the `resize` effect, and fails only when the row is fallible.
Every statement about runs holds for every such kernel; the evaluator
of `koitc run` is one of them, with its choices recorded.

### 19.2 Judgments

The relation is big-step: a judgment relates a state and a phrase to
what the phrase produces and the state after it. Core's control is
structured and bounded, so every phrase of a well-typed program has a
derivation, and a run is one derivation. The continuation frames of a
small-step account are the enclosing rules here: `loop` consumes a
`break`, a call consumes a `return`, `hold` releases on its way out
of any other outcome, and the program consumes a failure by running
the handler of its kind.

```
K |- <e, st>  =>  v, st'   |  abort, st'      expressions
K |- <p, st>  =>  place                       places
K |- <F, st>  =>  binding, st' | failed, st'  fallible operations
K |- <s, st>  =>  o, st'                      statements
K |- <P, st>  =>  halt(v), st' | err          programs

o ::= normal | break | continue | return v | raise k r | err
```

An expression or a fallible operation aborts when a function it calls
raises a failure. A block drops the names it declared. Two further
judgments carry the loops: `loop` with the iterations left, and `for`
with the index's next value.

### 19.3 Selected rules

```
(Try-ok)
    K |- <F, st> => u, st1     K |- <then, st1[x := u]> => o, st2
    -----------------------------------------------------------
    K |- <try x = F then s1 else s2, st> => o, st2
(Try-fail)
    K |- <F, st> => failed, st1     K |- <s2, st1> => o, st2
    ------------------------------------------------------
    K |- <try x = F then s1 else s2, st> => o, st2

(Raise)
    <raise k e, st>  =>  raise k [[e]]st, st
    a `raise` is an outcome every enclosing rule passes upward, each
    `hold` releasing abnormally on the way; the program rule consumes it
(Program-handled)
    K |- <body, st> => raise k r, st1
    K |- <H(k), st1[reason := r, held := []]> => return v, st2
    -------------------------------------------------------
    K |- <program(S, W, H, body), st> => halt(v), st2
(Program-return)
    K |- <body, st> => return v, st1
    ------------------------------------------
    K |- <program(S, W, H, body), st> => halt(v), st1
    a `syscall` body that completes normally halts with 0

(Loop)
    K |- <s, st> => normal | continue, st1    K |- <loop (n-1) s, st1> => o, st2
    ---------------------------------------------------------------------------
    K |- <loop n s, st> => o, st2            (n > 0)
    <loop 0 s, st> => normal, st
(Break)
    K |- <s, st> => break, st1
    ----------------------------------
    K |- <loop n s, st> => normal, st1
    a `return` or a failure leaves the loop as the body's outcome

(Hold-in, Hold-out)
    K |- <acq, st> => u, st1      R(x) pushed on the held set of st1
    K |- <body, st1[x := u]> => o, st2
    ------------------------------------------------------------------
    K |- <hold R x = acq body, st> => o, release(st2, o, x)
    release performs R's normal action when o is normal and its
    abnormal action otherwise, and nothing when x was moved (Hold-out-moved)
(Move)
    <move x, st>  =>  the reference sigma(x),
                      st with x marked moved and R(x) removed from the
                      held set, so that no release runs; the sink owns it
(Guard-drop)
    a view remembers the layout token it was carved under; a step with
    effect resize changes the token; a read or write through a view
    whose token is not the current one  =>  err     (unreachable, T1)

(Store)
    p denotes (region r, offset o) with o + size(T) <= size(r)
        =>  the bytes of [[e]] written, normal
(Store-err)
    otherwise  =>  err                              (unreachable, T1)
(Atomic)
    as (Store), with the read-modify-write performed indivisibly and
    the previous value bound
(Call)
    K(row, [[a...]], st) = ok(v, st')    =>  v, st'
    K(row, [[a...]], st) = failed(n, st') =>  failed, st'[errno := n]
    a call forbidden by a row of the held set  =>  err  (unreachable, T1)
(Insert)
    mu(m)[k] := copy of the value, or failed when the map is full
```

A helper that resizes yields, through `K`, any packet its contract
allows; the old packet is gone, which is why typing kills views.

## 20. Properties and theorems

### 20.1 The properties

Each row names a property of every execution of a well-typed Core
program, the mechanism that provides it, and how: statically by typing,
dynamically by a marked test with a declared consequence, or by
construction of the semantics.

| property | mechanism | how |
|---|---|---|
| no access outside a region: stack, map value, packet | M1, M2 | static for stack and map values; dynamic at view carving |
| no dangling reference or view; no use of a place whose guard has been dropped | M2, M3 | static: places never escape, guards are checked at every use |
| every owned reference released exactly once or transferred exactly once, never both | M3 | static: `hold` release on unmoved paths, join consistency of `move` |
| no read of uninitialized memory | M2 | by construction: locals initialized at declaration, map values zero-filled, packet bytes are data |
| no undefined operation | P5 | by construction: total arithmetic with the kernel's semantics |
| termination, with a step bound computable from the syntax | M4 | static |
| every resource released exactly once, abnormally on abnormal exits; no forbidden effect while held | M3 | static, by elaboration |
| every kernel call respects its signature and preconditions | M1 | static, or a `check` |
| every failure reaches a handler that exits; no unmarked failure point | F | static |
| verdict within the declared set; preserved regions unwritten | M1, M3 | static |
| map invariants maintained by every store of this unit; relied on only after a test | M1 | static at stores, dynamic at marked loads |

### 20.2 Theorems

**T1, safety of Core.** For every kernel within its contracts, every
program of a well-typed unit, and every initial state, a derivation
ending in `halt(v)` exists and no derivation ends in `err`; and every
run has the properties of 20.1. Existence is progress and termination
in one, since Core's loops are bounded and its calls acyclic; the
absence of `err` covers the cases the rules make unreachable, an
out-of-bounds store, a use of a view under a dropped token, a call a
held row forbids. Proof by induction on the derivation with the typing
judgment as the invariant, a lemma per row of 20.1.

**T2, soundness of entailment.** If `F |= P` and `sigma` satisfies `F`
then `sigma` satisfies `P`. So no demand accepted statically can fail at
runtime, and a marked load's refinement holds of the value it bound.

**T3, totality of desugaring.** Desugaring is a total function from
surface programs to Core programs, and a surface program is well-typed
exactly when its desugaring is; every handler table is total after
defaults. Its content is that desugaring needs no typing information,
which the three forms kept in Core (18.1) arrange.

**Corollary, independence from the verifier.** Let the compiler be
correct in the sense that every execution of the bytecode it produces
refines an execution of the Core program under the mechanized in-kernel
ISA semantics (`yuan:ebpf-isa:oopsla:2026`). Then the bytecode has the
properties of 20.1 as well, whatever the kernel verifier believes about
it. In particular a well-typed program cannot perform the out-of-bounds
access, the arithmetic on a possibly null pointer, or the division by
zero that a verifier soundness bug would fail to catch. The condition on
the compiler is assumed here and validated per program outside this
definition; the kernel's own verification is retained as an independent
check, not replaced.

**Trusted, for the corollary.** Besides the compiler and the ISA
semantics, the corollary trusts three columns of the prelude's call
table: a call's effect set, its `own` and `T?` annotations, and the
region kinds of its parameters and result. A helper marked as not
resizing the packet when it does would let a view outlive its region.
The availability, context, slot-layout, and verdict-range columns
affect acceptance only: an error there makes a program fail to load or
rejects one that would have loaded, and never makes a safe program
unsafe.

**Lemma L, path facts.** Every fact in `F` that the checker uses to
discharge a demand is implied by the branch conditions on the
corresponding path of the lowered code. The four fact sources, a
branch, a declared loop bound, a marked load of a `where` field, and
the coercion, all lower to a comparison; configuration constants fold
to immediates. Two further obligations on the lowering are part of L:
every `as` between widths is emitted as the instruction the verifier
tracks exactly, a 32-bit move or a shift pair, never a masked 64-bit
arithmetic; and the register the compiled code indexes with is the one
the emitted comparison tested, never a copy. L is a property of the
lowering, stated here because
two consequences of the design rest on it: an elided test is safe for
acceptance exactly when the verifier's domain re-derives the fact from
those branches, which P9 arranges; and any goal a proof-carrying kernel
formulates at an instruction its domain cannot pass is entailed by the
path condition, so it is provable by the existing bytecode-level
machinery without any proof construct in the source.

**Outside the theorems.** Whether the kernel verifier accepts the
compiled bytecode is a property of the compiler, tested empirically;
Lemma L is the part of that property the language can state.

## 21. Decisions and open questions

Decisions in this draft, each reversible:

1. Total arithmetic with the kernel's semantics; `check` for programmers
   who want a zero divisor to fail.
2. Six failure kinds; reasons are `u32`; markers only at bindings; `?`
   abbreviates `else fail`.
3. Handlers per kind in the program header; non-failing; must exit; all
   exits checked against the verdict set.
4. Resources are a table; `with` is the one construct.
5. Views carry `off(h)`; write effects are region-indexed.
6. Contracts are the program's signature: verdict set, preserved
   regions, map invariants.
7. Configuration constants with folded conditionals; no conditional
   declarations.
8. `fails` is explicit.
9. Map contents are untrusted; only marked loads yield refined values.
10. Entailment is a small fragment with no solver; solver cross-check
    in testing; mechanization planned.

Draft 3 decisions, from `mechanisms-draft3.md`:

11. `check P` is sugar for the coercion `e as T?`; one construct.
12. No `prove` and no solver in the type system: the kernel formulates
    proof goals from bytecode, and Lemma L makes them provable.
13. The entailment fragment is fixed by acceptance (P9).
14. `with` is `hold`; resource constructors are prelude names.
15. `move x` is an expression; sinks are the kernel's operations;
    moved state merges at joins like the held set.
16. Guards on places subsume view invalidation.
17. Places are second class and never compared.
18. Loop caps are the bound's type; iterator loops `bounded N`, with
    `?` making the cap a failure; the kernel's loop forms are lowering
    targets only, and the timed `may_goto` is never chosen for an
    exact loop.
19. `sleep` is an effect, permitted per kind, forbidden while held.
20. The `helper` reason defaults to the errno.
21. `license` per unit.
22. The stack-size limit is not a language rule; the compiler reports
    frame size per program.

Revisions of 2026-09-13, from `ISSUES.md`:

23. One typed Core: the surface desugars syntactically and the typing
    rules are on Core; functions, constant conditionals, and `for` stay
    in Core until checked.
24. Struct literals with scalar fields are stack places.
25. A `syscall` body may fall off its end and returns 0; packet bodies
    must exit.
26. A function body may end in an expression, its result.
27. The prelude is a table the compiler carries; protocol numbers are
    prelude constants.
28. The newline rule applies in blocks and between items; `else` on
    the line of its `}`; `abort` a verdict in statement position.

Revisions of 2026-09-14, from `ISSUES.md`:

29. The twelve representation points of entry 11: the fine print of
    18.1, the prelude as an outer scope (6), a function with a result
    ending in `return` (16), the struct literal's type from the
    binding's annotation or the unique declared struct (8.2), counts of
    any unsigned type (8.4).
30. Iterator loops wait for their resource row; parse-only in this
    draft (entry 12).
31. Absence from a `T?` function is a bare `return`; `T` is a scalar
    (entry 9).
32. Header fields spelled as the kernel spells them; `sk_lookup_*`
    take the tuple only, a `SockTuple` (entry 4).
33. The greedy `except` list and the multi-line comment as a newline,
    as the parser and lexer do (entry 10).
Revisions of 2026-09-14, second pass, from `ISSUES.md` entries 13 to 17:
34. Slot types: `spinlock` is a prelude slot row, not a keyword or a
    Core constructor; Core's `T` has `slot(row)` and `R` is a row
    (entry 13).
35. The target kernel is the compiler's `--kernel` input; the region
    table's columns and packet writability per kind; `const n: T`
    prelude parameters; sleepable variants as kind rows; the trusted
    columns (entry 14).
36. The acquisition's argument form is a column; lexical scoping is a
    stated non-claim; `own T` uniformly (entry 15).
37. The callback-loop rules recorded with the deferral (entry 16).
38. Lemma L's two lowering obligations (entry 17).
Revisions of 2026-09-15, settled before the entailment code was
written:
39. `F` is the list of facts as they entered, with view offsets and
    name equalities; the abstract state is built from it at a demand,
    in entry order without a fixpoint, and written back only at a
    join as the hull (18.5).
40. Facts are about places, read through the references `let` binds;
    `kill`, the alias groups of `ref` parameters and of views, the
    kill of every shared fact at a call, and `inv` and `meet` as 18.4
    now states them.
41. A branch or a `check` yields facts about stack places only; the
    view offset is the one fact about a shared place (18.4).
42. One interval per variable, in its type's signedness, with known
    bits; not the verifier's paired ranges. P9 is one-directional, so
    the smaller domain is safe, and the corpus demands are unsigned
    (18.5).
43. The cap of a `for` loop is an output of the checker to the
    lowering, by loop, not a Core annotation; the postcondition of a
    function is a fact at the binding of its call (16).
44. Entailment folds each configuration constant to its value for the
    build, the default where none is supplied; the checker runs per
    build; a `config` with no value at all is an error (entry 18).
45. The store record `p = e` is kept for stack places only; a store to
    a shared place leaves no fact (entry 19).
Revisions of 2026-09-18, from `ISSUES.md` entries 20 to 24:
46. The dynamic semantics is a big-step relation over a machine,
    parameterized by a kernel that stands for the helpers' choices and
    is trusted to its contracts; the frames of the earlier small-step
    account are the enclosing rules; T1 quantifies over every such
    kernel and states existence of a halting derivation and absence
    of `err` (sections 19, 20).
47. A view carve and a byte read demand that the window lies under
    the region's max offset, a column of the region table, 65535 for
    the packet; the lowering adds no bound test (entry 21).
48. P2 admits a branch the verifier requires on a path the kernel's
    contract makes unreachable, ending in the kind's default failure
    verdict (entry 22).
49. The atomic updates take a place of a 32- or 64-bit integer type
    (entry 23).
50. The machine of section 19.1 is aligned with the lowering's target:
    byte-order values are bit patterns, memory is little-endian, the
    layout token travels with the location, the state carries a trace
    of kernel calls and `printk` events, the predicate frame of a
    marked load is built from the fields, and a kernel function's
    failure signal follows its result type (entry 24).
Revisions of 2026-09-19, from `ISSUES.md` entries 25 to 27, at the
end of the session that lowered Core to LIR:
51. A loop head keeps a bound on a local its body only increments,
    and a store keeps what a dropped equation said of its other side
    and what the state knew of a self-referring value, as 18.4 now
    states; the section 23 examples stand unchanged under decision 47
    (entry 25).
52. The trace settles `printk`'s untyped arguments, a held lock's
    object is its place, and a row with no effects is still a kernel
    call, so that every level of the lowering compares equal on the
    shared state (entry 26).
53. The evaluator's failures carry the state they left: a map
    written before a `fail` stays written when the handler runs, as
    the rules always said (entry 27, a correction of the evaluator).
54. The shared state of 19.1 is one definition with no location of
    any level in it: a held object is a map slot and offset or a
    kernel object, a traced memory argument is bytes; Core's regions
    extend the shared ones with the struct literals' frames (entry
    30, 2026-09-19).

Open questions, with the default the checker implements until decided:

- Q1. Handlers on functions. Default: no; a function-level handler is
  a `try` and breaks declare-once.
- Q2. Closed 2026-09-13: local struct literals with scalar fields are
  supported (section 8.2); the stack rule is the compiler's frame
  report (decision 22).
- Q3. User-defined resources. Default: none; rows come from the prelude.
- Q4. A parsing cursor as sugar over consecutive views. Default: none.
- Q5. Conditional declarations under `config`. Default: none.
- Q6. Views on regions other than the packet. The core rule is general;
  this draft instantiates it for the packet only; dynptr slices and
  runtime-sized memory arrive with the extensions.
- Q7. Asynchronous callbacks as program kinds. Default: defined by the
  tracing extension, not in the core.
- Q8. An interruptible loop as declared semantics for the kernel's
  time-budget cut. Default: none; exact loops only.
- Q9. A second lowering of failure through `bpf_throw` and the
  exception callback. Compiler question; the portable lowering, jumps
  and error codes generated by elaboration, comes first.
- Q10. Whether the context and availability tables are probed from the
  running kernel or transcribed per version. Tooling question; probing
  is recommended.

## 22. Extensions not yet defined

Design notes for the extensions the core is built to receive, recorded
so that later drafts do not rediscover them.

**The kernel-memory extension**, for tracing and LSM programs. A fourth
region kind, kernel objects read through type information and fallible
probe reads, with a failure kind for a failed read. It adds the rows
draft 3 designed for: RCU-protected pointers as places guarded by the
RCU section; owned references to tasks, sockets, and allocated objects
bound by `hold` and moved into map fields by exchange or into lists
and trees by insertion, the inserted node becoming a place guarded by
the structure's lock; resilient locks with a fallible acquire;
preempt-off and IRQ-off sections; generic kernel iterators; dynptrs as
a region whose slices are views; and asynchronous callbacks, timers,
workqueues, and task work, as program kinds with their own context and
an empty initial held set. Pointer-typed fields
and arguments are nullable by default and consumed through a marked
load, so the language never inherits the verifier's table of which
kernel pointers may be null; two of the CVEs in `cve-study.md` were
errors in that table. Its resource rows add task and socket references
and its context types come from the kernel's BTF.

**The struct-ops extension**, for schedulers and similar callback sets.
A program becomes a set of typed callbacks over kernel objects with
reference discipline; the resource table grows first, since the sched_ext
schedulers we surveyed use spin locks, RCU, cpumask and object references
heavily.

**Iterator and map loops**, deferred with decision 30: `for x in it
bounded N` over a kernel iterator, and `for (k, v) in m` over a map,
which the kernel runs through a callback. Two rules hold for the body
when they arrive: locals it uses from the enclosing scope are passed as
places, and the caller's held set is visible inside, so a call
forbidden under a held lock is forbidden in the body. A map loop
requires a `bounded` cap; its body may delete the current key and
perform no other operation on the map. Whether the loop becomes a
callback, an open-coded iterator, or a counted loop is the compiler's
choice (decision 18).

**Features not tied to a program type**, deferred:

- tail calls as an explicit exit that never returns, with the `call`
  effect, for programs that dispatch through program arrays by design
  rather than by necessity;
- separately verified functions with declared contracts, for program
  size, once the verifier's global-function interface is modeled;
- the userspace boundary: a map declaration generating its userspace
  accessor with the same key and value types, and program handles with
  a load-then-attach typestate, in KernelScript's style;
- user-defined resources, adding rows to the resource table from user
  code;
- conditional verdicts and relational map properties, which need
  predicates over the input and reasoning about memory reads;
- contracts on functions, a middle layer for helper libraries.

## 23. The program template and examples

### 23.1 The template

Every unit has the same four parts, in this order, and every program body
has the same three phases.

```
// 1. constants, configuration, and types
const M = 16
config SLOTS : u32 = 65536
type Hdr = { ... }

// 2. shared state: maps, with invariants on what this unit writes
map policy : array[1] of { cur: u32 where cur < M }

// 3. functions: contracts on parameters and results, `fails` if needed
fn step(h: u32, c: u8) -> u32 { ... }

// 4. entry points: contract and failure policy first, then the body
program name : xdp
  verdict in { PASS, DROP, TX }
  fail drop
  on short_packet { pass }
  on invariant    { stats[0].bad += 1; abort }
{
  // parse: carve views, one fallible operation per line
  let eth = pkt.view<EthHdr>(0)?
  // decide: marked loads and lookups; ordinary cases are branches
  let cur = policy[0].cur?
  if eth.proto != ETH_P_IP { pass }
  // act: writes, resources, calls, then a verdict
  hold lock(e.lk) { ... }
  tx
}
```

The reading rule: a line with `?` or `else` can fail, a line without
cannot; a `hold` line holds something until its block ends; a verdict is
an exit; the header says what the program may return and what it leaves
alone.

### 23.2 Configuration-driven backend picker

```
const M = 16
const ETH_P_VLAN = hton(0x8100)
const ETH_P_IP   = hton(0x0800)

type EthHdr  = { dst: u8[6], src: u8[6], proto: be16 }
type VlanHdr = { tci: be16, proto: be16 }
type Backend = { ip: be32, ifindex: u32 }

map policy   : array[1] of { cur: u32 where cur < M }
map backends : array[1] of Backend[M]

program pick : xdp
  verdict in { PASS, DROP, ABORTED, REDIRECT }
  preserve pkt
  fail abort
  on short_packet { drop }
{
  var off = 0
  // short_packet: drop
  let eth = pkt.view<EthHdr>(off)?
  off += EthHdr.size
  var proto = eth.proto
  repeat 2 {
    if proto != ETH_P_VLAN { break }
    let tag = pkt.view<VlanHdr>(off)?
    proto = tag.proto
    off += VlanHdr.size
  }
  // an ordinary case, not a failure
  if proto != ETH_P_IP { pass }
  // invariant: abort; afterwards cur : {v | v < M}
  let cur = policy[0].cur?
  // demand cur < M: entailed
  let be  = backends[0][cur]
  // helper: abort; the result is REDIRECT, which the verdict set admits
  let v   = redirect(be.ifindex)?
  return v
}

program rotate : syscall {
  // demand (x + 1) % M < M: entailed
  policy[0].cur = (policy[0].cur + 1) % M
}
```

### 23.3 A memcached cache in the shape of BMC

```
const MAX_KEY   = 250
const MAX_VAL   = 1000
const DATA_SIZE = MAX_KEY + MAX_VAL + 53
config SLOTS : u32 = 3250000
const MC_PORT   = hton(11211)
const REASON_NOT_GET  = 1
const REASON_LONG_KEY = 2

type Ipv4Hdr = { vihl: u8, tos: u8, len: be16, id: be16, frag: be16,
                 ttl: u8, protocol: u8, csum: be16,
                 saddr: be32, daddr: be32 }
type UdpHdr  = { source: be16, dest: be16, len: be16, csum: be16 }
type McHdr   = { req_id: be16, seq: be16, n: be16, reserved: be16 }

type Entry = {
  lk:    spinlock,
  valid: u8,
  hash:  u32,
  // holds of the zero value
  len:   u32 where len <= DATA_SIZE,
  data:  u8[DATA_SIZE],
}
type Stats = { hits: u64, misses: u64, short: u64, other: u64 }

map cache : array[SLOTS] of Entry
map stats : percpu_array[1] of Stats

fn fnv_step(h: u32, c: u8) -> u32 { (h ^ (c as u32)) * 16777619 }

// whatever we cannot serve goes to the stack
program bmc_rx : xdp fail pass
  on short_packet { stats[0].short += 1; pass }
  on program      { stats[0].other += 1; pass }
  // a corrupted entry is a bug; make it visible
  on invariant    { abort }
{
  var off = 0
  let eth = pkt.view<EthHdr>(off)?
  if eth.proto != ETH_P_IP { pass }
  off += EthHdr.size
  let ip = pkt.view<Ipv4Hdr>(off)?
  if ip.protocol != IPPROTO_UDP { pass }
  off += ((ip.vihl & 0xf) as u64) * 4
  let udp = pkt.view<UdpHdr>(off)?
  if udp.dest != MC_PORT { pass }
  off += UdpHdr.size + McHdr.size
  let cmd = pkt.view<u8[4]>(off)?
  let is_get = cmd[0] == 'g' && cmd[1] == 'e' && cmd[2] == 't' && cmd[3] == ' '
  if !is_get { fail REASON_NOT_GET }
  off += 4
  let koff = off

  // hash the key; n <= MAX_KEY follows from i < MAX_KEY
  var h: u32 = 2166136261
  var n: u64 where n <= MAX_KEY = 0
  for i in 0..MAX_KEY {
    let c = pkt[koff + i]?
    if c == ' ' || c == '\r' { break }
    h = fnv_step(h, c)
    n = i + 1
  }
  if n == 0 || n == MAX_KEY { fail REASON_LONG_KEY }

  // demand h % SLOTS < SLOTS: entailed
  let e = cache[h % SLOTS]
  // helper: pass; kills eth, ip, udp, cmd
  pkt.adjust_tail(DATA_SIZE as i32)?

  var rlen: u64 where rlen <= DATA_SIZE = 0
  // no calls inside; released on every exit below
  hold lock(e.lk) {
    // invariant: abort, after unlocking
    let len = e.len?
    if e.valid == 1 && e.hash == h && (len as u64) >= n {
      var same = true
      // bound from n's refinement
      for i in 0..n {
        // short_packet: unlock, count, pass
        let c = pkt[koff + i]?
        // demand i < DATA_SIZE: i < n <= MAX_KEY
        if e.data[i] != c { same = false }
      }
      if same {
        rlen = len as u64
        for i in 0..rlen {
          let d = pkt.view<u8>(koff + i)?
          // demand i < DATA_SIZE: i < rlen <= DATA_SIZE
          *d = e.data[i]
        }
      }
    }
  }
  if rlen == 0 { stats[0].misses += 1; pass }
  stats[0].hits += 1

  // re-carve after the resize
  let eth2 = pkt.view<EthHdr>(0)?
  // a function over a view, no effects
  swap_addresses(eth2)
  // ... swap IP and UDP addresses, fix lengths and checksums ...
  tx
}

program bmc_tx : tc fail pass
  on short_packet { pass }
{
  // parse the server's reply, hash its key as above, then:
  let e = cache[h % SLOTS]
  hold lock(e.lk) {
    e.hash = h
    // demand n <= DATA_SIZE: entailed from n's refinement
    e.len  = n as u32
    for i in 0..n { let c = pkt[voff + i]?; e.data[i] = c }
    e.valid = 1
  }
  pass
}
```

### 23.4 The proposal's monitor and packet filter, as contracts

```
contract Monitor : xdp {
  verdict in { PASS }
  preserve pkt
  preserve maps except stats
}

map verdicts : hash[65536] of Flow -> { v: u32 where 1 <= v && v <= 2 }

program filter : xdp
  verdict in { PASS, DROP }
  preserve pkt[0 .. 14)
  fail drop
{
  let eth = pkt.view<EthHdr>(0)?
  let ip  = pkt.view<Ipv4Hdr>(EthHdr.size)?
  // ... parse, build the flow key ...
  // write(pkt[22..23)): disjoint from [0, 14)
  ip.ttl = ip.ttl - 1
  let f = verdicts[key] else { pass }
  // v : {v | 1 <= v && v <= 2}
  let v = f.v?
  // demand v in {PASS, DROP}: entailed, DROP = 1, PASS = 2
  return v
}
```

### 23.5 A rejected program

```
program bad : xdp {
  let eth = pkt.view<EthHdr>(0)?
  pkt.adjust_head(-8)?
  // error: view `eth` was invalidated by `adjust_head` at line 3
  let p = eth.proto
}
```
