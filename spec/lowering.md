# The lowering: passes, theorems, and the plan of proof

Status: draft 1, 2026-09-18, the third of the three documents that
settle session 6 before code. `lir.md` defines the first intermediate
language and `bir.md` the second together with the target machine.
This one defines the passes between Core and bytecode, states what
each preserves and how the statements compose into the compiler's
correctness theorem, restates Lemma L on the code the passes emit,
fixes the trusted base, and orders the proofs. Decisions 47 to 50 of
`language.md` are assumed. The decisions this draft embeds are listed
in section 12.

## 1. The pipeline

```
surface --desugar (T3)--> Core --check (T1, T2)--> Core, accepted
Core --A fold--> Core --B explicit--> LIR --I inline--> closed LIR
closed LIR --C flatten--> BIR --D allocate--> bytecode --E encode--> object
LIR --P print--> C source                        untrusted, section 9
```

Five semantic passes, A, B, I, C, and D; one encoding, E; one
printer, P. Three languages, Core, LIR, and BIR, and one machine
under all of them, whose state is shared verbatim across every pass:
maps, packet, layout token, kernel objects, held stack, trace
(`bir.md`, section 2). No pass owns a memory model of its own, and
the relation between two levels speaks only of locals and registers.

| pass | from, to | settles | leaves open |
|---|---|---|---|
| A | Core to Core | constants, dead constant branches, the access form of each map | everything else |
| B | Core to LIR | every test, release, and unwind; widths; addresses | functions, structure, registers |
| I | LIR to LIR | functions | structure, registers |
| C | closed LIR to BIR | structure, frame offsets, the 32-bit normal form, byte moves | registers |
| D | BIR to bytecode | registers, spill slots, the calling convention, label offsets | nothing |
| E | bytecode to object | words, relocations, BTF, sections | nothing |

The compiler is `compile = fold ; lower ; inline ; flatten ; alloc ;
encode`, a partial function on checked units: a frame over 512
bytes, a program over the instruction budget, or a construct the
target kernel lacks is a reported error, and every theorem is stated
for the `.ok` result.

## 2. What is preserved

### 2.1 Behaviors

A behavior of a program from an initial state, for a kernel `K`, is
what the kernel and the rest of the system can observe of the run:
the verdict, the final maps, the final packet, and the trace of
kernel calls and `printk` events in order (`language.md`, 19.1).
Core has exactly one behavior per initial state and kernel within its
contracts: T1 gives a halting derivation, and the rules are functional
in `K`. The machine has exactly one run per initial state, since its
step is a function of `K`. Preservation is therefore an equality of
behaviors. CompCert's theorem, that every behavior of the compiled
program improves some behavior of the source, collapses to equality
here because the source neither diverges nor goes wrong, and the
forward simulation that CompCert must turn around through the
determinism of its target is here the whole proof, for the same
reason. The price is the precondition: CompCert speaks of every C
program without undefined behavior, this theorem of every unit the
checker accepts.

### 2.2 The relation between states

`Agree st m` holds between a Core state and a machine state when the
shared parts are equal: the maps, the packet and its token, the
kernel objects and rings, the trace, and the held stack read as its
rows and objects, names dropped. Locals and registers are not
mentioned: at a halt they no longer matter. The per-pass relations
of sections 3 to 7 refine `Agree` with what each level keeps of the
locals.

### 2.3 The theorem

```
theorem compile_correct (pre u obj K) :
    KernelOk K → UnitOk pre u → compile pre u = .ok obj →
    ∀ p ∈ u.programs, ∀ st, Initial pre u p st →
      ∃ v st' m,
        ExecProgram K st p (.halt v) st' ∧
        Star (Step K) (load obj p st) m ∧ Halted m v ∧ Agree st' m
```

The existence of the Core derivation is T1's; the theorem adds the
run. From it and two properties of the machine, that `Step K` is a
function and that a stuck state has no successor, follow:

```
corollary bytecode_safe (pre u obj K) :
    KernelOk K → UnitOk pre u → compile pre u = .ok obj →
    ∀ p ∈ u.programs, ∀ st, Initial pre u p st →
      ∀ m, Star (Step K) (load obj p st) m → ¬ Stuck m
corollary bytecode_unique : the run of 2.3 is the only run, and its
    verdict, final maps, packet, and trace are the source's
```

`Stuck` is the list of `bir.md`, 5.3, which is the verifier's list.
So the corollary of `language.md` 20.2 reads, with its compiler
condition discharged: a well-typed program's bytecode never performs
an access outside its region, through a stale packet pointer, or on
an uninitialized slot, never leaks a pointer, never calls under a
lock, never exits holding a resource, and never trips a context or
argument rule, whatever the kernel verifier believes about it. What
remains assumed is the machine's faithfulness to the kernel,
validated as `bir.md` section 9 says.

### 2.4 Composition

Each pass has a theorem of the same shape, a forward simulation from
the level above to the level below under a relation that refines
`Agree`; the relations compose by relational composition and the
simulations by transitivity. Two passes translate between big-step
semantics, A and B, and one within a big-step semantics, I; their
theorems say a derivation above yields a derivation below. C
translates from a big-step semantics to the machine's small step;
its theorem says a derivation yields a `Star` of steps. D translates
within the machine; its theorem is a step diagram. The chain is:

```
ExecProgram K st p (halt v) st'                                  Core
  ⟹ (A) ExecProgram K st (fold p) (halt v) st'
  ⟹ (B) LIR.ExecProgram K st_B (lower p) (halt v) st_B', R_B st' st_B'
  ⟹ (I) LIR.ExecProgram K st_B (inline (lower p)) (halt v) st_I', Agree
  ⟹ (C) Star (Step K) (loadB B st) m_C, Halted m_C v, R_C st_I' m_C
  ⟹ (D) Star (Step K) (load obj p st) m, Halted m v, R_D m_C m
  ⟹ Agree st' m
```

## 3. Pass A: fold and select

**Definition.** On a checked unit, with the build's configuration:
every `config` name and `size T` and verdict and prelude constant
becomes a literal; every `ite` whose condition is a constant
expression becomes its live branch, both having been checked; every
`array[1]` map is marked for direct value access and every other map
for lookup by helper (`lir.md`, 6.4); the cap of each `for` loop,
from `Checked.caps`, is attached to the loop as an annotation that
selects its bytecode form in pass C and never enters a semantics.
Nothing else changes. The output is Core.

**Theorem A.** For every `K`, `st`, `p`, and outcome,
`ExecProgram K st p o st' ↔ ExecProgram K st (fold p) o st'`.

**Proof shape.** Induction on the derivation, one case per rule. A
constant evaluates to its value by the rules `varConst`, `varConfig`,
`varVerdict`, `varPrelude`, and `size`; a folded `ite` takes the
branch the condition's value selects. The map marking changes no
rule. This is the free pass, and it is separate so that B never sees
a constant or a dead branch.

## 4. Pass B: Core to LIR

### 4.1 Definition

The translation is per function and per program, driven by the
checker's `Env` for types and by four pieces of context threaded
through statements:

- `Γ`, the type of each Core name in scope, from which the width and
  signedness of every operator and literal are read;
- `ρ`, the release context: a stack of scopes, each either a boundary
  marker for a `block` or `loop` the translation has opened, or a
  release action `(row, x, normal, abnormal)` for a `hold` whose body
  is being translated, innermost last;
- `μ`, the set of owned names moved on the current path, which is
  the same on every path reaching a point (Lemma M below);
- `δ`, the number of `block` and `loop` constructs the translation has
  opened, for the depth of each `br`.

Expressions lower in two modes. A Core expression with no call, no
hash lookup, and no map slot reached by helper lowers to one pure LIR
expression at the checker's types. Any other expression lowers in
administrative normal form: each subexpression in Core's evaluation
order into its own `let`, so that every call and every load happens
in the order the rules `arith`, `cmpInt`, `andBoth`, and `EvalArgs`
of `Semantics.lean` fix. Places lower to addresses the same way, a
place reached by helper contributing the statements of `lir.md`, 6.4.

Statements lower as `lir.md`, section 6, shows. The context decides
the three things that section leaves implicit:

- **Exits.** `break` lowers to the abnormal releases of every action
  in `ρ` above the enclosing loop's boundary, innermost first, then
  `br n` with `n` the number of markers up to that loop's exit block;
  `continue` likewise to the body block; `return e` and `raise k e`
  to the abnormal releases of every action in `ρ`, then the
  statement; the fall-through of a `hold` body to the normal release.
  An action for a name in `μ` emits nothing.
- **Calls.** A call to a `fails` function carries `unwind s`, with `s`
  the abnormal releases of every action in `ρ`, innermost first, for
  names not in `μ`.
- **Moves.** `move x` emits nothing and adds `x` to `μ` for the rest
  of the sequence; at an `if`, both branches yield the same `μ` and
  it continues; a loop body yields the `μ` it started with, except on
  paths that leave the program.

The widths of the coercion and marked-load tests, the sibling loads
of a marked load, and the key frames of lookups are as `lir.md`
sections 6.2 and 6.5 say. A program lowers to its body under an
empty `ρ` and `μ` and its six handlers.

### 4.2 The relation

`R_B st_C st_L` holds when `Agree` holds on the shared parts and,
for every Core name `x` in scope with `Γ x = T`: a scalar `x` bound
in Core to `v` is bound in LIR to `fit(T, v)`; an aggregate or view
`x` bound in Core to a place `l` with token `t` is bound in LIR to
`loc(l.region, l.off, t)`; a moved `x` is unbound in LIR. Names
LIR introduces, the key frames, the sibling temporaries, the `err`
local, and the loop counters, are unconstrained.

### 4.3 Theorem B

```
theorem lower_correct (pre u K) :
    KernelOk K → UnitOk pre u → lower pre (fold u) = .ok U →
    ∀ p ∈ u.programs, ∀ st v st',
      ExecProgram K st p (.halt v) st' →
      ∃ st_L', LIR.ExecProgram K (init_B st) (U.program p) (.halt v) st_L'
               ∧ R_B st' st_L'
```

and, for the induction, its statement-level form: if
`ExecStmt K st s o st'` and `R_B st st_L`, then the translation of
`s` under the context that `st` satisfies runs from `st_L` to an
outcome `o_L` and a state `st_L'` with `R_B st' st_L'`, where `o_L`
is `o` with Core's `brk` and `cont` read as the `br` the context
assigns them, and with a `raise` preceded by the releases the context
owes.

### 4.4 Proof shape and what it uses

Induction on the Core derivation with one lemma per rule of
`ExecStmt`, `ExecFall`, and `Call`. Three lemmas carry the weight:

- **Lemma W, widths.** In a run of a well-typed program, an
  expression the checker gives type `int(s,w)` evaluates to an
  integer that `fit(int(s,w), ·)` leaves unchanged, and a polymorphic
  literal meets an operand of that type. This is the preservation
  half of T1 for expressions, stated separately so that B can cite
  it; it is why the dynamic meeting of widths in Core and the static
  widths in LIR agree.
- **Lemma M, moves.** In a well-typed program the set of owned names
  moved on a path is a function of the program point. This is the
  join rule of `move` and the loop rule, restated as a semantic
  invariant; it is why the release code at each exit is static.
- **Lemma H, releases.** For a `hold` body translated under an
  action `(R, x, n, a)`: on the normal outcome the normal release
  has run once, on every other outcome the abnormal release has run
  once, and on a path through `move x` neither has, so that the LIR
  held stack after the body equals Core's after `releaseRes`. Proved
  by induction on the body with the exit cases of 4.1.

What B does not use: T2, or any fact. Every test Core has, B emits,
and B adds only the dead branch of decision 48, which the Core
derivation's in-range index makes untaken. A demand the checker
discharged corresponds to a premise of a Core rule, `idx < len` in
`EvalPlace.index`, and the Core derivation supplies it; the LIR load
at the same address is admitted for the same reason. Elision is
therefore T1's business, not B's.

## 5. Pass I: inlining

**Definition.** As `lir.md`, 6.6: in call-graph order, leaves first,
each `x = call f(args) unwind U absent A` is replaced by `block {
params bound; body }` with the callee's locals renamed apart, `return
e` replaced by `x := e; br d`, bare `return` by `A; br d`, `raise k
e` by `U; raise k e`, and a nested `call g unwind U'` by `call g
unwind (U'; U)`, where `d` is the depth of the return inside the
callee's body. Scalars bind by value into fresh locals; `ref`,
`view`, and `own` parameters bind to the argument's location. The
result has no `call` statements and is closed LIR. Termination is by
the acyclic call graph, decision 26 of `language.md` section 16.

**Theorem I.** For every `K`, `st`, and program `P` of a
well-formed LIR unit, `LIR.ExecProgram K st P (.halt v) st'` implies
`LIR.ExecProgram K st (inline P) (.halt v) st''` with `Agree st'
st''`, the locals of the inlined copies being fresh.

**Proof shape.** One lemma per call: a run of the callee's body in
its own frame from the caller's shared state is a run of the renamed
body inside the caller's frame, with `ret` becoming `br d` caught by
the wrapping block, `raise` preceded by `U` as the call rule would
have run it, and absence becoming `A` in place. Induction on the
call-graph order composes the lemmas. The `unwind` substitution is
the delicate case: the callee's own releases run before its `raise`
by Lemma H applied inside the callee, and `U` then runs the caller's,
which is the order the call rule of `lir.md` 5.2 prescribes.

## 6. Pass C: flattening

### 6.1 Definition

On a closed LIR program: statements become instruction sequences
with labels; `block s` becomes the code of `s` followed by an exit
label, `loop s` a head label followed by the code of `s` and a jump
back, and `br n` a jump to the label of the `n`-th enclosing
construct, the exit label of a block or the head label of a loop; an
`if` becomes a `jcond` on the condition's comparison to the else
label; `raise k e` becomes a move of `e` into `v_reason` and a jump
to `handler_k`; `return e` a move into `v_ret` and a jump to the
program's exit sequence. Pure expressions become instruction
sequences over fresh virtual registers, one per intermediate value,
each ALU instruction at the class the width selects and each narrow
result normalized as `bir.md` section 4 says; casts by the table
there; `bswap` by `end`. Addresses become `alu` on a location
register. `frame x : n` becomes a declared object and `lea`, with
the object zero-filled by `st` instructions; `copy n` and `fill n`
become runs of loads and stores by 8, 4, 2, and 1 bytes. Builtins and
kernel functions become `call` with explicit operands. `ctx f`
becomes `ldx` from `v_ctx` at the field's offset and width, and
`pkt_data`, `pkt_end` the two location-yielding rows. A `for` loop's
annotation from pass A selects its form; in stage 1 every loop is the
counted loop of `lir.md` 6.1, and `bpf_loop` and the iterator forms
are later selections with their own templates.

### 6.2 The relation

`R_C st_L m` holds when `Agree` holds on the shared parts, the
machine's `pc` is the label the derivation has reached, every LIR
local of type `int(s,w)` bound to `v` is held by its virtual register
in the 32-bit normal form of `v`, every local of type `ptr` bound to
`loc(r, o, t)` is held as that location, except that a location into
an LIR stack region `stack(id)` is held as `loc(frame, base(id) + o,
t)` with `base` the offset the flattening assigned to that frame
object, and the frame's bytes at `base(id)` are the region's bytes.
This last clause is the one injection in the whole lowering, from
LIR's many small stack regions into the machine's one frame; it is
simple because the regions are disjoint by construction and never
escape.

### 6.3 Theorem C

```
theorem flatten_correct (K P B) :
    flatten P = .ok B →
    ∀ st v st', LIR.ExecProgram K st P (.halt v) st' →
      ∃ m, Star (Step K) (loadB B st) m ∧ Halted m v ∧ R_C st' m
```

with the statement-level form: if `LIR.ExecStmt K st s o st'` and
`R_C st m` with `pc` at the start of the code of `s`, then the
machine reaches, in zero or more steps, a state `m'` with `R_C st'
m'` and `pc` at the label `o` selects: the end of the code for
`normal`, the `n`-th enclosing label for `br n`, `handler_k` for
`raise k`, the exit sequence for `ret`.

### 6.4 Proof shape

Induction on the LIR derivation; the classic proof that compiling
structured code to labeled code is correct, in the form Leroy's
course gives for a while language and a virtual machine, extended
by the label stack that `block`, `loop`, and `br` need, which is the
form the WebAssembly proofs take. The expression lemma is a finite
table: for each operator, width, and signedness, the instruction and
its normalization compute `arith` of `Machine.lean` on normal forms.
The width table of `bir.md` section 4 is that lemma's statement. Pass
C also establishes BIR's well-formedness, registers written before
read and labels defined once, which pass D assumes.

## 7. Pass D: allocation and encoding

### 7.1 Definition

The naive allocation of `bir.md` section 7: every virtual register
gets an 8-byte spill slot below the frame objects; `v_ctx` is copied
from `r1` into `r6` at entry; each BIR instruction becomes loads of
its operands from their slots into `r1` to `r3`, the instruction on
those registers, and a store of the result to its slot; a `call`
loads its operands into `r1` to `r5`, calls, and stores `r0`; `lea`
becomes `mov r1, r10; add r1, off`. Labels become instruction
offsets. If the slots and objects exceed 512 bytes the program is
rejected with its frame size.

Encoding, E, is the word layout of `bir.md` section 7 with the
kernel's opcode tables, and the relocation list for `mapref` and
`mapval`.

### 7.2 Theorem D and the encoding lemma

`R_D m_B m` holds when the shared state, `pc` modulo the offset
table, and the held stack agree, `r10` is the frame pointer, `r6`
holds the context location, and every virtual register's value is in
its slot, spilled or as bytes according to its class.

```
theorem alloc_correct (K B O) :
    alloc B = .ok O →
    (∀ m_B m_B', R_D m_B m → Step K m_B = some m_B' →
       ∃ m', Plus (Step K) m m' ∧ R_D m_B' m') ∧
    (∀ st, R_D (loadB B st) (load O st)) ∧
    (∀ m_B m v, R_D m_B m → Halted m_B v → Halted m v)

theorem encode_decode (O) : decode (encode O) = O
```

The diagram is a plus simulation, each BIR step matched by one or
more bytecode steps and no stuttering, so no measure is needed. The
star-level statement of section 2.4 follows by induction on the
`Star`. A later linear-scan allocator replaces the naive one as an
untrusted function checked by a verified validator, and the theorem
becomes one about the validator, the way CompCert treats register
allocation.

## 8. Lemma L on the emitted code

Lemma L of `language.md` section 20 is the acceptance half of the
design, and no theorem here proves acceptance, since the verifier is
not modeled. What the passes give is the syntactic part of L, as
properties of the BIR the pipeline emits, each checkable on the
output:

- **L1, every fact is a branch on the path.** Pass B emits an `if`
  wherever Core has a `try`, a `for` bound, or a coercion, and
  removes none; pass C emits a `jcond` for every `if`; passes I and D
  add and remove no tests. So each of the four fact sources of L is a
  `jcond` on the path that reaches the use, and configuration
  constants are immediates by pass A. Provable as a property of the
  translations: every marker of the source has a `jcond` in the
  output whose condition is the marker's test. Whether the verifier's
  domain re-derives the fact from that branch is P9's conjecture,
  measured by E6.
- **L2, every cast is a tracked instruction.** By the cast table of
  `bir.md` section 4, which pass C implements; a property of the
  table.
- **L3, the indexing register is the tested register.** Pass B binds
  a coerced or marked value to one LIR local and uses that local at
  every later site; pass C gives it one virtual register; pass D one
  slot. Between the test and a use the value passes through its slot,
  and the verifier carries the bounds through an 8-byte spill and
  links the slot to the registers loaded from it on the kernels the
  plan targets. If E6 shows a kernel where it does not, the first
  allocation keeps a tested value in `r7` to `r9` until its last use
  in the same block, which is a local change to pass D.
- **The offset bound.** By decision 47 the checker demands that a
  view's window lies under the region's maximum offset, so the
  scalar pass C adds to `data` has a bound the verifier re-derives
  from the branch that established it; no bound test is emitted.

A small checker over BIR, `koitc shape`, tests L1 to L3 on every
emitted program in the runner: each `jcond` that pass B emitted for a
marker is present, each cast is in the table, and each access
register is the register of the comparison that dominates it. It is
a test, not a proof, and its failures are compiler bugs.

## 9. The printer, P

The C printer of `lir.md` section 8 reads LIR after pass B, before
inlining, since C has functions. It is not in any theorem. Its two
obligations are engineering: no C undefined behavior is reachable,
which the total-arithmetic shim and unsigned operations secure, and
the emitted C is what a reader expects of the source, one construct
per construct. It serves three purposes: the readable artifact of the
paper, the path through libbpf until the ELF writer of pass E exists,
and the cheap experiment of compiling koit's C through CompCert-BPF
for the related-work sentence. Acceptance idioms it adds for clang,
such as `barrier_var` after a coercion, are recorded here as they
are found and never enter LIR.

Printer policy as of session 6 (2026-09-19), each a choice of the
printer and not of any pass:

- `block`, `loop`, and `br` are a label after the block, `for (;;)`
  with a label at the head of its body, and `goto`; no re-sugaring
  into `for` with `break` and `continue` yet.
- A `fails` or `T ?` function returns an `int` status: 0 for a value,
  written through an out-parameter, 1 for absence, `2 + k` for a
  failure of kind `k` with the reason written through a `u32 *`
  parameter. A call site tests the status: a program body runs the
  `unwind` and jumps through a `switch` on the kind to the handler; a
  function runs its `unwind` and returns the status.
- A `raise` in a program body is `reason = e; goto handler_k;`; the
  handlers are labeled tails of the program's C function, each in
  its own block, ending in `return`.
- A map read by direct value access is looked up once at the
  program's entry by the key zero with a null test that returns the
  kind's failure verdict, since C has no direct value access for a
  declared map; `mapval m + k` is then an offset from that pointer.
- A `frame` is an 8-aligned zeroed object of the source type and a
  `void *` pointing at it, so that every mention of the frame's name
  is the pointer LIR means.
- Kernel functions go through templates that add the arguments the
  helpers take and the source does not name: `bpf_redirect`'s flags,
  the context of the resizes and the socket lookups, the tuple size
  and `BPF_F_CURRENT_NETNS`; in `tc` programs `pkt.adjust_tail` and
  `pkt.adjust_head` compute `bpf_skb_change_tail`'s new length and
  `bpf_skb_change_head`'s headroom from the delta, which the corpus
  does not exercise. `pkt.len` prints as the subtraction of the
  context fields.
- Arithmetic goes through the shim `tests/emit/koit.h`: every `+ -
  * & | ^` is computed unsigned at the width and cast, division,
  modulo, and shifts through `koit_div_T`, `koit_mod_T`,
  `koit_shl_T`, `koit_shr_T`, which implement section 8.1 of the
  definition; casts are C casts between fixed-width types.
- A koit name that is a C keyword, or one the printer uses itself,
  gets a trailing underscore.
- The shim declares the helpers by their uapi numbers and the
  context structs with the uapi offsets, since the kernel tree on
  this machine has no generated `bpf_helper_defs.h`; session 8's
  generator replaces it.
- Clang is run with `-fno-builtin`, since its loop idiom recognition
  otherwise turns a byte loop into a `memset` call the BPF backend
  cannot emit.

## 10. The trusted base

| trusted | for | how it is checked |
|---|---|---|
| the machine's stuck-state list, `bir.md` 5.3 | that it is the verifier's list and the kernel's behavior | differential runs, instruction replay, and the verifier's verdicts (`bir.md` 9) |
| the machine's builtins and the return convention | the kernel's map, ring, and lock semantics | the same |
| the call table's effect, `own`, `T?`, region, and failure-signal columns | `KernelOk` and argument fitting | already trusted for the corollary of section 20.2 |
| the context table and the helper numbers | context access and the assembler | generated from the kernel in session 8 |
| the encoder, the BTF encoder, the loaders | producing the object the kernel receives | `encode_decode`, and loading |
| T1 and T2 | the source's safety and the existence of the run | stated; proofs in progress |
| Lean and its kernel | everything | as for every mechanization |

Not trusted: the compiler's passes, which are proved; the kernel
verifier, which remains the kernel's independent check and is not
relied on for safety; clang, which the C path uses and the theorem
never mentions.

## 11. Order of proof and effort

Definitions first, every theorem stated with `sorry` at the first
commit, then the proofs by fragment and by least dependence:

1. **Fragment 1**, the picker: scalars, `if`, counted loops, views,
   coercions, `array[1]` maps by direct access, verdicts. Prove D,
   then C, on this fragment; neither depends on typing. Then B, using
   Lemma W only.
2. **Fragment 2**: hash lookups, marked loads, `raise` and handlers,
   fallible kernel calls, `array[n]` by lookup. B gains the `try`
   cases and the dead branch; C the handler labels.
3. **Fragment 3**: `hold`, `move`, ring buffers, sockets. Lemmas M
   and H; the protocol part of the machine.
4. **Fragment 4**: functions and pass I.
5. `compile_correct` and the corollaries, by composition.

| piece | rough size in Lean lines |
|---|---|
| LIR syntax, semantics, interpreter, printer | 1400 |
| pass A, pass B with the ANF lowering, pass I | 1300 |
| target machine and BIR syntax, printer | 900 |
| pass C, pass D, encoding | 1100 |
| theorem statements and the shape checker | 300 |
| C printer | 400 |
| loader and BTF encoder, Python | 500 |

The proofs are a separate budget, on the order of the definitions
several times over, and Lemma L's semantic part is never proved.

## 12. Validation at every boundary

Each level has an executable form of its semantics, as Core has
`Interp.lean`, and the runner compares them on every corpus program:
`koitc run` on Core, `koitc run --lir` on LIR before and after
inlining, `koitc run --bir` on BIR, `koitc run --bytecode` on the
allocated program, each reporting verdict, maps, packet, and trace.
A difference between two adjacent levels localizes a bug to one pass
before any proof exists, and the `tests/run` expectations extend to
every level unchanged. The last comparison, bytecode against the
kernel under `BPF_PROG_TEST_RUN`, is the model's validation and
belongs to session 8.

## 13. Decisions this draft embeds

1. Five semantic passes and one encoding, with inlining its own pass
   on LIR so that flattening never sees a call.
2. Preservation is equality of the unique behavior per kernel, on the
   precondition that the checker accepted the unit.
3. `Agree` is equality of the shared state with the held stack read
   as rows and objects; per-pass relations add only locals and
   registers.
4. Pass B lowers impure expressions to administrative normal form in
   Core's evaluation order and pure ones directly.
5. Pass B uses Lemmas W, M, and H, and never T2; it emits every test
   Core has and only the dead branch of decision 48 beyond them.
6. The one memory injection is pass C's placement of LIR stack
   regions in the frame.
7. Pass D is the naive allocation, proved as a plus simulation; a
   validated allocator later.
8. Lemma L's syntactic part is a property of the translations and a
   runner check; its semantic part stays P9's conjecture.
9. Every level has an interpreter and the runner compares adjacent
   levels on the whole corpus.
10. Proofs by fragment, the picker first, passes D and C before B.
