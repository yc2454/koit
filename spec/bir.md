# BIR, the flat language, and the target machine

Status: draft 1, 2026-09-18; revised 2026-09-19 at the start of
session 7 from `ISSUES.md` entries 28 to 35, before the target code.
The second intermediate language and the machine the theorems are
stated against. In the code the instruction set is `Koit/BPF/`, one
`Instr` over a register type and a jump-target type; BIR and
bytecode are its two instances (entry 34). BIR is bytecode with names:
its registers are unbounded and its jumps go to labels. Bytecode is
BIR with eleven registers, the frame reached through `r10`, and label
offsets. Both run on the machine of section 2, which is eBPF with the
verifier's safety conditions as stuck states. `lir.md` defines the
language above; `lowering.md`, to come, the passes and the theorems.
The decisions embedded here are listed in section 10.

## 1. Role

Three things happen between closed LIR and the kernel, and BIR is the
middle one. LIR is structured; BIR is flat: labels and jumps, one
instruction per line, every operand a register or an immediate. BIR
has as many registers as it likes and names its frame objects;
bytecode has eleven registers and a frame of 512 bytes. So the
flattening pass, LIR to BIR, settles control and addressing; the
allocation pass, BIR to bytecode, settles registers and the frame;
encoding is the last and smallest step.

The machine both run on is the point of this document. Its values are
scalars or locations, never integers standing for addresses. A load
or store outside its region, through a stale packet location, or
from an uninitialized frame slot has no step. An unlock that does not
match the innermost lock, a call a held declaration forbids, or an exit while
anything is held has no step. These are the conditions the kernel
verifier checks, made into the machine's own rules.

For a program as submitted to the kernel this is the only semantics
there is. The kernel rewrites context accesses, patches division and
modulo, and resolves map references before an instruction runs, so a
concrete semantics of the submitted instructions does not exist apart
from those rewrites. The model takes the rewritten meaning as
primitive: a context field is an abstract value, a division by zero
yields zero, a map reference is a handle. The correspondence between
this model and the kernel is validated, not proved (section 9).

Two consequences. The correctness theorem of `lowering.md` says that
the bytecode's unique run from the loaded state halts with the
source's verdict and never reaches a stuck state; with T1 this is the
corollary of `language.md` section 20.2 with its compiler condition
discharged. And the machine is the definition of an unsafe access at
the bytecode level that `safety-claim.md` section 4 lists as missing,
in the terms Alivio builds its safety conditions, so the proof and
the per-program validation speak of one object.

## 2. The machine

### 2.1 Values

```
v ::= scalar n          a 64-bit pattern, n < 2^64
    | loc(r, off, tok)  a region, a signed offset, the token it was
                        made under
    | handle m          a map, made by `mapref` and accepted only as
                        the map argument of a builtin or a call
```

A register holds one value. Null is `scalar 0`. A handle is what the
kernel's `lddw` with the pseudo map source yields: it is not a
scalar and not a location, and any use of it other than as a map
argument is stuck (entry 29). It exists so that one BIR call is one
bytecode call. A location's offset
may leave its region between the arithmetic that moves it and the
access that uses it; only the access is checked. The token matters
for the packet region only and is compared at every access.

### 2.2 Memory

The machine's memory, the part every level addresses alike, is three
regions: map slots, the packet, and kernel objects. Each level adds
its own: Core its numbered struct literals, BIR and bytecode the
frame and the context. A location over a shared region means the
same bytes at every level; a location over a level's own region
exists at that level only (`ISSUES.md`, entry 30). The declarations:

| region | size | contents | made by |
|---|---|---|---|
| `map(m, i)` | the value size of `m` | bytes | `lookup`, `mapval` |
| `pkt` | the packet's current length | bytes, guarded by the token | `data`, `data_end` |
| `kernel(id)` | the object's size | bytes | acquiring declarations |
| `frame` | 512 bytes as 64 slots of 8 | slots, below | `r10`, `lea` |
| `ctx` | the kind's context declaration | abstract fields | `r1` at entry |

Bytes are little-endian. A scalar load of `w` bits reads `w / 8`
bytes and zero-extends; a store writes them.

**The frame** is 64 slots of 8 bytes at offsets `-512` to `-1` from
its top. A slot is `spilled v`, one value, or `bytes b_0 .. b_7`,
each byte initialized or not. The rules are the verifier's:

- a store of a location or a handle is admitted only as 8 bytes at
  a slot boundary, and makes the slot `spilled`; anywhere else it is
  stuck,
  which is the rule that a pointer never leaks into a map, the
  packet, or a misaligned slot;
- a store of a scalar makes bytes, and unspills the slot it touches;
- a load of 8 bytes at a spilled slot yields the value;
- a load of bytes requires every byte read to be initialized and
  none to belong to a spilled slot;
- the frame starts with every byte uninitialized.

**The context** is a set of fields per kind, declared by the kernel
interface: for
each field its name, its type, its offset in bytes, and whether it
is writable; the width is the type's. Every declaration is readable, since a
field the source may not read is not a declaration, and a load or store at
an offset and size that is not a declaration is stuck, which is the
verifier's context-access check; the lowering never emits one,
because context access goes through the kind declaration. The offset is the
kernel's layout and reaches no developer-facing surface (entry 31).
Two declarations of a packet kind yield locations rather than scalars:
`data` yields `loc(pkt, 0, tok)` and `data_end` yields
`loc(pkt, len, tok)` with the current token, which is the kernel's
conversion of those fields made primitive.

### 2.3 Maps and rings

The map operations are builtins with fixed semantics, the ones
`Koit/Machine/Ops.lean` gives them and every level calls, and do not
consult the kernel parameter:

| builtin | arguments | meaning |
|---|---|---|
| `lookup` | the map's handle, the key's location | an array kind: `loc(map(m, k), 0)` when `k` is below the capacity, else null; a hash kind: the entry's location or null; per-CPU arrays as arrays |
| `update` | the handle, the key's and the value's locations | insert or replace; a full hash map answers with the negative `E2BIG` |
| `delete` | the handle, the key's location | remove, or the negative `ENOENT` |
| `mapval m + k` | none | `loc(map(m, 0), k)` for an `array[1]` map: direct value access |
| `reserve n` | the ring's handle | a fresh kernel object of `n` bytes, held as a record, or null when the ring is full |
| `submit`, `discard` | the record | pop it; `submit` appends it to the ring |
| `lock`, `unlock` | the lock field's location in a map value | push, pop |
| `enter R`, `leave R` | none | push, pop, for the scope declarations |
| `copy n`, `fill n` | locations, a byte | byte moves, expanded by the flattening |
| `printk fmt n` | `n` scalars; the format is on the instruction, and in bytecode the location in the read-only data and the size holding its bytes, filled at the call site by the flattening (entry 37) | an event on the trace with the format and the scalars |
| `tail m` | the context, the array `m`, and the index; a taken call replaces the program, and the machine runs the entry's body with one counter of 33 per invocation; not taken, the next instruction runs (decision 67) | the callee's trace and verdict, or nothing |
| `atomic op(w)` | a location, one or two scalars | the read-modify-write of section 8.5, at 32 or 64 bits |

A key or value argument may lie in any readable region, and its
bytes must be initialized. The lock argument must be the slot-typed
field of the value it lies in, which the map's declaration fixes.

### 2.4 The kernel parameter

Every other declaration of the interface's calls is a kernel function or
an inline declaration. Its implementation clause says which: a helper by
its number in the uapi header, a kfunc by name, each with the layout of
the kernel's arguments, or `inline`. A layout is the kernel's argument
positions, each one of: koit's `i`-th argument, the context, a constant,
the byte size of koit's `i`-th argument's place, or `printk`'s format;
`bpf_sk_lookup_tcp`'s is `(ctx, arg 0, size 0, -1, 0)`, the current
netns and no flags. A declaration whose helper differs by kind, the
resizes in `xdp` and `tc`, carries an override per kind. Stage 1
transcribes the clause from the uapi header; session 8's generator
produces it (entry 38).

For a kernel function the machine consults the same `Kernel` as
Core: `K.helper declaration args st` answers with a value and a state, or a
failure with its negative return, and `KernelOk` is the same
contract. The arguments `args` are koit's: in BIR they are the
call's operands; in bytecode the machine reads `r1` to `r5` by the
declaration's layout, koit's arguments from their positions and the context
where the layout says, and is stuck when the register at a context
position is not the context or a constant position does not hold
its constant. The trace therefore records koit's arguments at every
level. The machine fits the arguments to the declaration's parameter kinds
before the call: a scalar parameter of width `w` takes a scalar
reduced to `w`, a memory parameter takes a location whose region is
one the declaration's region clause admits, and anything else is stuck,
which is the verifier's argument-type check. Afterwards:

| the kernel answers | `r0` |
|---|---|
| a value `v` | `v` |
| no value | `scalar 0` |
| failure `n`, a declaration whose result is a scalar | `n` as a 64-bit two's complement pattern |
| failure, a declaration whose result is a location | `scalar 0` |

This convention is a rule, derived from the declaration's result type,
not a clause; a declaration that needs an exception gets a clause then.
A declaration that acquires pushes its result on the held stack; a
declaration that releases pops the entry whose object is its argument
and is stuck otherwise. A declaration with the `resize` effect may
change the packet and its token, as `KernelOk` allows and nothing else
may. A call while a held declaration forbids `call` is stuck, except the
declaration's own release. Every call appends an event to the trace.

An inline declaration, `pkt.len`, `csum_add`, `csum_fold`, is what the
kernel computes without a call: the packet's length, the 32-bit add
with end-around carry, the two folds and the complement. The machine
computes it as one function of the arguments and the state at every
level, Core included, without the kernel parameter and without a
trace event, since the kernel makes no call; the trace lists the
calls the kernel sees and every level still agrees on it. Pass D
expands each into the kernel's own instruction sequence, and a lemma
of pass D says the sequence computes the function (entry 38).

### 2.5 Protocol state and the trace

The held stack is a list of entries `(declaration, object)`, innermost
first, pushed and popped by the builtins and declarations above. The object
is described without a location of any level: a lock by its map slot
and offset, a record or a socket by its kernel object. The packet
token is a counter changed only by declarations with `resize`. The trace is
a list of events:

```
ev ::= call decl [a_i] (ok v? | failed n) | print fmt [v_i]
a   ::= a scalar | the bytes a memory argument pointed at
```

A memory argument is recorded as the bytes the kernel received,
sized by the declaration's parameter kind, never as a location, since the
kernel observes bytes and the levels name regions differently. Both
the stack and the trace are part of the shared state, so Core's run
and the machine's append the same events in the same order, and the
theorem asks for equality of traces (`ISSUES.md`, entries 24 and
30).

### 2.6 Machine states, loading, halting

```
m ::= (pc, R, st)
```

`pc` indexes the code, `R` maps registers to values or marks them
uninitialized, and `st` is the shared state. The loaded state of a
program `p` from Core's initial state `st` is:

- `r1 = loc(ctx, 0, tok)`, `r10 = loc(frame, 0, tok)`, every other
  register uninitialized; in BIR the same with `v_ctx` and `v_fp`;
- the frame uninitialized; the maps, packet, and context as in `st`;
- the held stack empty, the trace empty, `pc = 0`.

A state is halted when its instruction is `exit`, `r0` is a scalar,
and the held stack is empty; its value is `r0` fitted to the kind's
verdict width. A state with no successor that is not halted is
stuck; section 5.3 lists the causes.

## 3. Instructions

The set is the part of the kernel's instruction set the templates
need, cpu v3, with the v4 additions marked. It is one syntax over two
parameters, the register type and the jump-target type: registers
are `v_i` and targets labels in BIR, `r0` to `r10` and signed
offsets in bytecode, and the two differ in nothing else but the
conventions of section 7 (entry 34). `cls` is the operation class,
64 or 32 bits, which is the kernel's ALU and ALU32, JMP and JMP32
distinction; `w` is an access or extension width.

```
alu(op, cls) d s          op in {add sub mul div mod and or xor lsh rsh arsh}
alu_imm(op, cls) d k
sdiv, smod                v4: alu with the signed variant of div, mod
mov(cls) d s
mov_imm(cls) d k
movsx(cls, w) d s         v4: sign-extending move from w in {8, 16, 32}
end(to, w) d              byte order: to in {be, le}, w in {16, 32, 64}
ldx(w) d [s + off]        w in {8, 16, 32, 64}
stx(w) [d + off] s
st(w) [d + off] k
ja L                      v4 adds the long form
jcond(cmp, cls) a b L     cmp in {eq ne gt ge lt le sgt sge slt sle set}
jcond_imm(cmp, cls) a k L
lddw d k64
lea d obj                 BIR only: the frame object's location
mapref d m                the map's handle, `handle m`
mapval d m k              direct value access
call h                    BIR: call h (s_1 .. s_5) -> d, koit's operands;
                          bytecode: r1..r5 by the declaration's layout -> r0
atomic(op, cls, fetch) [d + off] s     op in {add and or xor xchg cmpxchg}
exit
```

Meaning, by class of instruction:

- **ALU on scalars.** The operation of section 8.1 on the operands'
  patterns at `cls` bits, the result written at `cls` bits and, for
  32, zero-extended into the register. Division and modulo by zero
  yield zero and the dividend; the shift amount is masked to `cls -
  1`; `arsh` is arithmetic. This is what the kernel's fixups and
  JITs implement.
- **ALU on locations.** `add` and `sub` of a scalar to a location
  move its offset; `sub` of two locations of one region yields their
  offset difference as a scalar; `mov` copies a location. Every
  other operation on a location is stuck.
- **Loads and stores.** The base must be a location; the effective
  location is the base moved by `off`; the access is admitted by the
  region's rules of section 2.2 and by the token for the packet.
- **Jumps.** Two scalars compare at `cls` bits, signed for the `s`
  forms; two locations of one region compare by offset, and a
  location compares with the immediate zero under `eq` and `ne`;
  anything else is stuck.
- **`lddw`, `mapref`, `mapval`, `lea`.** Constants and handles.
  `mapref` yields a value only a builtin or a declaration with a map
  parameter accepts.
- **`call h`.** The builtin or kernel function of section 2.3 or
  2.4, with arguments in `r1` to `r5` and the result in `r0`; `r1` to
  `r5` are uninitialized after the call, `r6` to `r9` unchanged. In
  BIR the operands are explicit and nothing is clobbered.
- **`atomic`.** The read-modify-write at 32 or 64 bits on a location
  into a map value or the frame; with `fetch`, the previous value
  replaces the source register, and `cmpxchg` uses `r0` as the
  kernel does.
- **`exit`.** Halts as section 2.6 says, or is stuck.

What `call h` encodes to is the declaration's implementation clause of 2.4:
a helper's number in the immediate; a kfunc's BTF id, which the
encoder leaves as a relocation by name in the form clang leaves in an
object, a pseudo call with an immediate of -1, for the loader to
resolve as libbpf does;
and for an inline declaration no call at all but the expansion pass D makes.
The scope declarations' `enter` and `leave` are kfunc calls by the resource
declaration's kernel names; no stage-1 program uses one.

## 4. Widths in registers

Registers are 64 bits and the source has four widths and two
signednesses. The invariant that relates a local of type `int(s,w)`
to the register that holds it is the 32-bit normal form:

| type | register pattern |
|---|---|
| `int(s,64)` | the 64-bit pattern of the value |
| `int(s,32)` | the 32-bit pattern, zero-extended |
| `int(u,8)`, `int(u,16)` | the `w`-bit pattern, zero-extended |
| `int(i,8)`, `int(i,16)` | the `w`-bit pattern sign-extended to 32 bits, then zero-extended |

Under the invariant every operation is one instruction at `cls`
chosen by the width, followed for the narrow widths by a
normalization: `and_imm(32) d mask_w` for unsigned, and
`movsx(32, w)` or the pair `lsh_imm(32) d (32 - w); arsh_imm(32) d
(32 - w)` for signed. Comparisons need no normalization: unsigned
narrow values compare as 32-bit unsigned, signed narrow values as
32-bit signed. Two operations need more than the normalization:

- a narrow shift masks its amount to `w - 1` first, since the
  instruction masks to 31 and section 8.1 masks to `w - 1`;
- signed division and modulo are `sdiv` and `smod` on v4; below v4
  they need a sequence around the unsigned instructions that fixes
  the signs and the two special cases of section 8.1, which is not
  yet written, so under `--cpu v3` the compiler reports them as a
  construct the target lacks (entry 32).

The casts of section 8.1 are the table below, which is the shape
obligation L2 of `lowering.md` section 8 made concrete: every cast is
one of the instructions the verifier tracks exactly.

| from | to | instructions |
|---|---|---|
| any width | 64, from an unsigned source | none |
| 32 or narrow signed | 64 | `movsx(64, 32)`, or `lsh 32; arsh 32` |
| 64 | 32 | `mov(32) d s` |
| narrow | 32 | none |
| any | 16 or 8 unsigned | `and_imm(32) d mask_w` |
| any | 16 or 8 signed | `movsx(32, w)`, or the shift pair at 32 |
| `int(u,w)` | `int(i,w)`, `w` narrow | `movsx(32, w)`, or the shift pair |
| `int(i,w)` | `int(u,w)`, `w` narrow | `and_imm(32) d mask_w` |
| same width, 32 or 64 | the other signedness | none |
| `bool` | any | none, or the mask |

Byte order: `end(be, w)` is the swap on this little-endian machine,
zero-extending for 16 and 32, and is what `bswap(w)` of LIR becomes.

## 5. The step relation

### 5.1 Form

`Step K : m -> m' | refused c` is a total function of `m` for each
kernel `K`, so the machine is deterministic per kernel; `c` is the
cause of the refusal, one constructor per item of 5.3 carrying the
data that identifies the instance, and a step on a halted state is
refused with the cause "halted". `Star (Step K)` is the reflexive
transitive closure of the successful steps. A run is the sequence
from the loaded state to a halted state. `Stuck m` is "not halted
and refused", so the theorems speak of the predicate and the runner
prints the cause (entry 33).

### 5.2 Selected rules

```
(Alu)
    code[pc] = alu(op, cls) d s     R d = scalar a     R s = scalar b
    ---------------------------------------------------------------
    (pc, R, st) -> (pc + 1, R[d := norm_cls(op(a, b))], st)

(Alu-loc)
    code[pc] = alu(add, 64) d s     R d = loc(r, o, t)     R s = scalar b
    ---------------------------------------------------------------------
    (pc, R, st) -> (pc + 1, R[d := loc(r, o + signed(b), t)], st)

(Ldx)
    code[pc] = ldx(w) d [s + off]     R s = loc(r, o, t)
    the access of w bits at loc(r, o + off, t) is admitted in st
    ---------------------------------------------------------------
    (pc, R, st) -> (pc + 1, R[d := the value read], st)

(Stx)
    code[pc] = stx(w) [d + off] s     R d = loc(r, o, t)     R s = v
    the store of v at w bits at loc(r, o + off, t) is admitted in st
    ---------------------------------------------------------------
    (pc, R, st) -> (pc + 1, R, st[the bytes or the slot written])

(Jcond)
    code[pc] = jcond(cmp, cls) a b L     R a, R b comparable under cmp
    -------------------------------------------------------------------
    (pc, R, st) -> (if cmp holds then L else pc + 1, R, st)

(Call-kernel)
    code[pc] = call h     h a kernel declaration
    [v_i] = koit's arguments, read by the declaration's layout in bytecode
    the arguments fit the declaration
    no held resource forbids call, or h releases that resource
    K.helper h [v_i] st = ok v st'
    ---------------------------------------------------------------
    (pc, R, st) -> (pc + 1, R[r0 := r0(v), r1..r5 := uninit],
                    st'[trace += ev, held pushed or popped per the declaration])
    and with failed n st', r0 := signal(h, n)

(Call-builtin)
    code[pc] = call b     b a builtin     the arguments fit
    ---------------------------------------------------------------
    (pc, R, st) -> (pc + 1, R[r0 := the builtin's answer, r1..r5 := uninit],
                    st[the builtin's effect])

(Call-inline)
    code[pc] = call h     h an inline declaration     inline(h, [v_i], st) = v
    ---------------------------------------------------------------
    (pc, R, st) -> (pc + 1, R[r0 := v, r1..r5 := uninit], st)

(Exit)
    code[pc] = exit     R r0 = scalar v     held(st) = []
    -------------------------------------------------------
    (pc, R, st) is halted with v fitted to the verdict width
```

### 5.3 Stuck states

A state that is not halted and has no successor is stuck. The causes
are exactly these, and each is a check the verifier makes:

1. an access outside its region, or of a width that crosses its end;
2. an access through a packet location whose token is not current;
3. a read of an uninitialized register or frame byte, or a byte read
   of a spilled slot;
4. a store of a location anywhere but an aligned frame slot;
5. an ALU operation on a location other than the two of section 3;
6. a comparison of a location with a scalar other than the immediate
   zero, or of locations of different regions;
7. a context access that is not a field of the kind's context, or a
   write to a read-only declaration;
8. a call whose argument does not fit its parameter kind, a handle
   used other than as a map argument, or a call while a held declaration
   forbids it;
9. a release whose argument is not the innermost held object, or a
   lock acquired while a lock is held;
10. an exit while the held stack is not empty, or with `r0` not a
    scalar;
11. a `pc` outside the code, or a jump to one.

Division by zero, overflow, and shifts by any amount are not causes;
they are total. The list is the model's whole trusted content: it
says what the kernel refuses, and `lowering.md`'s theorem says the
lowering never produces a run that reaches any of it.

## 6. BIR

A BIR program is one flat program per koit program, produced from
closed LIR: a list of frame objects with sizes and alignments, a
list of virtual registers with a class each, scalar, location, or
handle, and an instruction array with labels. The class is metadata
for the allocation pass, not part of the instruction. The flattening
reuses registers by LIR's block structure: a temporary made for an
intermediate value is free again at the end of its statement, and
two locals whose scopes are disjoint share a register, so the count
is bounded by the locals in scope at once plus the temporaries of
one statement, and the naive allocation of section 7 fits the corpus
in the frame (entry 28). Well-formedness:

- every register is written before it is read on every path, which
  the flattening guarantees from LIR's `let` discipline;
- every label is defined once and every jump targets a label;
- `v_ctx` holds the context location from entry to exit and `v_fp`
  the frame's, both read-only;
- `lea d obj` names a declared object; the flattening assigns each
  object its frame offset, packed from the top at 8-byte alignment,
  and the allocation pass places spill slots below them; the sum
  must fit in the frame or the program is rejected with its frame
  size, decision 22;
- a raise site is `mov v_reason, e; ja handler_k`, and the handler's
  code follows the body at `handler_k`, reading `v_reason` as its
  `reason`; the held-stack check of LIR's program rule is the
  `exit` rule here, since the releases ran before the jump.

The semantics of BIR is the machine of section 2 with `R` over
virtual registers and no clobbering at calls. There is no separate
BIR semantics to write: one `Step` over the one instruction syntax,
parameterized by the convention, explicit call operands and `lea`
admitted for BIR, the fixed five and clobbering for bytecode; the
two are instances, and `alloc_correct` relates two instances of one
function (entry 34).

## 7. Bytecode

Bytecode is BIR with these choices made:

**Registers and the frame.** `r10` is the frame pointer, read-only;
`r1` holds the context at entry and is copied to `r6` or spilled
before the first call; `r1` to `r5` carry a call's arguments and are
dead after it; `r0` is its result; `r6` to `r9` survive calls. The
first allocation is naive: every virtual register lives in a spill
slot below the frame objects, and each BIR instruction becomes loads
of its operands into `r1` to `r3`, the instruction, and a store of
the result. It is provable directly and it is what the verifier sees
from clang at low optimization, so it is accepted. A linear-scan
allocation over `r6` to `r9` comes later as an untrusted pass with a
verified checker, the way CompCert validates its own.

**Kernel calls.** A call's registers are laid out as the declaration's
implementation clause says: koit's arguments at their positions,
the context from `r6`, constants and sizes as immediates, `printk`'s
format as its location in the read-only data and its size. An inline declaration
becomes the kernel's own sequence: `data_end - data` for `pkt.len`,
the add with a carry test and increment for `csum_add`, the two
folds and the complement for `csum_fold` (entry 38).

**Formats.** Each `printk` format, its holes converted to the
kernel's conversions by the arguments' types, lives in the unit's
read-only data, one map per unit holding every format's bytes; the
call passes `mapval` at the format's offset and its size. The
machine's trace event, the format and the scalars, does not see
where the bytes live (entries 37 and 52).

**Labels.** Jump targets become signed instruction offsets; the long
jump of v4 is used when an offset exceeds 16 bits, and under v3 such
a program is rejected.

**CPU version.** `--cpu v3|v4` selects, v3 the default, recorded in
the object; v3 stands the shift pair in for `movsx` and `end` for
`bswap`, and rejects signed division and modulo (entry 32).

**Encoding.** One 64-bit word per instruction, `opcode:8 dst:4 src:4
off:16 imm:32`, two words for `lddw`, with the opcode tables of the
kernel's `Documentation/bpf/standardization/instruction-set.rst`.
Map references are `lddw` with the pseudo source register the
loader recognizes, `BPF_PSEUDO_MAP_FD` for `mapref` and
`BPF_PSEUDO_MAP_VALUE` for `mapval`, and a relocation naming the
map. Since a handle is a value and the map is an operand of the
call, one BIR call is one bytecode call and the encoder is a word
layout. The object it produces is the words, the relocation list,
map file descriptors, map values, and kfuncs by name, and a note per
call naming the callee the model sees, since the words alone do not
say which builtin a helper number stands for once its size and flags
are in registers; the notes are not loaded. The decode-encode round
trip on the object is the one property of the encoder worth proving,
and LLVM's BPF disassembler and assembler on the words and the
printed bytecode are its independent check until a kernel is
available, when the tool is present (entries 29, 35, 38).

**Loading.** Two loaders serve two purposes. The first is a few
hundred lines over the `bpf` system call: create the maps, with BTF
for a value that holds a spin lock, patch the map file descriptors
into the relocations, load each program with the kind declaration's program
type, and attach; it is the fast path to acceptance numbers and needs
no ELF. The second writes the ELF object libbpf expects, with
`.maps` and `.BTF`, so that a koit object loads through the stock
toolchain; it is the path the paper's toolchain claim needs. Both are
kernel-facing tooling in the sense of the plan's decision table:
untrusted, no theorem.

**BTF.** A map value with a slot field needs BTF for the kernel to
find the lock, and the encoder must produce integers, arrays, and
structs, and the struct named `bpf_spin_lock`. Programs need BTF
only for kfunc calls and for line information, both later.

**Sections and types.** From the kind declaration: the section name for
ELF, the program type and expected attach type for the system call,
the license from the unit.

## 8. What the verifier must re-derive

Acceptance is not part of the machine; it is Claim A of
`proof-structure.md`, under the hypothesis H2 that the verifier
re-derives the checker's facts, and the shape obligations of
`lowering.md` section 8 are where the machine and that hypothesis
meet. Stated on the templates of sections 3 and 4:

- Every fact the checker used is a comparison on the path, because
  every LIR `if` is a `jcond` and the lowering emits a test wherever
  Core had a marker. Configuration constants are immediates.
- Every cast is an instruction of the table in section 4.
- The register an access indexes with is the register the comparison
  tested. Under the naive allocation the value passes through a
  spill slot between the test and the use, and the verifier carries
  bounds through 8-byte spills and links the slot to the register it
  was loaded into, on the kernels the plan targets; the measurement
  of E6 decides whether the first allocation must keep the tested
  value in a register until its last use.
- A packet location's variable offset stays below the kernel's
  maximum packet offset because the view rule's obligation bounds it
  (`ISSUES.md`, entry 21), so the pointer arithmetic that carves a
  view is accepted and the comparison that follows sets the range.
- Frame objects are 8-aligned and every access through them has the
  natural alignment of its type; map values are 8-aligned by the
  kernel; packet fields are at their natural offsets from `data`,
  which the architectures the plan targets accept.
- The naive allocation multiplies instruction counts by a small
  constant, which the budgets of section 20's non-claims absorb for
  the corpus; the counted loops carry their bound in a register the
  verifier tracks, and a `for` loop's bound is a constant or a value
  with a fact on the path.

## 9. Validation against the kernel

The machine is a model, and three checks tie it to the kernel, none
of them a proof:

1. **Differential runs.** `koitc run --bytecode` executes the machine
   on the emitted program and compares its verdict, maps, packet, and
   trace with `koitc run` on Core; then the same program under
   `BPF_PROG_TEST_RUN` in a VM, with the same inputs, compared on
   verdict, packet, and maps.
2. **Instruction-level replay.** Yuan et al.'s mechanized in-kernel
   semantics replays a program's registers against the kernel's
   interpreter instruction by instruction; the same replay against
   this machine's trace of register values checks the ALU, jump, and
   memory rules on the instructions the templates emit.
3. **The verifier's own answer.** A program the machine runs without
   a stuck state should load; a rejection names either a re-derivation
   the templates failed to make visible, a shape obligation's
   business (`lowering.md` 8) or a failure of H2,
   or a rule of the verifier the list of 5.3 lacks, which is a bug in
   the model and is added to the list.

A formal bridge from this machine to the concrete in-kernel model,
a memory injection from locations to addresses, is possible later
and is not needed for the paper.

## 10. Decisions this draft embeds

1. One machine for BIR and bytecode, and the same shared state as
   Core: maps, packet, token, kernel objects, held stack, trace. The
   shared state is one definition containing no location of any
   level, embedded by every level's state; each level extends the
   shared regions with its own; the builtins, the kernel call, and
   the protocol are one implementation every level calls (entry 30).
2. Values are scalars, locations, or map handles; null is the
   scalar zero; pointers never become integers; a handle is only ever
   a map argument and spills like a location (entry 29).
3. The verifier's safety conditions are the stuck states, listed in
   5.3, and the list is the model's trusted content; `Step` names the
   cause it refuses for, one constructor per item (entry 33).
4. Context fields are abstract, declarations of name, type, offset, and
   writability per kind whose offsets no developer sees; `data` and
   `data_end` yield packet locations; division and shifts are total
   as the kernel patches them (entry 31).
5. Map operations are builtins with Core's semantics; every other
   declaration goes through the kernel parameter, with the return convention
   of 2.4 derived from the declaration's result type.
6. The frame is 64 slots with the verifier's spill rules, and starts
   uninitialized.
7. The 32-bit normal form of section 4 and its cast table realize
   the shape obligation L2 (`lowering.md` 8).
8. cpu v3 is the default, `--cpu v4` selects v4's `movsx`, `sdiv`,
   `smod`, `bswap`, and long jump; signed division below v4 is
   rejected until its sequence is written (entry 32).
9. The first allocation is naive and provable, and the flattening
   reuses virtual registers by block structure so that it fits
   (entry 28); a validated allocator comes later.
10. Two loaders, system call first, ELF and BTF second; both
    untrusted.
11. The model is validated by differential runs, instruction replay,
    and the verifier's own verdicts, and a rejection that 5.3 does not
    predict is a model bug. Until the ELF writer and a kernel exist,
    the Lean interpreter checks the passes and the disassembler
    checks the encoder; neither checks the model (entry 35).
12. One instruction syntax over a register type and a jump-target
    type, one `Step` parameterized by the calling convention; BIR and
    bytecode are its instances (entry 34).
13. `printk`'s format is metadata on the instruction at every level;
    the direct backend places its bytes in the unit's read-only data
    and passes their location (entries 37 and 52).
14. A call declaration's implementation clause carries the kernel's
    calling convention, a helper number or kfunc name with the
    layout of its arguments relative to koit's; the bytecode
    instance reads koit's arguments back by it, so the trace is the
    same at every level. The inline declarations are one function of the
    machine at every level, untraced, and pass D expands them; the
    object is words, relocations, and notes (entry 38).
