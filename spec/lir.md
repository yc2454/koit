# LIR, the explicit intermediate language

Status: draft 1, 2026-09-18, written at the start of session 6 after
the decision to make a direct backend to eBPF bytecode the
theorem-bearing path and to keep C as a printer. LIR is the first of
two intermediate languages. `bir.md` defines the second and the
target machine both are measured against; `lowering.md`, to be
written next, defines the passes between Core, LIR, BIR, and bytecode
and states their theorems. The decisions this draft embeds are listed
in section 9, so that they can be disputed line by line. The gaps in
`language.md` it found are entries 21 to 24 of `ISSUES.md`.

## 1. Role

LIR is Core after the checker, with the facts spent. Two properties
of the lowering are visible in its syntax and nowhere else:

- Every runtime test is an `if` on a comparison, and there is one
  exactly where the source had a marker: a view carve, a hash lookup,
  a marked load, a coercion, a fallible call. An obligation the checker
  discharged has no test, because Core never had one; elision is a
  fact about the source, established by T1 and T2, not a decision of
  the compiler. The one exception is a branch the verifier requires on
  a path the kernel's contract makes unreachable (section 6.4).
- Every failure, acquisition, and release is a statement. A failure
  carries its kind and reason in an outcome that the enclosing call
  or the program catches; the releases it owes are statements before
  it, at the site. Nothing happens in a rule that did not happen in a
  statement.

Two consumers read LIR. The C printer prints each construct as one C
construct, which gives the readable artifact and the way through the
stock toolchain (section 8). The flattening pass turns LIR into BIR,
which is the way to bytecode and the path the theorems follow.

LIR keeps structured control, local names, functions, maps, and the
builtins and kernel functions of the interface's calls. It drops refinement
types for widths, fallible operations for tests, `hold` for acquire
and release statements, `move`, which emits nothing, `for` for a
tested loop, and every constant of sections 8.4 and 15 for its value.
It decides nothing about registers, frame offsets, or instructions;
those are BIR's.

LIR programs come in two forms. Core lowers to LIR with functions,
one per Core function, so that the lowering and its proof are per
function. An inlining pass, LIR to LIR, removes the functions
(section 6.6); BIR is produced from closed LIR only.

## 2. Values, widths, and locations

LIR values are Core's, minus polymorphic literals: a fixed-width
integer reduced to its type's range, or a location. A boolean is the
integer 0 or 1 at width 8. Every literal carries its width, so an
expression has one static type, and the dynamic meeting of widths of
section 19.1 does not occur. Arithmetic is the total function of
section 8.1, the same `arith` as Core's, applied at the annotated
width and signedness.

A location is a region, an offset, and the packet's layout token at
the time the location was made. The regions are Core's: a map slot,
the packet, a stack object, a kernel object. A location into the
packet is usable only while its token is the current one, and any
statement with the `resize` effect changes the token. This is the
target machine's rule too (`bir.md`, section 2), and it is what
Core's binding-token check in the rule (PGuard) becomes once the
token travels with the value (`ISSUES.md`, entry 24).

There is no null value. A builtin or a kernel function that may
answer with no location answers with the scalar zero, and the test
the lowering emits compares the result with zero. A comparison
between a location and the literal zero is allowed; between a
location and any other scalar, or between locations of different
regions, it is an error.

Byte-order values are their stored bit pattern. `hton` of a constant
folds to the swapped constant, `ntoh` is a byte swap, and a `be`
field is loaded and stored like any integer of its width. Memory is
little-endian (entry 24).

## 3. Syntax

```
widths        w ::= 8 | 16 | 32 | 64
signedness    s ::= u | i
types         T ::= int(s,w) | ptr
literals      k ::= an integer constant

expressions   e ::= k(w) | x | e op(s,w) e | cast(s,w -> s',w') e
                  | bswap(w) e | load(w) a | ctx f | a
addresses     a ::= x | a + k | a + e * k
                  | pkt_data | pkt_end | mapval m + k
conditions    c ::= e cmp(s,w) e
operators    op ::= + | - | * | / | % | & | '|' | ^ | << | >>
             cmp ::= == | != | < | <= | > | >=

statements    s ::= skip | s ; s
                  | let x : T = e | x := e
                  | store(w) a e | ctx f <- e
                  | frame x : n [as S]
                  | if c s s
                  | block s | loop s | br n
                  | return e?
                  | raise k e
                  | [x =] call f(arg, ...) [unwind s] [absent s]
                  | [x =] b(arg, ...)              a builtin
                  | [x =] h(arg, ...)              a kernel function
arguments   arg ::= e
builtins      b ::= lookup m | update m | delete m
                  | reserve m n | submit | discard
                  | lock | unlock | enter R | leave R
                  | copy n | fill n | printk "fmt"
                  | atomic op(s,w) [fetch]

functions     F ::= fn f (x : T, ...) [-> T [?]] [fails] { s }
handlers      H ::= on k => s
programs      P ::= program p : kind { s } H^6
units         U ::= map* F* P*
```

Reading notes.

- `k(w)` is the literal `k` at width `w`; a literal is never wider
  than its context.
- `op(s,w)` applies the operator at width `w`; `s` matters for `/`,
  `%`, `>>`, and the comparisons, and is carried on every operator so
  that the printer and the flattening never consult a type.
- `cast(s,w -> s',w')` is the conversion of section 8.1: truncation,
  zero extension from unsigned, sign extension from signed.
- `load(w) a` reads `w` bits at the address; `store(w) a e` writes
  them. There is no load or store of an aggregate; `copy n` and
  `fill n` move `n` bytes.
- `ctx f` reads the context field `f` at the width of its declaration, and
  `ctx f <- e` stores to a field the declaration marks writable, `mark` in a
  `tc` program. `pkt_data` and `pkt_end` are the packet's bounds as
  locations, read from the context each time they are mentioned; they
  exist in packet kinds, and in a function only for the element test
  of 6.4 on a view parameter, which the checker's typing of views
  confines to callers of packet kinds (entry 39).
- `mapval m + k` is the location `k` bytes into the value of a map
  that pass A marked for direct access: an `array[1]` map. Every
  other map is reached through `lookup`.
- `frame x : n` allocates `n` bytes of zeroed stack, aligned to 8, and
  binds `x` to its location; `as S` names the source struct type, for
  the printer only.
- `block s` runs `s`; `br n` leaves `n + 1` enclosing `block` or
  `loop` constructs, counting from the innermost; a `br` that reaches
  a `loop` restarts it, one that reaches a `block` leaves it.
- `return e` leaves the function or program with `e`; `return` with
  no value leaves a function declared `-> T ?` with absence, or a
  function without a result early.
- `raise k e` leaves with the failure kind `k` and the reason `e`,
  an `int(u,32)`. The releases owed at the site precede it.
- `call f(...)`: `unwind s` runs when `f` raises, before the failure
  continues outward; it holds the releases the call site owes.
  `absent s` runs when a `-> T ?` function returns without a value;
  its outcome is the call's.
- A builtin or kernel function is called by the name of its declaration. A
  fallible kernel function answers with the value the declaration's
  convention gives on failure, a negative number or the scalar zero
  (`bir.md`, section 2.5), and the lowering tests it. The result of a
  kernel function is bound at `int(i,64)` when the declaration yields a
  scalar or nothing, and at `ptr` when it yields a location; the
  lowering casts a scalar result to the declaration's type after the test. A
  declaration with no effects, `pkt.len`, is a kernel function all the same,
  so that the trace lists it at every level.
- `atomic op(s,w)` carries the signedness of the place, which the
  previous value it yields has.
- `on k => s` is the handler of kind `k`; the six are present after
  defaults. Its body sees the local `reason`.

## 4. Well-formedness

LIR has no typing judgment with facts; it has a well-formedness
check that the lowering satisfies by construction and that the
flattening assumes.

- Each `let x` in a function declares `x` once; every other mention
  is a use or an assignment. A use on a path with no earlier `let`
  reads an unbound local, which is an error of the semantics; Core's
  definite initialization keeps it unreachable.
- `x : int(s,w)` is used at that width and signedness; both operands
  of `op(s,w)` and `cmp(s,w)` have type `int(s,w)`; `cast` accepts
  any integer type; `bswap(w)` applies to `int(u,w)`; `load(w)` and
  `store(w)` take a `ptr`; the value stored has width `w`.
- An address is a `ptr` local, a `ptr` plus a constant, a `ptr` plus
  a scalar times a constant, `pkt_data`, `pkt_end`, or `mapval`.
- A condition compares two scalars of one type, two addresses, or an
  address with `0(64)` under `==` or `!=`.
- `br n` occurs inside at least `n + 1` enclosing `block` or `loop`.
- `return e` has the function's result type, or the kind's verdict
  width in a program; a bare `return` occurs only in a `-> T ?`
  function.
- `raise k e` occurs only in a `fails` function or a program body,
  never in a handler; `e : int(u,32)`.
- A call matches the callee's signature; `unwind` is present exactly
  when the callee is `fails`; `absent` exactly when it is `-> T ?`.
  An `unwind` body contains only release builtins and release declarations.
- A function neither acquires nor releases across its boundary: the
  held stack at its return is the one at its entry, which the
  semantics checks.
- A handler ends in `return` on every path and contains no `raise`,
  no `unwind`, and no call to a `fails` function. A packet program's
  body ends in `return` on every path.

## 5. Dynamic semantics

LIR runs on the machine of `bir.md`, section 2, restricted to what a
structured language needs: the shared state of Core, whose maps,
packet, kernel objects, layout token, held stack, and trace are the
same objects Core's run acts on; a frame of locals per activation,
each bound to a value; and the memory and protocol rules of that
section, which say which loads, stores, and calls are admitted. The
kernel `K` of section 19.1 is the same parameter, and `KernelOk` the
same contract.

### 5.1 Judgments

```
K |- <e, st> => v                  expressions and addresses
K |- <c, st> => b                  conditions
K |- <s, st> => o, st'             statements
K |- <P, st> => halt v, st' | err  programs

o ::= normal | br n | ret v? | raise k r | err
```

Expressions are pure: no call appears in one, so evaluation neither
changes the state nor aborts. It is a partial function of the state;
when it is undefined, because a load is not admitted or a local is
unbound, the statement evaluating it has outcome `err`. `err` is the
outcome the theorems make unreachable, as in Core.

### 5.2 Selected rules

```
(Let)
    K |- <e, st> => v
    ---------------------------------------------
    K |- <let x : T = e, st> => normal, st[x := fit(T, v)]
    fit reduces an integer to int(s,w) and keeps a location

(Store)
    K |- <a, st> => l    K |- <e, st> => v
    the machine admits a store of w bits at l in st
    -----------------------------------------------------------
    K |- <store(w) a e, st> => normal, st[w bits at l := v]
(Store-err)
    otherwise  =>  err

(Frame)
    id fresh in st
    ------------------------------------------------------------
    K |- <frame x : n, st> => normal,
         st[region stack(id) := n zero bytes, x := loc(stack(id), 0)]

(If)
    K |- <c, st> => true     K |- <s1, st> => o, st'
    -------------------------------------------------
    K |- <if c s1 s2, st> => o, st'
    and symmetrically with false and s2

(Seq)
    K |- <s1, st> => normal, st1     K |- <s2, st1> => o, st2
    ----------------------------------------------------------
    K |- <s1 ; s2, st> => o, st2
    K |- <s1, st> => o, st1     o != normal
    ----------------------------------------
    K |- <s1 ; s2, st> => o, st1

(Block)
    K |- <s, st> => normal, st'   or   br 0, st'
    ---------------------------------------------
    K |- <block s, st> => normal, st'
    K |- <s, st> => br (n+1), st'
    -------------------------------
    K |- <block s, st> => br n, st'
    K |- <s, st> => o, st'     o is ret, raise, or err
    ---------------------------------------------------
    K |- <block s, st> => o, st'

(Loop)
    K |- <s, st> => normal, st1   or   br 0, st1
    K |- <loop s, st1> => o, st2
    ---------------------------------------------
    K |- <loop s, st> => o, st2
    K |- <s, st> => br (n+1), st'
    -------------------------------
    K |- <loop s, st> => br n, st'
    ret, raise, and err leave as in (Block)

(Br)      K |- <br n, st> => br n, st
(Return)  K |- <return e, st> => ret (some v), st       when e => v
          K |- <return, st>   => ret none, st
(Raise)   K |- <raise k e, st> => raise k v, st         when e => v

(Call)
    f = fn f (x_i : T_i) ... { body }
    K |- <arg_i, st> => v_i
    st1 = st with a fresh frame binding each x_i to fit(T_i, v_i)
    K |- <body, st1> => o, st2
    held(st2) = held(st)                       else the call is err
    st3 = st2 with the caller's frame restored
    ------------------------------------------------------------
    o = ret (some v)   =>  K |- <x = call f(...) ..., st> => normal, st3[x := v]
    o = ret none       =>  the `absent s` body runs from st3; its
                           outcome and state are the call's
    o = raise k r      =>  the `unwind s` body runs from st3 to
                           normal, st4; the call's outcome is
                           raise k r, st4
    o = normal, no x   =>  normal, st3
    o = br n           =>  err (excluded by well-formedness)

(Kernel)
    h is a call the interface declares with a `.fn` signature
    K |- <arg_i, st> => v_i, fitted to the declaration's parameter kinds
    no held resource forbids `call`, or h is that resource's release
    ------------------------------------------------------------
    K.helper h [v_i] st = ok v st'
        =>  K |- <x = h(...), st> => normal,
            st'[x := r0(v), trace += call h [v_i] v,
                held pushed with the result when h acquires,
                held popped when h releases]
    K.helper h [v_i] st = failed n st'
        =>  normal, st'[x := signal(h, n), trace += call h [v_i] fail n]
    an argument that does not fit its kind, a release whose argument
    is not the innermost held object, or a forbidden call  =>  err

(Lookup)
    K |- <arg, st> => l    the key's bytes at l are initialized
    ------------------------------------------------------------
    array kind, key < capacity  =>  x := loc(map(m, key), 0)
    array kind, otherwise       =>  x := 0(64)
    hash kind, entry i found    =>  x := loc(map(m, i), 0)
    hash kind, not found        =>  x := 0(64)

(Lock)     the argument is the lock field of a map value, and no
           spin lock is held  =>  held pushed with (spinlock, l)
(Unlock)   the innermost held entry is (spinlock, l)  =>  popped
           otherwise  =>  err
(Reserve)  as Core's (reserveOk) and (reserveFull): x := the record's
           location, pushed as held, or 0(64)
(Submit)   the innermost held entry is the record  =>  popped, the
           record appended to the ring; (Discard) popped only

(Program)
    K |- <s, st> => ret (some v), st'     held(st') = []
    ---------------------------------------------------
    K |- <program p : kind { s } H, st> => halt fit(verdict, v), st'
    K |- <s, st> => raise k r, st'        held(st') = []
    K |- <H(k), st'[reason := r]> => ret (some v), st''
    ------------------------------------------------------
    K |- <program p : kind { s } H, st> => halt fit(verdict, v), st''
    K |- <s, st> => normal, st'           the kind has no packet
    ------------------------------------------------------
    K |- <program p : kind { s } H, st> => halt 0, st'
    anything else, including a held stack that is not empty at a
    return or a raise  =>  err
```

The held stack in LIR is protocol state, as in the target machine:
`lock`, `enter`, `reserve`, and an acquiring declaration push; `unlock`,
`leave`, `submit`, `discard`, and a releasing declaration pop and check. Core
tracks the same stack through its `hold` rule; LIR has no `hold`, so
the stack is what makes a missing or misplaced release an error
rather than a silent divergence from Core. The theorem of pass B,
that Core's run is matched by an LIR run without `err`, is therefore
also the statement that the lowering's releases are right.

### 5.3 What is shared with Core, and what is not

Shared verbatim: the maps, the packet and its token, the kernel objects,
the ring buffers, the trace, whose `printk` events carry their untyped
arguments settled to `u64`, and the held stack's declarations and
objects, a spin lock's object being the lock's place. Related, not
shared: Core's frame binds names to values or places with a token, LIR's
binds names to values that may be locations with a token; the pass-B
relation maps one to the other. Dropped: Core's `errno`, which LIR keeps
in an ordinary local written at the failing call; the names Core
attaches to held entries, which LIR does not need because releases are
statements.

## 6. What each Core construct becomes

The table gives the shape; `lowering.md` gives the rule and the proof
obligation. Primed statements are the lowered bodies. Calls that
occur inside Core expressions are hoisted into their own `let`
statements in evaluation order, and any load that precedes a call in
that order is hoisted with it, so that LIR expressions are pure and
the order of effects is Core's.

### 6.1 Values, places, control

| Core | LIR |
|---|---|
| `let x = e`, scalar | `let x : int(s,w) = e'`, with `s,w` the checker's type |
| `let r = p`, aggregate | `let r : ptr = a` |
| `let k : S = { f: e, ... }` | `frame k : size(S) as S`, then one `store` per field; the padding stays zero, which the map lookups that read the key need |
| `p := e` | `store(w) a e` |
| `if e s1 s2` | `if c s1' s2'`; `&&`, `\|\|`, `!` become nested `if`, as Core's short-circuit rules evaluate them |
| a boolean in value position | `let b = 0(8); if c { b := 1(8) }` |
| `loop n s` | `block { c := 0; loop { if !(c < n) { br 1 }; block { s' }; c := c + 1 } }` |
| `for i in a..b s` | `block { i := a; b' := b; loop { if !(i < b') { br 1 }; block { s' }; i := i + 1 } }`; no cap appears |
| `break`, `continue` | `br` to the loop's enclosing block, `br` to the body's block |
| `return e`, a verdict | `return e` |
| `if c s1 s2`, `c` constant | the live branch alone |
| `size T`, `config`, verdict and interface constants, `hton k` | immediates |
| `x = atomic op p e...` | `x = atomic op(s,w) fetch (a, e...)`; on a scalar local, a read and a store, since a local is the program's alone |
| `ctx.f := e` | `ctx f <- e` |
| `let _ = call f(...)` | `call f(...) unwind { ... }` |
| `errno` | the local `err` the failing call's test wrote |

### 6.2 Fallible operations

| Core | LIR |
|---|---|
| `try h = view(e, T) then s1 else s2` | `let p : ptr = pkt_data + e; if p + size(T) > pkt_end { s2' } else { let h : ptr = p; s1' }` |
| `try r = lookup(m, k) then s1 else s2` | `r = lookup m (k); if r == 0 { s2' } else { s1' }` |
| `try x = loadw(p.f) then s1 else s2` | `let x = load(w) (a + off_f)`, one `let` per sibling the predicate mentions, `if !P { s2' } else { s1' }` |
| `try x = coerce(e, {v: T \| P}) then s1 else s2` | `let x = e'; if !P[v := x] { s2' } else { s1' }` |
| `try x = call h(...) then s1 else s2`, scalar result | `x = h(...); if x <(i,64) 0 { err := x; s2' } else { s1' }` |
| the same, location result | `x = h(...); if x == 0 { s2' } else { s1' }` |
| `try x = callopt f(...) then s1 else s2` | `block { x = call f(...) absent { s2'; br 0 } ; s1' }` |

Every test above is the marker the source wrote, and it tests the
value the following code uses, which is the second obligation of
Lemma L stated at the LIR level.

### 6.3 Failure and resources

| Core | LIR |
|---|---|
| `raise k e` | the releases owed at this point, innermost first, then `raise k e` |
| `hold lock(p) then body` | `lock (a); block { body' }; unlock (a)`, with `unlock (a)` before every `br`, `return`, and `raise` that leaves the body, and in the `unwind` of every `fails` call in it |
| `hold rcu then body`, and the other scope declarations | `enter R; block { body' }; leave R`, releases placed as above |
| `hold x = reserve<T>() then body else els` | `x = reserve m size(T); if x == 0 { els' } else { block { body' }; submit x }`, with `discard x` before every abnormal exit |
| `hold x = sk_lookup_tcp(t) then body else els` | `x = sk_lookup_tcp(t); if x == 0 { els' } else { block { body' }; sk_release x }`, likewise |
| `move x` | nothing; the sink call is the release, and the scope emits none on that path |

The releases at an exit are the ones for the resources acquired
between the exit and the target of the exit, innermost first, which
is the order Core's `hold` rules release in. Whether an owned name is
still held at an exit is path-independent by the join rule of `move`,
so the release code at each exit is static; this is the second place
where pass B leans on typing.

### 6.4 The branch the verifier requires

An `array[n]` map with more than one slot is reached through
`lookup`, which the kernel answers with null for an index at or past
the capacity. Core's `m[e]` has no such path: the index obligation
makes it total. LIR emits the test anyway, because the verifier requires
it, and its branch is dead:

```
r = lookup m (key); if r == 0 { return ABORTED_OF_KIND }; ...
```

The dead branch returns the kind's own failure verdict, so that a
violation of the model, should the kernel ever answer null, is
observable through the kernel's exception tracepoint rather than silent;
inside a function, which has no kind, it is an early return of zero, or
a bare `return` for a function without a result or with `T ?`. Per-CPU
arrays are reached this way whatever their capacity, since the kernel's
direct value access exists for plain array maps only. The key of such a
lookup is a 4-byte frame holding the index cast to `u32`, the width the
kernel's array maps take. The pass-B theorem does not see this branch:
the source's derivation takes the in-range path, the machine's `lookup`
answers with a location, and the branch is not taken. Principle P2 is
amended to allow it (`ISSUES.md`, entry 22). Kernels that mark array
lookups with a constant in-range key as non-null make the branch
unnecessary for acceptance as well; the lowering may then omit it.

An element of a view reached by an index that is not a constant is
the other such branch. The verifier gives a packet pointer with a
variable added a fresh id and no range, and links a range only to
the pointers of one id, so the view's own test does not reach the
element's address. LIR binds that address once and tests it:

```
el = h + i * size; if el + size > pkt_end { return ABORTED_OF_KIND }; ...
```

The branch is dead by the view's window and the index obligation, its
value is as above, and the accesses go through `el`, so that the
comparison is on the pointer they use. A constant index needs no
test, since the verifier keeps the id across a constant offset
(`ISSUES.md`, entry 39).

### 6.5 The frame

Core allocates a fresh stack region for each struct literal. LIR does
the same with `frame`, and adds frames the source did not have: the
key of a hash lookup or an array lookup by helper, which the kernel
takes by address, and the temporary a scalar is spilled into when a
builtin needs its address. Every frame is zeroed, so that the bytes
a helper reads, padding included, are initialized, which both Core's
semantics and the verifier require.

### 6.6 Inlining, LIR to LIR

The call graph is acyclic. Inlining replaces `x = call f(args)
unwind U absent A` by the callee's body with its parameters bound to
the arguments, its locals renamed apart, and three substitutions:
`return e` becomes `x := e; br d`, and a bare `return` becomes
`A; br d`, where `d` counts the `block` and `loop` constructs between
the return and the block that wraps the inlined body; `raise k e`
becomes `U; raise k e`; and a nested `call g(...) unwind U'` becomes
`call g(...) unwind (U'; U)`. Scalars bind by value, `ref` and
`view` parameters by their location, as Core's (Frame) rules do. The
result is closed LIR, with one function per program and no call
statements except builtins and kernel functions. `lowering.md` states
the pass and its theorem.

## 7. What is not in LIR

No registers, no frame layout, no instruction selection, no
calling convention: the flattening pass and the allocation pass of
`bir.md` decide those. No facts, no refinements, no effects: the
checker spent them. No loop caps: the cap of a `for` loop is the
checker's output to the lowering, decision 43, and it selects the
bytecode form of the loop without entering the semantics; a `for`
loop runs until its bound, as Core's does, and the verifier converges
because the bound is a constant or a value whose fact is on the path
(Lemma L). No `hold`, no `try`, no `move`, no `for`, no optionals,
no polymorphic literals, no `errno`.

## 8. Printing to C

The C printer is one function from LIR to text, one construct at a
time, and it is not part of any theorem: the C path is the portable
one through clang and libbpf, untrusted and validated per program
like everything the compiler emits, and readable enough to be the
artifact a reader compares with the source.

| LIR | C |
|---|---|
| `let x : int(s,w) = e` | `uW x = e;` or `sW x = e;` with the fixed-width typedefs |
| `let x : ptr = a` | `void *x = a;` or the struct pointer when the source type is known |
| `e op(s,w) e` | the operator, through the total-arithmetic shim: `DIV_uW(a, b)`, `MOD_sW(a, b)`, `SHL_W(a, s)` and the signed operators as unsigned operations with casts, so that no C undefined behavior is reachable |
| `cast` | a C cast between fixed-width types, which has the semantics of section 8.1 |
| `bswap(w)` | `__builtin_bswapW` |
| `load(w) a`, `store(w) a e` | `*(uW *)(a)` |
| `frame x : n as S` | `S x = {0};` or `u8 x[n] __attribute__((aligned(8))) = {0};` |
| `ctx f`, `pkt_data`, `pkt_end` | `ctx->f`, `(void *)(long)ctx->data`, `(void *)(long)ctx->data_end`; in a function, the two `void *` parameters the printer adds for the bounds |
| `mapval m + k` | a lookup of slot 0 with a null test that aborts, since C has no direct value access for a declared map; the two backends differ here |
| `block`, `loop`, `br` | a label after the block, `for (;;)`, and `goto`; the printer may re-sugar the loop shapes of 6.1 into `for` with `break` and `continue` |
| `raise k e` | `reason = e; goto handler_k;` |
| `call f` | a call of the `static __always_inline` function; `unwind` and `absent` as the error-code protocol of the portable failure lowering, tested after the call |
| `lookup m`, `update m`, `delete m`, `reserve`, `submit`, `discard`, `lock`, `unlock` | the uapi helper names |
| `h(...)` | the declaration's kernel name |
| `printk "fmt"` | `bpf_printk` with `{}` rewritten to the format of each argument's width |
| maps | BTF-defined maps in `SEC(".maps")`, with `struct bpf_spin_lock` for the slot field |
| programs | `SEC("...")` from the kind declaration, the handlers as labeled tails ending in `return` |

The printer may add acceptance idioms the semantics does not know,
such as `barrier_var` after a coercion's test, when measurement
shows clang needs them; they are printer policy, recorded in
`lowering.md`, never LIR.

## 9. Decisions this draft embeds

1. LIR is Core after the checker, structured, with functions, and
   is produced per function; a separate LIR-to-LIR pass inlines.
2. Expressions are pure; calls are statements; calls inside Core
   expressions are hoisted in evaluation order with the loads that
   precede them.
3. Widths come from the checker's types; every literal and operator
   carries its width; signedness is carried where it matters.
4. Control is `block`, `loop`, `br n`, `if`, `return`; `break`,
   `continue`, inlined returns, and absence are all `br`.
5. Failure is `raise k e` with an outcome; the releases owed at a
   site are statements before it; a call site owes its releases in an
   `unwind`; there is no `hold`.
6. The held stack is protocol state of the semantics, checked at
   every release and at every exit of the program, so that the pass-B
   theorem states the release discipline.
7. No loop caps in the semantics; `for` runs to its bound.
8. Every carve reads `pkt_data` and `pkt_end` afresh; there is no
   reload-after-resize bookkeeping, and the token rule does the rest.
9. Null is the scalar zero; the null test is the only comparison of
   a location with a scalar.
10. Frames are fresh zeroed regions, as Core's struct literals are,
    and the keys helpers take by address are frames the source did
    not write.
11. Array maps with one slot are reached by `mapval`; the others by
    `lookup` with the dead branch of 6.4, under the amendment to P2
    of entry 22; a view's element by a non-constant index is bound
    once and tested with the second dead branch of 6.4 (entry 39).
12. Byte-order values are bit patterns and memory is little-endian
    (entry 24).
13. `errno` is a local written by the test after a failing call.
15. Folded 2026-09-19 from `ISSUES.md` entry 26: the context store,
    the signedness of an atomic update, the dead branch inside a
    function, the 4-byte key frame, per-CPU arrays by lookup, kernel
    results bound at `int(i,64)` or `ptr`, and `pkt.len` as a kernel
    call.
14. The C printer is outside every theorem and may re-sugar control
    and add acceptance idioms.
