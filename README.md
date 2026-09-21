# koit

An eBPF source language whose types are the conditions the kernel
verifier checks. Status, 2026-09-14: the language is defined (draft 3
plus the folded revisions of 2026-09-13); the front end, the
desugaring to Core, and the base half of the checker are implemented
(`koitc parse | print | desugar | check`); facts and entailment are
next.

## Thesis

The conditions the kernel verifier checks can be stated as a type system
at the source, and koit is that type system. A well-typed program
compiles to bytecode the verifier accepts without a fight, is safe by the
language's own theorem independently of the verifier, and can tell the
kernel, through a proof-carrying pipeline, what the verifier cannot
infer. See `spec/motivation.md` for the full argument and the claims.

## Reading order

1. `spec/motivation.md`: problem, prior work, thesis, the claims E1-E10,
   what we do not claim, evidence still to produce.
2. `spec/language.md`: the definition. Sections 2-17 surface language,
   18-20 formal core and theorems, 21 decisions and open questions, 22
   extensions not yet defined, 23 template and examples.
3. `spec/mechanisms-draft3.md`: each mechanism re-derived against the
   kernel's own state, with what is new, what is not, and the open
   points; `spec/mechanisms-by-example.md`: the four mechanisms with
   small C versus koit examples; `spec/mechanisms.md` for the theory,
   verbatim production examples, and why these four;
   `spec/verifier-checks.md` for the classification of the verifier's
   rejection messages and the state model read from upstream v7.0.
4. `spec/constructs.md`, `spec/related-languages.md`,
   `spec/comparison-beepl-kernelscript.md`, `spec/cve-study.md`,
   `spec/safety-claim.md`, `spec/contracts.md`: supporting studies.
5. `spec/examples/bmc-request-path.md`: BMC's request path in C and koit.
6. `spec/mechanisms.bib`: citations; entries marked "to verify" need
   checking before submission.

## Implementation

The plan is `PLAN.md`: near sessions planned to the task, later ones to
the phase. The language itself is written in Lean 4, one Lake project,
because everything from the AST to the lowered IR carries a theorem;
kernel-facing tooling is Rust or Python. Source files end in `.ko`.
Stage 1 is the front end and the checker: `koitc parse`, `koitc
desugar` (the Core of `spec/language.md` 18.1), and `koitc check`,
whose base half (declarations, names, base types, places against
values, the positions of fallible operations, exits) is done and whose
facts, entailment, effects, and resources are sessions 3 and 4; the
Core interpreter follows; the C backend and the kernel interface's
transcriber are the phase after. `tests/run.sh` runs the corpus; `KOIT_STAGE=check`
runs the checker over it. `tests/demo/` holds four short programs,
one per mechanism, written to be read rather than to cover cases, and
held to everything the corpus is held to at every stage. The kernel interface, the tables of section
13 for `xdp`, `tc`, and `syscall`, is `Koit/Interface/`: the koit side
in `KoitSide.lean`, the kernel side per tag under `Kernel/`, written
by `tools/transcribe/transcribe.py` from a Linux tree and never
edited, and their join with its checks in `Join.lean`, run at build
time by `Interface.lean`. The checker is
`Koit/Check/` (one judgment: `Env`, `Types`, `Expr`, `Stmt`, `Decl`,
and `Rules` for the judgment as a proposition); the refinement layer
(`Koit/Facts/`) and the effect layer (`Koit/Effects/`) are its next
two inputs.

The editor support is `editor/vscode/`, a Visual Studio Code
extension: highlighting from a grammar over the language's keywords,
the checker's diagnostics as the file is typed through `koitc check
--json`, hovers over the constructs and over the kernel interface
`koitc interface` prints, and the bytecode and the C beside the
source. It reimplements nothing about the language; everything it
shows is `koitc` output, so it cannot drift from the compiler. Its
README says how to run it.

Rule while implementing: gaps or contradictions found in the spec are
logged in `spec/ISSUES.md` with a proposed resolution, not silently
resolved in code.

## Decisions pending

- Proof assistant: decided, Lean 4, since the checker and the proofs
  share one codebase; Rocq's advantage was composition with the eBPF
  ISA semantics, which matters only for a verified compiler.
- Open questions Q1-Q10 in `spec/language.md` section 21, each with
  the default the checker implements until decided.

## Outside this repository

Alivio (`~/Alivio`), the userspace verifier mirror, is the future
translation-validation oracle; the kernel source (`~/linux-stable`) is the
source of the verifier-checks classification; the NSF proposal
(`~/nsf-future-core-2026`) is the funding context, and its DSL section is
a sketch that this repository supersedes.
