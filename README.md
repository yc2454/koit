# koit

An eBPF source language whose types are the conditions the kernel
verifier checks. Status, 2026-09-12: the language is defined (draft 3);
implementation begins with the checker.

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
Stage 1 is the front end and the checker, `koitc parse` and `koitc
check`; the Core interpreter follows; the C backend and the kernel
table generator are the phase after.

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
