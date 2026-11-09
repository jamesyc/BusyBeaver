# Verification

## Package checks

Run `bash scripts/check.sh` to verify file hashes and compare the literal,
sparse, and arithmetic transition tables. The checker also reconstructs
the source program from the Lean tree and verifies the default import
closure and all nine endpoint audit declarations. Mutation tests exercise
changes to transition rows, state relabelings, and source instructions.
[Reproduction instructions](reproduction.md)

## Build results

The serial build passed all 2,420 scheduled modules, including 2,276
project modules and 144 Foundation modules. Both default targets also
built successfully. Lake reported 336 jobs for `PA211` and 3,548 for
`PA211PA`. The build allowed cached external dependencies, including
Mathlib and the Lean toolchain. [Build record](../evidence/publication/local-validation.json)

The default targets use support modules in the `PA213`, `PA215`,
`PA213PA`, and `PA215PA` namespaces for the proof calculus, scheduler,
refutation compiler, and machine lemmas. The build also uses two pinned
Foundation patches. [Patch specifications](../Lean/metamathematics/patches/README.md)

## Axiom audits

The core audit passed all eight physical and runtime declarations. The
metamathematics audit passed all nine endpoint declarations, including the
literal endpoint, the internal consistency implication, and both sides of
independence. The audits found only `propext`, `Classical.choice`, and
`Quot.sound`. The literal arithmetic binding uses no axioms.
[Core axiom report](../evidence/publication/core-axioms.txt) ·
[Endpoint axiom report](../evidence/publication/endpoint-axioms.txt)

A separate check imported the default metamathematics root and verified
that the two-sided theorem is stated for ordinary `Peano` with no
explicit premises, and that the nonhalting corollary uses the literal
table and starts in state 0 on a blank tape.
[Formal theorem statements](result.md) ·
[Interface check](../evidence/publication/local-validation.json)
