# ZF207

A binary Turing machine with 207 working states and a halting sentence whose
independence from first-order ZF has two explicit assumptions:

- Consistency of ZF implies actual nonhalting and unprovability of nonhalting.
- Arithmetic Σ₁-soundness of ZF implies unprovability of both halting and nonhalting.

The exact compared statement is `PalomarZF207.exact207Claim`. It constructs a
sentence and proves its machine meaning in every ZF model, including models
with nonstandard natural numbers. The machine-meaning theorem and compiler
correctness are conclusions of the proof, not assumptions supplied by a caller.

The machine runs the same proof search as [ZF209](../ZF209/README.md) with a
smaller decoder for the stored program. The Lean development is ZF209's with
the literal table, the startup run and the per-instruction simulation checks
redone for the 207-state table; it does not rely on ZF209's machine. The
[paper](paper/zf207.pdf), [literal machine](data/zf207.tm),
[standalone statement](ProofSources/Challenge.lean), and
[proof entry point](ProofSources/Solution.lean) are kept together here.

This is a separate Lake project. The local build, axiom audit and Comparator
passed, with Lean's kernel, NanoDa and the bundled con-ron accepting the
Solution export. Comparator ran unsandboxed on macOS. Palomar submission is
pending. See [reproduction](docs/reproduction.md) and the
[verification record](docs/provenance.md#verification-record).

The repository MIT licence covers the project sources. Foundation retains
its [upstream licence](Vendor/FOUNDATION_LICENSE) and original namespaces.
