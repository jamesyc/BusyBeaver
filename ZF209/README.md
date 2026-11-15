# ZF209

A binary Turing machine with 209 working states and a halting sentence whose
independence from first-order ZF has two explicit assumptions:

- Consistency of ZF implies actual nonhalting and unprovability of nonhalting.
- Arithmetic Σ₁-soundness of ZF implies unprovability of both halting and nonhalting.

The exact compared statement is `PalomarZF209.exact209Claim`. It constructs a
sentence and proves its machine meaning in every ZF model, including models
with nonstandard natural numbers. The machine-meaning theorem and compiler
correctness are conclusions of the proof, not assumptions supplied by a caller.

This is a separate Lake project from [PA196](../PA196/README.md). The
[paper](paper/zf209.pdf), [literal machine](data/zf209.tm),
[standalone statement](ProofSources/Challenge.lean), and
[proof entry point](ProofSources/Solution.lean) are kept together here.

The unprovability of nonhalting goes through an arithmetic theory read off
from proofs in the machine's calculus, so Foundation's second incompleteness
theorem for arithmetic applies directly; see the paper.

The local Linux build, axiom audit and stock Comparator passed. Lean's
default kernel and NanoDa accepted the Solution export. The pinned con-ron
replay reached its local 30-minute limit under x86 emulation without a
verdict. Palomar submission is pending. See [reproduction](docs/reproduction.md)
and the [verification record](docs/provenance.md#verification-record).

The repository MIT licence covers the project sources. Foundation retains
its [upstream licence](Vendor/FOUNDATION_LICENSE) and original namespaces.
