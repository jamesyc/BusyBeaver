# Verification

Lean 4.35.0 compiled both default Lake packages on ARM64 macOS. The
metamathematics root depends on 2,515 local modules through its imports. Its build used the pinned
dependencies, official Mathlib cache objects, and the two documented
Foundation patches.

The core package passed its axiom check for 109 theorem roots. For each of the
four theorems in the article, Lean traced the dependencies back to exactly
`propext`, `Classical.choice`, and `Quot.sound`.
[Theorem statements](result.md) · [Axiom report](../evidence/publication/endpoint-axioms.txt)

The conditional machine-nonhalting theorem also has a separate kernel check.
Of the 4,030 modules it depends on, 768 were replayed afresh. For the other
3,262, the check verified that the module and its dependencies matched those
already validated. [Kernel check](../evidence/nonhalting/SUCCESSOR_RESULT.json)

The input checks compare all 430 rows of the transition table, all 3,947
instruction sites, and all 5,134 census records with their Lean representations.
They also check file identities, imports, and the presence of the four theorem
names in the axiom audit. [Run the checks](reproduction.md)
