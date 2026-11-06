# Formal theorem statements

The formalization uses Foundation's first-order theory `Peano`.
`PA215.PA.Consistent` means that no proof of a contradiction can be derived
in that theory. The initial tape contains only zeros, extends infinitely in
both directions, and has its head at position zero.
[Theory](../Lean/metamathematics/PA215PA/Theory.lean) · [Tape semantics](../Lean/PA215/Tape.lean)

| Theorem | Statement |
|---|---|
| `PA215.PA.CachedV2.consistent_machine_nonhalting` | If PA is consistent, `¬ PA215.Halts PA215.blank`. |
| `PA215.PA.CachedV2.consistent_nonhalting_sentence` | If PA is consistent, `HaltingFormula.nonhaltingSentence` is true in the standard natural numbers. |
| `PA215.PA.InternalUnprovability.pa_proves_nonhalting_consistency` | PA proves that `HaltingFormula.nonhaltingSentence` implies `consistencySentence`. The proof of this implication requires no external consistency assumption. |
| `PA215.PA.InternalUnprovability.nonhalting_unprovable` | If PA is consistent, PA cannot prove `HaltingFormula.nonhaltingSentence`. |

[MachineNonhaltingV2.lean](../Lean/metamathematics/PA215PA/MachineNonhaltingV2.lean)
contains the first two proofs.
[NonhaltingUnprovability.lean](../Lean/metamathematics/PA215PA/NonhaltingUnprovability.lean)
contains the last two. The [article](../README.md) explains how they fit together.
