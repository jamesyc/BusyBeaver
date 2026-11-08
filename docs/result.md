# Formal theorem statements

The formalization uses Foundation's first-order theory `Peano`.
The consistency hypothesis means that no proof of a contradiction can be
derived in that theory. The physical machine is
`PA213.CandidateTable.machine`, with 213 working controls and 426 transitions.
The initial tape contains only zeros and extends infinitely in both directions.
`PA213.Startup.blank` places the head at zero with physical control 74.
[Theory](../Lean/metamathematics/PA213PA/Theory.lean) · [Machine](../Lean/PA213/CandidateTable.lean) · [Startup](../Lean/PA213/StartupData.lean)

In the statements below, *N* is
`PA213.PA.ExactHaltingFormula.nonhaltingSentence`, the sentence for the
exact 426-row machine.

| Theorem | Statement |
|---|---|
| `PA213.PA.consistent_machine_nonhalting` | If PA is consistent, the physical machine cannot halt from `PA213.Startup.blank`. |
| `PA213.PA.InternalUnprovability.nonhalting_true` | If PA is consistent, *N* is true in the standard natural numbers. |
| `PA213.PA.InternalUnprovability.pa_proves_nonhalting_consistency` | PA proves *N* → Con(PA). This implication requires no external consistency assumption. |
| `PA213.PA.InternalUnprovability.nonhalting_unprovable` | If PA is consistent, PA cannot prove *N*. |
| `PA213.PA.InternalUnprovability.final_endpoint` | Under PA consistency, combines the 213-control bound, 426-row count, physical blank nonhalting, standard-model truth, and PA unprovability. |

[MachineNonhalting.lean](../Lean/metamathematics/PA213PA/MachineNonhalting.lean)
contains the physical nonhalting proof.
[NonhaltingUnprovability.lean](../Lean/metamathematics/PA213PA/NonhaltingUnprovability.lean)
contains the remaining four theorems.

## Two-sided independence

The default build also includes
[TwoSidedIndependence.lean](../Lean/metamathematics/PA213PA/TwoSidedIndependence.lean).
It uses Foundation's proof that the standard natural numbers model PA and
logical soundness. The five original statements above are unchanged.

| Theorem | Statement |
|---|---|
| `PA213.PA.Independence.nonhalting_irrefutable` | Given PA consistency, PA cannot prove the negation of *N*, using standard-model soundness already proved by Foundation. |
| `PA213.PA.Independence.two_sided_independence` | PA proves neither *N* nor its negation. There are no explicit premises: Foundation's standard-model consistency instance discharges the consistency hypotheses. |
| `PA213.PA.Independence.machine_nonhalting` | The physical machine cannot halt from `PA213.Startup.blank`. The same instance discharges the consistency premise of `consistent_machine_nonhalting`. |

Soundness and consistency are established in Lean's metatheory; they are
not asserted to be PA theorems. All three new declarations use only `propext`,
`Classical.choice`, and `Quot.sound`, and are included alongside the five
original roots in the [extended axiom audit](../evidence/publication/independence-axioms.txt).
