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
