# Formal theorem statements

The formalization uses Foundation's ordinary first-order theory `Peano`.
The published machine is `PA211.UserCandidate.Dense.machine`, started at
`PA215.Zip.zc 0 [] []`: literal state 0 on a blank binary tape. Its 211
working states have 422 rows; 215 is the halt label.
[Literal table](../Lean/PA211/UserCandidate/Dense.lean) · [Theory](../Lean/metamathematics/PA215PA/Theory.lean)

Write *N* for
`PA211.UserCandidate.PA.ExactHaltingFormula.nonhaltingSentence`.
The premise `PA215.PA.Consistent` expresses consistency of ordinary PA.

The final audit checks these nine declarations. In the table, names are
relative to `PA211.UserCandidate.PA`.

| Theorem | Statement |
|---|---|
| `literal_final_endpoint` | Under PA consistency, combines the 211-state and 422-row counts, literal blank-tape nonhalting, truth of *N*, and PA unprovability of *N*. |
| `consistent_literal_nonhalting` | Under PA consistency, the literal machine does not halt from the blank tape in state 0. |
| `InternalUnprovability.nonhalting_true` | Under PA consistency, *N* is true in the natural numbers. |
| `InternalUnprovability.pa_proves_nonhalting_consistency` | PA proves *N* → Con(PA), without an external consistency premise. |
| `InternalUnprovability.nonhalting_unprovable` | Under PA consistency, PA cannot prove *N*. |
| `literal_arithmetic_binding` | Every active arithmetic row equals the corresponding transition of the literal table. |
| `Independence.nonhalting_irrefutable` | Under PA consistency, standard-model soundness rules out a PA proof of the negation of *N*. |
| `Independence.two_sided_independence` | PA proves neither *N* nor its negation, with no explicit premises. |
| `Independence.machine_nonhalting` | The literal machine does not halt from the blank tape, with no explicit premises. |

The final three declarations use Foundation's standard-model soundness and
consistency theorems in Lean's metatheory.
[Literal endpoint](../Lean/metamathematics/User211LiteralEndpoint.lean) ·
[Independence corollaries](../Lean/metamathematics/PA211PA/TwoSidedIndependence.lean) ·
[Axiom audit](../Lean/metamathematics/Audit.lean)

The physical simulation uses a sparse relabeling with start 74 and halt
254. `Dense.run_conjugate` binds literal runs to that encoding. The
arithmetic auxiliary table has 430 rows on 215 tags; the exact sentence
removes all four unreachable tags 122, 150, 205, and 214.
