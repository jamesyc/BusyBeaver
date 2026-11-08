# Verification

Both PA213 default Lake packages built successfully with Lean 4.35.0 on
ARM64 macOS, using the pinned dependencies, official Mathlib cache, and
two reviewed Foundation proof repairs. The core axiom audit passed all
eight roots, and the final audit passed all five endpoint roots. Every
endpoint uses exactly `propext`, `Classical.choice`, and `Quot.sound`.
[Endpoint axiom report](../evidence/publication/endpoint-axioms.txt)

The frozen endpoint build completed 3,224 targets. Its dependency closure
contains 2,097 project and Foundation modules, including 144 Foundation modules.
The final theorem combines the 213-control bound, exact 426-row sentence,
blank nonhalting, standard-model truth, and one-sided PA unprovability
under ordinary PA consistency.
[Final build receipt](../evidence/pa213/FINAL_PA_RECEIPT.json) · [Frozen source manifest](../evidence/pa213/FINAL_PA_MANIFEST.json) · [Theorem statements](result.md)

The package contains 1,955 local proof modules, comprising the endpoint's
1,953-module local dependency closure and the two package roots. The input
checks compare all 426 table rows with the dense and sparse Lean representations and all
3,947 source sites with the frozen JSON. The package check verifies the recorded file hashes.
[Run the checks](reproduction.md)

The package names are `pa213` and
`pa213Metamathematics`, with `PA213` and `PA213PA` as their sole default
targets.
