# Nonhalting and PA-independence for a 211-state Turing machine

Let PA stand for ordinary first-order Peano arithmetic. PA is consistent if its axioms admit no proof of a contradiction.

> PA211 runs forever on a blank tape, and PA can neither prove nor refute its arithmetic nonhalting sentence. The consistency-conditional proof is checked independently; the two-sided corollary uses Foundation's standard model of PA in Lean's metatheory.

PA211 searches for a proof of a contradiction from PA. Its proof commands encode formulas and finite derivations as numbers. The machine halts when the command interpreter derives falsity.

The tape extends infinitely in both directions, contains only zeros initially, and has alphabet `{0,1}`. The machine starts in state 0. Its 211 working states use labels 0 through 214 with 122, 150, 205, and 214 omitted. There are 422 transition rows. State 215 signals a halt and is excluded from the working-state count. [Complete transition table](Lean/data/pa211.tm)

## Nonhalting

If PA is consistent, the search cannot derive a contradiction. The Lean proof connects that search to the exact transition table. The source has 3,947 instructions, represented by a 173-node tree. Its instruction order and successors are unchanged from the accepted interpreter; 366 source paths were rearranged to obtain this machine. The new source equivalence, physical runtime, and all-model runtime are checked separately.

After exactly 64,764 tape steps, the machine reaches the frame for a checked 159-step source prefix. The proof checks all 5,134 branch-sensitive runtime duties and covers every source site. Each simulated instruction takes a positive number of tape steps. An indefinitely running source therefore gives an indefinitely running tape machine. [Source equivalence](Lean/User211SourceEquivalence.lean) · [Physical endpoint](Lean/PA211/UserCandidate/KernelEndpoint.lean) · [Nonhalting from PA consistency](Lean/metamathematics/User211ConsistentNonhalting.lean)

## Independence from PA

Let *N* be the exact arithmetic sentence saying that no finite halting trace exists. Its step formula uses exactly the 422 active rows. Lean binds those arithmetic rows directly to the published literal table and proves standard-model adequacy through the physical encoding. [Exact sentence](Lean/metamathematics/User211EndpointExactHaltingFormula.lean) · [Literal row binding](Lean/metamathematics/User211LiteralArithmeticBinding.lean)

The proof translates a PA refutation code into an accepted certificate and then into a halting trace, uniformly in every PA model. Consequently PA proves *N* → Con(PA). If PA proved *N*, it would prove its own consistency, contrary to Gödel's second incompleteness theorem under PA consistency. [Internal implication and unprovability](Lean/metamathematics/User211NonhaltingUnprovability.lean)

Foundation proves that the natural numbers model PA, hence that PA is consistent and its theorems are true there. A PA proof of the negation of *N* would contradict the established truth of *N*. The combined independence and literal blank-tape nonhalting theorems therefore have no explicit premises. These are results in Lean's metatheory, not PA proofs of its own consistency. [Two-sided theorem](Lean/metamathematics/PA211PA/TwoSidedIndependence.lean) · [LaTeX exposition](docs/pa211-independence.tex)

## Formal verification

The Lean formalization checks source equivalence, the physical simulation, the runtime in every PA model, and the literal endpoint. Foundation's standard model of PA supplies the consistency and soundness used for the two-sided result. [Formal statements](docs/result.md) · [Verification records](docs/validation.md)

The default targets `PA211` and `PA211PA` use support libraries under the `PA213`, `PA215`, `PA213PA`, and `PA215PA` namespaces. The final audit covers nine PA211 roots and allows `propext`, `Classical.choice`, and `Quot.sound`.

## References and reproduction

- Tibor Radó, “On Non-Computable Functions,” *Bell System Technical Journal* 41 (1962), 877–884. [Paper](https://doi.org/10.1002/j.1538-7305.1962.tb00480.x)
- Kurt Gödel, “Über formal unentscheidbare Sätze der Principia Mathematica und verwandter Systeme I,” *Monatshefte für Mathematik und Physik* 38 (1931), 173–198. [Paper](https://doi.org/10.1007/BF01700692)

Run `bash scripts/check.sh` for package and input checks. With the pinned Lean toolchain and dependencies installed, `bash scripts/check.sh --full` builds the metamathematics root and runs its axiom audit. [Reproduction instructions](docs/reproduction.md) · [Citation](CITATION.cff)
