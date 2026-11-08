# Nonhalting and PA-unprovability for a 213-state Turing machine

Let PA stand for ordinary first-order Peano arithmetic. PA is consistent if its axioms admit no proof of a contradiction.

> If PA is consistent, PA213 runs forever on a blank tape, and PA cannot prove the arithmetic sentence that says it runs forever.

PA213 searches for a proof of a contradiction from the axioms of PA. A proof is a finite derivation. Each line contains a formula, and a mechanical rule determines whether that line follows from the axioms or from earlier lines. The machine encodes formulas and derivations as numbers on its tape. It halts when it derives a contradiction.

The tape extends infinitely in both directions. Each cell holds a 0 or a 1, and all cells start at 0. The machine starts in state 0. Its 213 working states use labels 0 through 214 with 122 and 214 omitted. For each working state there are two rows in the transition table, one for each symbol the machine might read. The first row, `0 0 1 R 1`, says that in state 0, on reading a 0, the machine writes a 1, moves right, and enters state 1. There are 426 rows. State 215 signals a halt and is excluded from the working-state count. [Complete transition table](Lean/data/pa213.tm)

## Non halting

If PA is consistent, the search can never find a contradiction. To prove that the machine runs forever, we also have to show that its 426 transition rules carry out that search from a blank tape.

The Lean proof starts with a search program containing 3,947 instruction sites. After exactly 64,764 tape steps from the blank tape, the machine reaches a frame corresponding to a checked 159-step prefix of the source program. Using 5,134 runtime contract records, the proof checks what the machine does at each reachable configuration that represents a search instruction. A positive, finite number of tape steps brings it to the configuration for the next instruction.

After simulating *k* instructions, the machine must have taken at least *k* tape steps. Suppose it halted after *t* steps. The search can execute *t* + 1 instructions, so the machine must be able to take at least *t* + 1 steps. That rules out a halt at *t*. [Blank-tape startup](Lean/PA213/StartupExact.lean) · [Positive progress](Lean/PA213/CompilerCorrectness.lean) · [Nonhalting theorem](Lean/metamathematics/PA213PA/MachineNonhalting.lean)

## Unprovability in PA

PA can describe a run of the machine by encoding its successive configurations as numbers. Let *N* say that no natural number encodes a finite run of PA213 from the blank tape to state 215. Every halting run can be encoded as a trace. Conversely, any witnesses to the trace formula decode to a halting run of this machine. In the natural numbers, then, *N* says exactly that PA213 runs forever. [Trace formula and its interpretation](Lean/metamathematics/PA213PA/ExactHaltingFormula.lean)

Suppose a number codes a PA proof of a contradiction. The formalization translates it into a code the search program accepts, and from that code obtains a halting trace. In every model of PA, including nonstandard models, a code for a refutation would therefore make *N* false. By completeness of first-order logic, PA itself proves *N* → Con(PA), where Con(PA) is its arithmetic sentence for consistency. [Proof-code translation](Lean/metamathematics/PA215PA/FoundationNativeRefutationTransport.lean) · [From a refutation to a halting trace](Lean/metamathematics/PA213PA/InternalActualRefutationHalting.lean)

If PA also proved *N*, it could apply that implication and prove Con(PA). Gödel's second incompleteness theorem rules this out when PA is consistent. Under that assumption, *N* is true and PA cannot prove it. Two-sided independence would require a further result ruling out a PA proof of the negation of *N*. The figure 213 counts the working states of this particular machine. [Unprovability theorem](Lean/metamathematics/PA213PA/NonhaltingUnprovability.lean)

## Formal verification

The frozen PA213 build used Lean 4.35.0 and completed 3,224 targets. Its final theorem combines the 213-state and 426-row counts, nonhalting from the blank tape, truth of *N* in the natural numbers, and the unprovability of *N* under consistency. PA's internal implication *N* → Con(PA) is also proved. The audited endpoint uses propositional extensionality (`propext`), classical choice (`Classical.choice`), and quotient soundness (`Quot.sound`). [Formal statements](docs/result.md) · [Frozen build receipt](evidence/pa213/FINAL_PA_RECEIPT.json)

The physical proof uses an equivalent sparse labeling, with start label 74 and halt label 254. The arithmetic sentence uses exactly the published table's 426 transitions. Lean proves its equivalence to an auxiliary encoding with two unreachable padding states. The default build checks PA213, and the axiom audit covers its five endpoint theorems. [Table relabeling](Lean/PA213/CandidateTable.lean) · [Exact arithmetic sentence](Lean/metamathematics/PA213PA/ExactHaltingFormula.lean) · [Verification records](docs/validation.md)

## References and reproduction

- Tibor Radó, “On Non-Computable Functions,” *Bell System Technical Journal* 41 (1962), 877–884. [Paper](https://doi.org/10.1002/j.1538-7305.1962.tb00480.x)
- Kurt Gödel, “Über formal unentscheidbare Sätze der Principia Mathematica und verwandter Systeme I,” *Monatshefte für Mathematik und Physik* 38 (1931), 173–198. [Paper](https://doi.org/10.1007/BF01700692)

The repository includes the table, the search program, and the proof inputs with their hashes. Once you've installed the pinned toolchain and dependencies, run `bash scripts/check.sh --full` from the repository root. [Reproduction instructions](docs/reproduction.md) · [Citation](CITATION.cff)
