# Nonhalting and PA-independence for a 196-state Turing machine

PA196 is an explicit binary Turing machine that searches for a contradiction
in ordinary first-order Peano arithmetic (PA). Lean 4 proves that it runs
forever from a blank tape and that PA proves neither its exact arithmetic
halting sentence nor its negation.

[Paper (PDF)](paper/pa196.pdf) · [Transition table](data/pa196.tm) ·
[Theorem statements](docs/result.md) · [Reproduction](docs/reproduction.md)

The machine has 196 working states and 392 rows, reducing the working-state
count of the [previous published construction](https://github.com/jamesyc/BusyBeaver/tree/69d98241a721ead20b4f0b17df9062950b40fbfe) by 13. It starts in state 0 on an
all-zero tape and reaches the register-program frame for candidate 2 after
58,154 steps. The tape machine implements a proof-command search with a
transposed universal-quantifier code and a guarded equality-vacuity clause.
The proof verifies the startup and the simulation at all 3,812 source sites.

In an arbitrary model of PA, a coded PA refutation yields an accepted
certificate, a halting source execution, and a coded trace for the literal
machine. PA therefore proves that nonhalting implies its own consistency.
Gödel's second incompleteness theorem excludes a PA proof of nonhalting under
consistency. Soundness in the standard natural numbers excludes a PA proof of
halting. Foundation supplies standard-model consistency and soundness in
Lean's metatheory.

| Component | Lean |
| --- | --- |
| Literal table and startup | [Literal](ProofSources/PA196/Literal.lean), [Startup](ProofSources/PA196/Startup.lean) |
| Tape simulation and command calculus | [Coverage](ProofSources/PA196/Coverage.lean), [Logic](ProofSources/PA196/Logic/Basic.lean), [Nonhalting](ProofSources/PA196/Nonhalting.lean) |
| Exact trace sentence and internal implication | [Literal binding](ProofSources/PA196/Arithmetic/Machine/Exact/SentenceCorrectness.lean), [Refutation-to-halting](ProofSources/PA196/Arithmetic/RefutationHalting.lean), [Independence](ProofSources/PA196/Independence.lean) |
| Palomar statement and proof | [Challenge](Challenge.lean), [Solution](ProofSources/PA196/Palomar/Solution.lean), [Axiom audit](Audit.lean) |

Run `bash scripts/check.sh` for the source and table checks, or
`bash scripts/check.sh --full` to build and audit the proof. The root license
is MIT. Bundled support retains its own license notices.

Run these commands from this `PA196/` project directory. Lean file paths in
the paper are relative to `ProofSources/`; data and documentation paths are
relative to this directory. The paper and its PDF are unchanged from main
before this reorganization.

Shared tape-engine code now lives in `ProofSources/PA196/Engine`, and arithmetic
support in `ProofSources/PA196/ArithmeticSupport`. The Lake libraries retain
their `M6` and `M6PA` names, and all original declaration namespaces and credits
are preserved. There are no separate M6 or M6PA source folders.
