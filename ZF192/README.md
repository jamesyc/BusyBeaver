# ZF192

A binary, deterministic Turing machine with 192 working states and a separate halt
label. The blank tape is all zero, the initial state is 0, and the tape is infinite
in both directions. The literal table has 384 transitions. The contextual
scanner and seven-control arithmetic engine implement a nine-register proof search.
The verified blank prefix reaches the prescribed source frame after 44,181 steps.

Consistency of first-order ZF
implies that the machine runs forever and that ZF cannot prove its nonhalting.
Arithmetic Σ₁-soundness of ZF implies that ZF can prove neither halting nor
nonhalting. The independence claim constructs a sentence with the meaning of
blank-tape halting in every ZF model, including models with nonstandard natural
numbers.

- [Paper (PDF)](paper/zf192.pdf), [TeX source](paper/zf192.tex), and [Lean source archive](paper/anc/zf192-lean.zip)
- [Exact machine](data/zf192.tm)
- [Standalone Challenge](ProofSources/ZF192/Challenge.lean) and [Lean Solution](ProofSources/ZF192/Solution.lean)
- [Reproduction](docs/reproduction.md) and [source provenance](docs/provenance.md)

## Lean proof layout

[Support](Support/ZF192Support) contains the reusable definitions and proofs.

- [Coding](Support/ZF192Support/Coding) develops arithmetic, pairing, lists, and histories in models of arithmetic. [Calculus](Support/ZF192Support/Calculus) defines C derivations and their standard and internal versions.
- [Execution](Support/ZF192Support/Execution) compiles C refutations to commands and proves that the register machine implements them. [Machine](Support/ZF192Support/Machine) defines the tape and register program.
- [Logic](Support/ZF192Support/Logic) develops the source calculus and translates it to and from Foundation. [Set theory](Support/ZF192Support/SetTheory) supplies ZF models, ordinal arithmetic on ω, and soundness of the standard C calculus.
- [Independence](Support/ZF192Support/Independence) develops the arithmetization and incompleteness argument. [Palomar](Support/ZF192Support/Palomar) connects the set-theoretic statements to the challenge definitions.

[ProofSources](ProofSources/ZF192) instantiates these results for ZF192.

- [Machine](ProofSources/ZF192/Machine) contains the literal table and verifies startup, decoder traversal, and source control alignment. [Tape](ProofSources/ZF192/Tape) defines finite tape histories and their halting predicates.
- [Simulation](ProofSources/ZF192/Simulation) lifts register execution to tape histories. [Proof](ProofSources/ZF192/Proof) proves standard nonhalting, calibration inside models of ZF, and the Σ₁ transfer.
- [Palomar](ProofSources/ZF192/Palomar) identifies tape halting with the standalone representation. [Solution.lean](ProofSources/ZF192/Solution.lean) assembles the final theorem.
