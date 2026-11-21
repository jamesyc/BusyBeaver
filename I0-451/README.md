# I0-451

A Lean formalization of conditional independence for the exact 451-working-state
binary Turing machine. State 0 starts on an all-zero doubly infinite tape. Label
451 is the unique halt state. The original transition table is in
[`data/zf-berkeley-451.tm`](data/zf-berkeley-451.tm).

Let B be ZF plus “there is a Berkeley cardinal” and T be ZFC plus I₀. The
conditional result assumes consistency of B, arithmetic Σ₁-soundness of T,
and a B-proof of the consistency sentence for the Craig presentation of
T's arithmetic consequences. Under these hypotheses the machine never
halts, and neither its halting nor its nonhalting is provable in T.
Both unprovability results also hold in ZF with the same I₀ axiom.

For unprovability of nonhalting alone, consistency of T and the B-proof
of this exact consistency sentence suffice. The paper explains the
relationship to the relative consistency theorem attributed to Woodin,
including the internal transfer that would be needed to discharge the
premise from its usual formulation.
[Paper (PDF)](paper/i0-451.pdf) · [LaTeX source](paper/i0-451.tex)

The proof connects the literal tape to a native proof calculus in standard
and nonstandard arithmetic models. It identifies the emitted set-theory axiom
with the Berkeley cardinal axiom over ZF. The native calculus represents
proofs in B, and a coded refutation of the effective arithmetic presentation
can be carried to the literal tape. The relative consistency premise then
gives the Gödel II step.

The main Lean theorem is [`I0451.exact451_independence`](ProofSources/I0451/Independence.lean).
The standalone membership-model statement is
[`I0451.Standalone.exact451Claim`](ProofSources/Challenge.lean).
[Reproduction](docs/reproduction.md) · [Provenance and verification](docs/provenance.md)
