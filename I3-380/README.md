# I3-380

A two-symbol, 380-state Turing machine searches for a finite ground
equational derivation of `D = J`. Its actual blank-tape nonhalting
is equivalent to syntactic consistency of ZFC + I3. Under consistency,
ZFC + I3 cannot prove nonhalting. Under arithmetic Σ₁-soundness, it can
prove neither halting nor nonhalting.

The [paper](paper/i3-380.pdf) by James Chang gives the proof, the
assumptions, and the full transition table. The [LaTeX source](paper/i3-380.tex)
and [literal machine data](data/zfc-i3-native-380.tm) are included.

The standalone [Challenge](ProofSources/Challenge.lean) and
[Solution](ProofSources/Solution.lean) share `PalomarI3380.exactClaim`.
The Solution connects the literal machine to the ground search,
recovers ZFC + I3 from a separating algebra, and constructs the
internal consistency implication used for unprovability. Comparator
checks the full principal theorem with Lean and NanoDa.

[Reproduction](docs/reproduction.md) · [Provenance](docs/provenance.md)
