# Busy Beaver independence proofs

These Lean projects verify blank-tape halting statements for explicit binary
Turing machines. Each project page links to its paper, exact transition
table, theorem statement, and reproduction instructions.

| Project | Working states | Theory |
| --- | ---: | --- |
| [PA196](PA196/README.md) | 196 | Peano arithmetic |
| [ZF192](ZF192/README.md) | 192 | First-order ZF |
| [ZF207](ZF207/README.md) | 207 | First-order ZF |
| [ZF209](ZF209/README.md) | 209 | First-order ZF |
| [I3-334](I3-334/README.md) | 334 | ZFC + I3 |
| [I3-380](I3-380/README.md) | 380 | ZFC + I3 |
| [I0-451](I0-451/README.md) | 451 | ZFC + I₀, with additional assumptions involving a Berkeley cardinal |

The ZF and large-cardinal results are conditional. The project statements
spell out the consistency, soundness, and proof assumptions used in each
result.

## Reproduction and Palomar

Use the Lean toolchain and check commands documented in the project you want
to reproduce. The repository-level `scripts/check.sh` covers PA196, ZF192,
ZF207, and ZF209.

I3-334 is a standalone Lake project with bundled proof support and Foundation
sources. Its [reproduction instructions](I3-334/docs/reproduction.md) cover
the build, axiom audit, and Comparator. For Palomar, use project path
`I3-334` and configuration `I3-334/comparator.json` with the full commit SHA.

The repository uses the [MIT license](LICENSE). Vendored libraries retain
their own notices.
