# Source provenance

James Chang authored the ZF192 construction and paper proof with assistance from ChatGPT.
The Lean build checks the startup checkpoint directly from the [literal table](../data/zf192.tm).

The working-state labels are 0 through 191 and the halt label is 192. The
SHA-256 of the 384-row table is
`be1db915a6f40e37a601d3cb54bc0cf0d9597bdf0c75e97098cf4c201c6d5585`.

The Lean proof uses a [list-based binary tape](../Support/ZF192Support/Machine/BinaryTape.lean)
to replay and reason about the literal table. The module records the origin
of the adapted tape code. Vendored Foundation retains its upstream names and
licence, with revision and patch manifests alongside it. The project sources
use the repository MIT licence.

The exact 44,181-step blank run reaches control 157 at the prescribed
contextual source site 22. The head is at coordinate −121. The register
values are (2, 0, 0, 0, 0, 0, 0, 0, 0), the gap is 86, and the tape has
186 ones. The arithmetic proof applies to any PA model and preserves
the blank file exterior. The linear order of the 3,037 arithmetic and
halt sites determines the alignment with the verified source compiler.
Lean checks the matched operations and their successors after
unconditional jumps, as well as the decoder and return interfaces.

The contextual codebook and scalar graph are retained in [source.json](../data/source.json).
Their SHA-256 is
`8c258c075daf5e37cea26129d4273b5c1dd12cd4e9d8fc206dde6704bd5f9771`.

The compared claims use halting equivalence with the source on the standard
tape and an internal implication from source-calculus refutations to physical
halting. The full reverse implication for nonstandard histories lies outside
the scope of this development.
