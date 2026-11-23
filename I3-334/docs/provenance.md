# Provenance

James Chang supplied the exact machine and wrote the [paper](../paper/i3-334.pdf).
Codex assisted with Lean formalization, verification and paper preparation.
The project is covered by the [MIT license](../LICENSE-MIT).

The [literal table](../data/zfc-i3-native-334.tm) has 668 rows. Lean checks the
simulation using the [decoder reference](../data/decoder-reference-344.tm) and
a [direct state correspondence](../ProofSources/I3_334/Simulation/LiteralDecoderRows.lean).

The local [proof support](../Support/I3_334Support) adapts the arithmetic,
machine semantics, and proof transport from the
[I3-380 formalization](https://github.com/jamesyc/BusyBeaver/tree/5928cc3a0ca3fbc548a39074ade7338c77983349/I3-380).
The optimized [Foundation sources](../Vendor/Foundation) are the ZF192
snapshot, with the [upstream Apache-2.0 license](../Vendor/FOUNDATION_LICENSE)
and [source provenance](../Vendor/FOUNDATION_UPSTREAM_PROVENANCE.json)
copied alongside them.
