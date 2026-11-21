# Provenance

James Chang is the author of the [paper](../paper/i3-380.pdf) and the
author and maintainer of this formalization. Codex assisted with the
Lean development, proof organization, and preparation of the paper.
The project uses the repository's [MIT license](../../LICENSE).
Vendored Foundation retains its [Apache-2.0 license](../vendor/Foundation/LICENSE).

The Lean proof and local package checks take the [literal table](../data/zfc-i3-native-380.tm)
and [decoder reference](../data/decoder-reference.tsv) as inputs.

The proof uses the limit-rank formulation of I3 described by
[Paul Corazza](https://doi.org/10.4064/fm179-1-4). The Boolean algebra
calculation follows Truszkowska and Grabowski's [ROBBINS2](https://mizar.uwb.edu.pl/JFM/Vol15/robbins2.html),
lemma Lm4. The arithmetic interpretation adapts proof transport and
standard semantics from Chang's earlier work on ZF proof search. The
[Foundation snapshot](../vendor/Foundation/README.md) comes from
PA196's copy of revision `c3eb37a`, with compatibility edits for the
pinned Lean and Mathlib releases.

## Verification record

On macOS with Lean 4.37.0-rc1, the exact-table checks, build of
Challenge and Solution, and axiom audit passed. Stock Comparator,
run in local unsandboxed mode, accepted `PalomarI3380.exactClaim`
with both Lean and NanoDa. Its axioms are `propext`,
`Classical.choice`, and `Quot.sound`. Hosted Palomar verification
is pending.
