# Provenance

James Chang is the author and maintainer. Codex assisted with the Lean
formalization, review, and manuscript. The project is MIT licensed.
[Paper](../paper/i0-451.pdf) · [License](../../LICENSE)

The package includes the exact 451-state transition table and its named
counterpart before numbering and totalization.
[Literal table](../data/zf-berkeley-451.tm) · [Named table](../data/final-451.named.tm)

The construction uses the proof-search engine and compiler from Jeff
Ketchersid's repository at the revision below. The generator notice credits
Andrew James Wade.
[Compiler and search engine](https://github.com/jeff87654/busy-beaver/tree/cde3649e0f1f3ae57454be7a5bed8bf19f8115d7)
· [Generator license](https://github.com/jeff87654/busy-beaver/blob/cde3649e0f1f3ae57454be7a5bed8bf19f8115d7/ZF/generator/LICENSE.wade)

The Lean files reuse the arithmetic interpretation and general logical
libraries from ZF207. The 164 vendored Foundation modules retain their
original names and Apache 2.0 license.
Three proof-only patches inherited from ZF207 shorten independent replay.
[Foundation revision](https://github.com/FormalizedFormalLogic/Foundation/tree/b2d8f55e995dede4fdb809423bb4e83f55c14446)
· [Patch record](../Vendor/FOUNDATION_PATCHES.json)
· [Foundation license](../Vendor/FOUNDATION_LICENSE)

## Verification record

On 20 November 2026, Lean 4.35.0 built the Solution and Challenge. The axiom
audit reported only `propext`, `Classical.choice`, and `Quot.sound` for the
core and standalone theorems. Comparator passed with Lean's kernel and
NanoDa on macOS without Bubblewrap. The bundled Con-Ron accepted all 25,613
declarations in the same Solution export in verified mode.
[Reproduction](reproduction.md)
