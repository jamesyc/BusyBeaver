# Provenance

James Chang is the author and maintainer. The Lean formalization was developed
with assistance from ChatGPT and accompanies the [ZF209 paper](../paper/zf209.pdf).
The project is [MIT licensed](../../LICENSE).

The tape engine builds on work by [Elliot Glazer](../ProofSources/M6/Zip.lean)
and [Jeff Ketchersid](../ProofSources/M6/Native.lean). ZF209 vendors
[Foundation](../Vendor/FOUNDATION_LICENSE) from two revisions:
[122 modules from `b2d8f55`](../VENDORED_FOUNDATION_HASHES.json), including a
[documented performance patch](../provenance/FOUNDATION_PATCHES.json), and
[39 from PA196's copy of `c3eb37a`](../provenance/FOUNDATION_FROM_PA196.json).

## Verification record

The local build, axiom audit, and Comparator checks with Lean and NanoDa passed.
The local con-ron replay timed out. Hosted Palomar verification is pending.
