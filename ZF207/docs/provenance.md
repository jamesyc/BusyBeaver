# Provenance

James Chang is the author and maintainer. The Lean formalization accompanies
the [ZF207 paper](../paper/zf207.pdf) and is the [ZF209](../../ZF209/README.md)
formalization, developed with assistance from ChatGPT, adapted to the
207-state table with assistance from Claude Code. The project is
[MIT licensed](../../LICENSE).

James Chang designed the 207-state table in
[`data/zf207.tm`](../data/zf207.tm) and the decoder comparison in
[`scripts/compare_zf209.py`](../scripts/compare_zf209.py).

Relative to ZF209, the table-specific parts were replaced:

- [`M207/Literal.lean`](../ProofSources/M207/Literal.lean): the table and the
  renumbering between native engine states and table labels. Labels outside
  the decoder keep ZF209's native numbers.
- [`M207/Startup/`](../ProofSources/M207/Startup): the chunked startup run,
  regenerated for the 207-state table. It reaches the same clean frame as
  ZF209's after 58,616 steps instead of 58,154.
- The state count, row count and halt label in the Challenge, the history
  definitions and the row lemmas.

The per-instruction simulation checks in `M207/CheckedCoverage/` are textually
ZF209's and are re-evaluated against the new table. Identifiers containing
`209` that name the machine were renamed to `207`.

The tape engine builds on work by [Elliot Glazer](../ProofSources/M6/Zip.lean)
and [Jeff Ketchersid](../ProofSources/M6/Native.lean). ZF207 vendors
[Foundation](../Vendor/FOUNDATION_LICENSE) from two revisions:
[122 modules from `b2d8f55`](../VENDORED_FOUNDATION_HASHES.json), including a
[documented performance patch](../provenance/FOUNDATION_PATCHES.json), and
[39 from PA196's copy of `c3eb37a`](../provenance/FOUNDATION_FROM_PA196.json).

## Verification record

Run on 18 November 2026 on macOS (Apple silicon), Lean 4.35.0:

- `bash scripts/check.sh --full` passed: source preflight, build of Solution
  and Challenge, and the axiom audit of all nine declarations in `Audit.lean`
  (only `propext`, `Classical.choice` and `Quot.sound`).
- `lake comparator --config comparator.json` passed, with NanoDa and Lean's
  default kernel accepting the Solution export. Bubblewrap is unavailable on
  macOS, so this run used `--inadvisably-no-sandbox`.
- The toolchain's bundled con-ron accepted the 34,414 exported declarations
  in `--verified` mode. Palomar pins a different con-ron build (see
  [reproduction](reproduction.md)).
- `scripts/compare_zf209.py` passed.

Sandboxed Comparator on Linux and hosted Palomar verification are pending.
