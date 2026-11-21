# Maintaining the proof packages

Read the [paper](PA196/paper/pa196.tex), [theorem statements](PA196/docs/result.md), and
[reproduction instructions](PA196/docs/reproduction.md) before changing the package.

- Preserve the machine bytes, theorem statements, and explicit assumptions.
- Keep the literal PA196 proof in the default build and both compared declarations in the axiom audit.
- Run `bash scripts/check.sh` for packaging changes. For changes to proofs,
  imports, or dependencies, build the affected targets and run the axiom audit.
- Keep source identities and license notices accurate. Preserve original validation data verbatim.
- Retain the required support libraries under their original names. Publish
  only the PA196, ZF209, ZF207 and I3-380 papers, proofs, machine data, and reproduction materials.
- PA196 is a separate Lake project under `PA196/`. Its shared engine and
  arithmetic support live under `ProofSources/PA196/Engine` and
  `ProofSources/PA196/ArithmeticSupport`; preserve their declaration namespaces.
- Keep build caches, private files, and experiments outside the publication tree.
- ZF209 is a separate Lake project under `ZF209/`. Preserve its standalone
  Challenge, exact machine bytes, and explicit consistency/soundness assumptions.
  Keep the per-process memory cap and audit the final compared declaration.
  Batch proof-family changes before compiling; independently replay the final proof.
- ZF207 is a separate Lake project under `ZF207/`, derived from ZF209 with the
  table, state renumbering, startup run and row-count lemmas replaced. The
  same rules as ZF209 apply. Regenerate `paper/machine-table.tex` with
  `scripts/machine_table.py`; keep `scripts/compare_zf209.py` passing.
- I3-380 is a separate Lake project under `I3-380/`. Keep the literal
  380-state table, standalone Challenge, and explicit consistency and
  arithmetic soundness assumptions. Run `bash scripts/check.sh --full`
  from `I3-380/` for proof changes, and use `comparator.json` to compare
  `PalomarI3380.exactClaim`. Keep the paper's appendix synchronized with
  `data/zfc-i3-native-380.tm` and preserve the decoder reference data.
- Push, release, or change repository visibility only on the user's instruction.
