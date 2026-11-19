# Busy Beaver independence proofs

[PA196](PA196/README.md) contains the paper, Lean proof, exact machine data,
and reproduction materials for the 196-state machine independent of PA.
Its existing Palomar submission remains tied to the original submitted commit.

[ZF209](ZF209/README.md) contains the separate 209-state ZF project and paper.
The local build, axiom audit and Comparator passed with Lean and NanoDa.
The local con-ron replay reached its time limit. Palomar submission is pending.

[ZF207](ZF207/README.md) is a separate project for a 207-state machine that
runs the same proof search with a smaller decoder. It reuses the ZF209
development with the table-specific checks redone. The local build, axiom
audit, Comparator (unsandboxed, on macOS) with Lean and NanoDa, and the
bundled con-ron passed. Palomar submission is pending.

PA196 is self-contained under `PA196/`. Its Lean sources are in
`PA196/ProofSources/`; shared tape-engine and arithmetic support are folded
into `PA196.Engine` and `PA196.ArithmeticSupport`. Required support code and
its original declaration namespaces and licence notices are retained.

From the repository root:

```sh
bash scripts/check.sh
bash scripts/check.sh --full
```

See the [paper](PA196/paper/pa196.pdf),
[theorem statements](PA196/docs/result.md), and
[reproduction instructions](PA196/docs/reproduction.md).
PA196's citation metadata is in [CITATION.cff](PA196/CITATION.cff).
Use project path `PA196` for a local Palomar verification of this layout.
ZF209 and ZF207 use project paths `ZF209` and `ZF207`, each with its own
pinned dependencies.
The repository licence is [MIT](LICENSE); vendored support retains its own notices.
