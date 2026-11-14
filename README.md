# Busy Beaver independence proofs

[PA196](PA196/README.md) contains the paper, Lean proof, exact machine data,
and reproduction materials for the 196-state machine independent of PA.
Its existing Palomar submission remains tied to the original submitted commit.

The project is self-contained under `PA196/`. Its Lean sources are in
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
The repository licence is [MIT](LICENSE); vendored support retains its own notices.
