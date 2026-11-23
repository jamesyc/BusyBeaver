# Reproduction

Run from `I3-334/` with elan on `PATH`. Lake uses the pinned Mathlib dependency
and builds the bundled Foundation and support libraries from source.
The folder can be copied and built independently of the repository’s
other proof packages.

```sh
lake exe cache get
bash scripts/check.sh
```

The cache download is optional. The script checks the literal table
and reference data, verifies the generated Lean declarations and
paper table, builds the package, and runs the [axiom audit](../Audit.lean).

Compare the full independence theorem with the standalone Challenge.

```sh
export PATH="$(lean --print-prefix)/bin:$PATH"
lake comparator --config comparator.json
```

The local macOS run used `--inadvisably-no-sandbox` and enabled
NanoDa. For [Palomar](https://palomar-registry.org/how-to-submit),
the project path is `I3-334` and the configuration is
`I3-334/comparator.json`. The
[startup configuration](../comparator-startup.json) compares the
table binding and the startup trace separately.

Regenerate the paper's table with `python3 scripts/literal.py`.
Build the paper with `tectonic --outdir paper paper/i3-334.tex`.
