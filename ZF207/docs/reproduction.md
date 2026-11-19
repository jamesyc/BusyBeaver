# Reproducing ZF207

Run from `ZF207/`, using Lean 4.35.0 and the committed Lake manifest:

```sh
lake exe cache get
LEAN_NUM_THREADS=6 bash scripts/check.sh --full
```

The cache download is optional. `check.sh` without `--full` performs source,
licence-manifest, import, and exact-machine checks. The full mode also builds
the Solution and Challenge and checks every declaration in `Audit.lean`.
Only `propext`, `Classical.choice`, and `Quot.sound` are allowed. The single
intentional Challenge placeholder is excluded from the Solution imports.

The Lake configuration caps each Lean process at 1536 MiB and one worker
thread. Independent modules can build concurrently. A clean build of the
package, with Mathlib's cached build, took about 21 minutes on a ten-core
Apple silicon machine; the largest Lean process used 1.2 GB. Keep build caches and logs outside the source package. No native evaluation
axiom is used.

Run the stock statement comparison and NanoDa replay on Linux with Bubblewrap
and working user namespaces.

```sh
bwrap --unshare-user --ro-bind / / true
lake comparator --config comparator.json
```

Palomar additionally
supplies its protected independent-checker configuration. Its pipeline revision
`14aa8d6b3c2f14a8540605e37144560b9a00e7e7` pins con-ron from Lean 4.36.0-rc1
for Lean 4.35.0 submissions; the bundled 4.35.0 con-ron is not that checker.
Compilation, axiom inspection, statement comparison, NanoDa replay, and
con-ron replay are separate checks.

To typeset the paper, run `pdflatex` twice in `paper/`, supplying an output
directory outside the repository for auxiliary files.
`python3 scripts/machine_table.py` regenerates the appendix table
`paper/machine-table.tex` from the exact rows in `data/zf207.tm`.

`python3 scripts/compare_zf209.py` reruns the exhaustive comparison of the
ZF207 and ZF209 decoders described in the paper. It reads
`../ZF209/data/zf209.tm` and is not part of the Lean proof.

For a future Palomar submission, use project path `ZF207` and the reviewed,
pushed full commit SHA. No submission is made by these scripts.
