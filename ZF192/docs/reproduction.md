# Reproducing ZF192

Run the commands from `ZF192/` with the pinned Lean toolchain.

```sh
lake exe cache get
LEAN_NUM_THREADS=6 bash scripts/check.sh --full
```

The source check verifies the exact table, contextual source data, paper appendix,
and standalone Challenge.
Full mode builds both entry points and checks the axiom audit. The per-process
Lean limit is 1,536 MiB with one worker. The Lean kernel checks the literal
startup, decoder windows, and control alignment.

Run Comparator on Linux with Bubblewrap and user namespaces for the sandboxed
comparison and NanoDa replay.

```sh
lake comparator --config comparator.json
```

Use project path `ZF192` and configuration path `ZF192/comparator.json` for a
future Palomar submission of the reviewed public commit. No command here submits
a result.

Lean replays the blank-tape startup in five intervals over packed tape
words. The evaluator derives its packed table from the literal rows and
Lean checks its correspondence with the ordinary tape semantics.

Build the standalone paper with Tectonic.

```sh
tectonic --outdir paper paper/zf192.tex
```
