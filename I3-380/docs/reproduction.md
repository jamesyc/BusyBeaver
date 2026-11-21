# Reproducing I3-380

Run from `I3-380/` with elan on `PATH`. The toolchain and Lake
manifest pin Lean 4.35.0 and Mathlib.

```sh
lake exe cache get
bash scripts/check.sh --full
```

The cache download is optional. Running the script without `--full`
checks the exact 760 transition rows and the data and statement copies
used in Lean. Full mode builds the Solution and standalone Challenge
and runs `Audit.lean`. The two intentional Challenge placeholders
are outside the Solution import closure.

On Linux with Bubblewrap and working user namespaces, run the full
statement comparison with the bundled NanoDa on `PATH`.

```sh
export PATH="$(lean --print-prefix)/bin:$PATH"
lake comparator --config comparator.json
```

The local macOS run used `--inadvisably-no-sandbox`. For Palomar,
select project path `I3-380` and config `I3-380/comparator.json`
at the reviewed public commit.

Build the [paper](../paper/i3-380.tex) with
`tectonic --outdir paper paper/i3-380.tex`. The appendix gives the
literal table in packed display form.
