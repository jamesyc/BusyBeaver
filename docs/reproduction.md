# Reproducing the proofs

Run the commands below from the repository root. You'll need Python 3.10 or later
to check the data. To compile the proofs, you'll also need Git and the version
of Lean named in `Lean/lean-toolchain`.

## Check the data

```sh
bash scripts/check.sh
```

The script compares PA213's 426 transition rows and 3,947 source sites with
their Lean representations, checks its relabeling and 519 reviewed module
hashes. It checks file hashes, module imports, and all eight theorem names
in the final axiom audit: the five original roots and the three independence roots.

## Install the proof dependencies

Install [elan](https://github.com/leanprover/elan). Put its executables on
`PATH`. The commands below install Lean, resolve the dependencies in the
checked-in Lake manifest, and apply two patches to Foundation's tactic proofs.
If you want to build external dependencies from source, skip
`lake exe cache get`, which downloads the official Mathlib cache.

```sh
elan toolchain install leanprover/lean4:v4.35.0
cd Lean/metamathematics
lake env lean --version
lake exe cache get
python3 scripts/apply_foundation_patch.py
python3 scripts/apply_foundation_functions_patch.py
cd ../..
```

The patch scripts accept the pinned originals and recognized proof repairs.
They check the input and output hashes and upgrade an older repair using
the preserved original. The 22 project proof
overlays are already applied to the source files.
[Patch specifications](../Lean/metamathematics/patches/README.md)

## Compile and audit

Allow several hours for a build from source. Large modules can take several
GiB of memory each. You'll also need disk space for the toolchain and downloaded
dependencies. The verified build ran on a machine with 32 GiB of memory.

```sh
bash scripts/check.sh --full
```

This runs the data checks, compiles the PA213 metamathematics root, and
checks the transitive axioms of all eight audited theorems. The scheduler
submits one local or Foundation target at a time.

To inspect the build order, run the scheduler with `--list`.

```sh
python3 Lean/scripts/build_serial.py --metamathematics --list
```

To build the final theorem module directly, name it with `--target`.

```sh
python3 Lean/scripts/build_serial.py --metamathematics --target PA213PA.TwoSidedIndependence
```

With the endpoint built, run `python3 Lean/metamathematics/scripts/check_axioms.py`
to check its axioms. To check the core machine library on its own, run
`bash Lean/scripts/check.sh`.

The PA213 final target can also be rechecked with
`lake --rehash build +PA213PA.TwoSidedIndependence` from
`Lean/metamathematics` after the serial build.
[Extended axiom report](../evidence/publication/independence-axioms.txt) · [Original endpoint axiom report](../evidence/publication/endpoint-axioms.txt) · [Frozen build receipt](../evidence/pa213/FINAL_PA_RECEIPT.json)
