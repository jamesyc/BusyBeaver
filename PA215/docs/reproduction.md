# Reproducing the proofs

Run the commands below from the repository root. You'll need Python 3.10 or later
to check the data. To compile the proofs, you'll also need Git and the version
of Lean named in `Lean/lean-toolchain`.

## Check the data

```sh
bash scripts/check.sh
```

The script compares the transition table, search program, and runtime census
with the data in the Lean sources. It checks file hashes, module imports, and
the names of the theorems in the axiom audit.

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

Both patch scripts check the original file hash before writing and verify the
patched hash afterward. If the file already has the patched hash, the script
accepts it. [Patch specifications](../Lean/metamathematics/patches/README.md)

## Compile and audit

Allow several hours for a build from source. Large modules can take several
GiB of memory each. You'll also need disk space for the toolchain and downloaded
dependencies. The verified build ran on a machine with 32 GiB of memory.

```sh
bash scripts/check.sh --full
```

This runs the data checks, compiles the metamathematics root with both theorem
modules, then checks the transitive axioms of all four theorems. The scheduler
submits one local or Foundation target at a time.

To inspect the build order, run the scheduler with `--list`.

```sh
python3 Lean/scripts/build_serial.py --metamathematics --list
```

To build one theorem module at a time, name it with `--target`.

```sh
python3 Lean/scripts/build_serial.py --metamathematics --target PA215PA.MachineNonhaltingV2
python3 Lean/scripts/build_serial.py --metamathematics --target PA215PA.NonhaltingUnprovability
```

With both modules built, run `python3 Lean/metamathematics/scripts/check_axioms.py`
to check their axioms. To check the core machine library on its own, run
`bash Lean/scripts/check.sh`.

[Expected axiom report](../evidence/publication/endpoint-axioms.txt)
