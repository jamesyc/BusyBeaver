# Reproducing the proofs

Run these commands from the repository root. The input checks require
Python 3.10 or later. Proof compilation also requires Git and the Lean
version in `Lean/lean-toolchain`.

## Check the package

```sh
bash scripts/check.sh
```

This checks file hashes, the default import closure, all nine endpoint
audit names, the literal and sparse tables, the arithmetic rows, and the
3,947 source instructions reconstructed from the 173-node Lean tree.
The exact table and source hashes are pinned in the checker.

## Install the dependencies

Install [elan](https://github.com/leanprover/elan) and put its executables
on `PATH`. Then install the pinned toolchain and dependencies:

```sh
elan toolchain install leanprover/lean4:v4.35.0
cd Lean/metamathematics
lake env lean --version
lake exe cache get
python3 scripts/apply_foundation_patch.py
python3 scripts/apply_foundation_functions_patch.py
cd ../..
```

Skip `lake exe cache get` to build external dependencies from source.
The two Foundation repairs are hash-checked and idempotent. The project
support sources already contain their proof repairs.
[Patch specifications](../Lean/metamathematics/patches/README.md)

## Build and audit

```sh
bash scripts/check.sh --full
```

The scheduler submits one project or Foundation module at a time. A clean
build can take several hours and several GiB of memory per large module.

Inspect the order without building:

```sh
python3 Lean/scripts/build_serial.py --metamathematics --list
```

To build the final module and audit its declarations:

```sh
python3 Lean/scripts/build_serial.py --metamathematics --target PA211PA.TwoSidedIndependence
python3 Lean/metamathematics/scripts/check_axioms.py
```

The core physical package has its own eight-root audit:

```sh
bash Lean/scripts/check.sh
```

After the serial build, `lake --rehash build` from either `Lean` or
`Lean/metamathematics` checks that package's default target. Those targets
are `PA211` and `PA211PA`.
[Verification records](validation.md)
