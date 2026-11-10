# Busy Beaver: Turing machines independent of Peano arithmetic

This repository archives three explicit binary Turing machines with **215, 213, and 211 working states**. Each machine starts on a blank, two-way-infinite tape and searches for a proof of a contradiction in ordinary first-order Peano arithmetic (PA). Their Lean proof packages connect the published transition tables to that search and formalize statements about nonhalting and PA independence.

The versions are kept as **complete, separate snapshots**, not a shared, evolving Lean project. This preserves the exact sources, dependency manifests, proof evidence, and instructions associated with each result.

| Version | Working states | Transition rows | Formal result | Reproduce |
| --- | ---: | ---: | --- | --- |
| [PA215](PA215/README.md) | 215 | 430 | Nonhalting and PA-unprovability, conditional on PA consistency | `bash PA215/scripts/check.sh` |
| [PA213](PA213/README.md) | 213 | 426 | Two-sided PA independence, with the consistency and truth prerequisites discharged in Lean's metatheory | `bash PA213/scripts/check.sh` |
| [PA211](PA211/README.md) | 211 | 422 | Two-sided PA independence, with the consistency and truth prerequisites discharged in Lean's metatheory | `bash PA211/scripts/check.sh` |

These are distinct published machines, not the number of Lean modules or source-level search instructions. In particular, PA215's original result did **not** claim the same unconditional two-sided independence theorem later established for PA213 and PA211.

## Explore the versions

Each version directory contains its original:

- `README.md`, `AGENTS.md`, `CITATION.cff`, and publication metadata;
- `Lean/` packages, data (including the exact machine table), scripts, and pinned toolchain/dependency manifests;
- `docs/`, `evidence/`, and `scripts/` folders, including available verification records;
- other files present in that historical commit, kept under their original relative paths.

Some recent Lean packages contain support modules named `PA213` and `PA215`. These modules belong to the snapshot containing them; they must not be replaced with files from another top-level version directory.

The quick checks above verify publication package integrity without requiring a Lean build. With each snapshot's pinned toolchain and dependencies installed, use `bash PA215/scripts/check.sh --full`, `bash PA213/scripts/check.sh --full`, or `bash PA211/scripts/check.sh --full` for the corresponding Lean build and axiom audit. See each version's `docs/reproduction.md` for further details.

## Provenance

| Snapshot | Original commit | Original Git tree |
| --- | --- | --- |
| PA215 | [`eccd1b0`](https://github.com/jamesyc/BusyBeaver/commit/eccd1b006e951bad1ed03efd627cab548c743194) | `2456a82396242f8eb44231145a0e7f0efc0b8b7e` |
| PA213 | [`b42d9ff`](https://github.com/jamesyc/BusyBeaver/commit/b42d9ffe1aee8e074bff2359aba4c5f07adc5293) | `37e0440ebc7a38cea565cce1202043d68f3cdc7d` |
| PA211 | [`1654314`](https://github.com/jamesyc/BusyBeaver/commit/1654314dd6892371ea38e488a7aa501d2aa55a0c) | `8c23186eef0b05e760421c0903cdb3acdfc7f331` |

The archive directories are direct references to those historical Git trees, so the bytes and paths within them match their source commits exactly. Run `bash scripts/verify-snapshots.sh` from a Git checkout to verify their tree hashes. The root CI runs that check and each version's fast publication checks.

For citations, prefer the `CITATION.cff` in the specific version folder and identify its original commit. This root describes the combined archive.
