# Maintaining the combined BusyBeaver archive

- Treat `PA215/`, `PA213/`, and `PA211/` as frozen historical snapshots. Preserve their relative file paths, machine table bytes, evidence, toolchain locks, and theorem statements.
- The three directories are complete original Git trees. Keep `scripts/verify-snapshots.sh` consistent with the recorded tree hashes if deliberately changing archive policy; do not silently modify historical snapshots.
- Do not deduplicate Lean proof sources across top-level versions. Within a snapshot, modules named after earlier versions may be necessary imports for its proof.
- For a new smaller machine, create a new top-level `PA<number>/` snapshot with its own readme, scripts, Lean tree, and evidence. Update the root index and CI separately.
- Run `bash scripts/verify-snapshots.sh` and `bash PA215/scripts/check.sh`, `bash PA213/scripts/check.sh`, and `bash PA211/scripts/check.sh` before publishing organizational changes. Full Lean builds require the pinned toolchain and dependencies in each snapshot.
- Do not rewrite Git history or merge the archive into another branch without explicit instruction.
