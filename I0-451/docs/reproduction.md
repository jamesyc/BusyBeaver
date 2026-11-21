# Reproducing I0-451

Run from `I0-451/` with Lean 4.35.0 and Python 3.10 or later.

```sh
lake exe cache get                  # Optional Mathlib cache
bash scripts/check.sh --full
```

Without `--full`, the script checks the original table bytes, the named-to-numbered
alignment, and the generated Lean tables and Challenge. The full command
also compiles the Solution and Challenge and checks `Audit.lean`. Lake uses
one worker thread and a 1,536 MiB cap per Lean process.

Run Comparator on Linux with Bubblewrap and working user namespaces.

```sh
export PATH="$(lean --print-prefix)/bin:$PATH"
lake comparator --config comparator.json
```

Comparator checks `I0451.Standalone.exact451Claim` and four named formula
values. The configuration enables NanoDa. Challenge placeholders are
confined to the standalone statement and the Solution has its own imports.
[Palomar requirements](https://github.com/PalomarRegistry/PalomarPolicy/blob/main/CONTRIBUTING.md)

Build the paper with Tectonic. An external output directory keeps the build
products out of the source tree.

```sh
paper_build=$(mktemp -d)
tectonic --outdir "$paper_build" paper/i0-451.tex
```

For hosted preflight, select project `I0-451` in the repository's Palomar
workflow on the exact pushed commit. The Comparator path is
`I0-451/comparator.json`. [Palomar preflight instructions](https://submit.palomar-registry.org/llms.txt)
