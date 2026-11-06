# Toolchain

Both packages use `leanprover/lean4:v4.35.0` (Lean commit
`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`). The metamathematics package
pins Foundation at `c3eb37ae896dc8f1d239ba1511e74d9f25e9d158` and Mathlib at
`56a005855ea17e0b0958f73ec801ae140b0a1679`. The
[Lake manifest](metamathematics/lake-manifest.json) lists the versions of the
packages they depend on. The core machine package depends only on the Lean toolchain.

[Lean release](https://github.com/leanprover/lean4/releases/tag/v4.35.0) · [Setup and verification](../docs/reproduction.md)
