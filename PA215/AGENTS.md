# Maintaining PA215

Read the [article](README.md), [theorem statements](docs/result.md), and
[reproduction instructions](docs/reproduction.md) before changing the package.

- Preserve the machine bytes, theorem statements, and explicit assumptions.
- Keep both final modules in the default metamathematics build and all four roots in its axiom audit.
- Run `bash scripts/check.sh` for packaging changes. For changes to proofs, imports, or dependencies, build the affected packages and run the axiom audit.
- Keep source identities and license notices accurate. Preserve original validation data verbatim.
- Keep build caches, private files, and experiments outside the publication tree.
- Push, release, or change repository visibility only on the user's instruction.
