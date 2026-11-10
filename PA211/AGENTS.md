# Maintaining PA211

Read the [article](README.md), [theorem statements](docs/result.md), and
[reproduction instructions](docs/reproduction.md) before changing the package.

- Preserve the machine bytes, theorem statements, and explicit assumptions.
- Keep the literal PA211 endpoint in the default metamathematics build and all nine roots in its axiom audit.
- Run `bash scripts/check.sh` for packaging changes. For changes to proofs, imports, or dependencies, build the affected packages and run the axiom audit.
- Keep source identities and license notices accurate. Preserve original validation data verbatim.
- Retain the support libraries under their original names. Publish only the PA211 endpoint and machine data.
- Keep build caches, private files, and experiments outside the publication tree.
- Push, release, or change repository visibility only on the user's instruction.
