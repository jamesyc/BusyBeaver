# Foundation proof patches

The PA211 build uses two reviewed repairs to Foundation commit
`c3eb37ae896dc8f1d239ba1511e74d9f25e9d158` with Lean 4.35.0.
They add generic substitution lemmas and use them in two syntax proofs.
The preserved originals, patches, and exact hashes are in
[the Foundation overlay manifest](MANIFEST.json).

| File | Proof field | Patch |
|---|---|---|
| Term/Basic | `IsUTerm.BV.construction.func_defined` | [Basic patch](foundation-term-basic.patch) |
| Term/Functions | `TermSubst.construction.bvar_defined` | [Functions patch](foundation-term-functions.patch) |

Once the pinned dependencies are installed, run this command from
`Lean/metamathematics`.

```sh
python3 scripts/apply_foundation_patch.py
python3 scripts/apply_foundation_functions_patch.py
```

The scripts accept the pinned originals and recognized proof repairs.
Each checks its input hash, applies the patch to a temporary copy of the
preserved original, verifies the output hash, and atomically installs the
repair. Rerunning either on its reviewed version succeeds immediately.
[Dependency license](../../licenses/Foundation-Apache-2.0.txt)

The 22 project proof overlays are already applied in the supporting sources.
Their original files and diffs are preserved alongside
[the project overlay manifest](../../proof_overlays/MANIFEST.json).
