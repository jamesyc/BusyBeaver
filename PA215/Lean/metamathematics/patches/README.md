# Foundation proof patches

Both patches apply to Foundation commit
`c3eb37ae896dc8f1d239ba1511e74d9f25e9d158` with Lean 4.35.0. To reduce memory use, the patched tactics rewrite formula substitution
explicitly before running the simplifier. The patches preserve the declaration
statements and mathematical definitions.

| File | Declaration |
|---|---|
| [Term/Basic patch](foundation-term-basic.patch) | `IsUTerm.BV.construction.func_defined` |
| [Term/Functions patch](foundation-term-functions.patch) | `TermSubst.construction.bvar_defined` |

Once the pinned dependencies are installed, run these commands from
`Lean/metamathematics`.

```sh
python3 scripts/apply_foundation_patch.py
python3 scripts/apply_foundation_functions_patch.py
```

The Basic script checks the original SHA256
`011d4e6c7d222628926ef327104ee6ef4dd683ed4a8447f8379a6752c61e78ec` and
verifies patched SHA256
`6b700dc6ea4ea8d60bb17b7d681c46e1ac53ce52a37f5be5b84e4d033c5bb31e`.
You can rerun either script on a file with the expected patched hash.
[Term/Functions hashes](TERM_FUNCTIONS.md) · [Dependency license](../../licenses/Foundation-Apache-2.0.txt)
