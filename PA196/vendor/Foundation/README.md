# Foundation

These Lean modules come from [FormalizedFormalLogic/Foundation][foundation]
at revision [c3eb37a][revision]. The included modules supply first-order
arithmetic and proof support. The local changes are confined to proof
performance and Lake configuration. They preserve the definitions and theorem statements of
the affected declarations.

The package omits the unused `doc-gen4` and `Forgive` dependencies and their
documentation-only transitive dependencies. The retained source modules are
all on PA196's import paths; their upstream attribution and licences are unchanged.

Foundation is distributed under the [Apache License, Version 2.0](LICENSE).
See [Foundation's citation](CITATION.cff) for attribution.

[foundation]: https://github.com/FormalizedFormalLogic/Foundation
[revision]: https://github.com/FormalizedFormalLogic/Foundation/tree/c3eb37ae896dc8f1d239ba1511e74d9f25e9d158
