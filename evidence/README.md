# Verification records

| Record | What it contains |
|---|---|
| [Endpoint axiom report](publication/endpoint-axioms.txt) | The axioms Lean found by following each of the four PA215 theorems through its dependencies. |
| [Nonhalting source build](nonhalting/CLEAN_SOURCE_RESULT.json) and [module identities](nonhalting/PROJECT_SOURCE_OUTPUT_IDENTITIES.json) | Hashes of the sources and compiled outputs for the 1,060 project modules used by the conditional nonhalting theorem. |
| [Modular kernel check](nonhalting/SUCCESSOR_RESULT.json) | Kernel replay results for the nonhalting theorem and its dependencies, covering 4,030 modules. |
| [Unprovability theorem output](unprovability/final-replay.log) | Lean's printout of the internal PA implication, the unprovability corollary, and the axioms each uses. |

The [file manifest](source-manifest.json) lists the package files and their SHA-256 hashes. The [verification summary](../docs/validation.md) explains how to
interpret the results.
