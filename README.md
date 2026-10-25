# Leaned Paper

This branch formalizes the supplied 52-page manuscript, *Spectral Theory and Diophantine Bounds for Hankel Determinants of Odd Zeta Values*, using its project sources, pinned cross-repository inputs and newly constructed Lean proofs.

**The manuscript is not completely formalized or ready to be certified as printed.** Theorems and corollaries are tracked by their actual statements, separately from successful compilation. The printed statements of 3.4, 3.5 and 3.6 require correction; quantitative arithmetic and analytic endpoints remain open.

Version `v0_1_4_construction` contains **166 active modules**. All compile under Lean 4.33.0 and pass the independent transitive axiom audit; see the [local acceptance receipt](validation/linux/acceptance.json). All 153 prior mathematical and audit-helper source files are unchanged. The final audit module is extended to include the 12 new modules.

## Manuscript coverage

The [formalization status](docs/FORMALIZATION_STATUS.md) and its [structured companion](docs/formalization_status.json) review all 45 numbered results, with Definition 2.1 and supporting constructions recorded separately. Of the complete printed results, **Theorem 3.1 is newly verified and Proposition 4.3 is retained as verified**. The other 43 comprise 24 partial developments, 16 not formalized and 3 blocked literal statements. These counts concern complete printed statements, not the much larger number of compiled Lean lemmas.

The [45-item ledger](docs/manuscript_45_ledger.csv) preserves manuscript numbering and records exact remaining obligations. A conditional helper, finite-dimensional model, corrected variant or theorem-name wrapper is not counted as a complete manuscript theorem.

## New mathematical proofs

| Development | Exact contribution |
| --- | --- |
| [Rational-function domains](src/LeanPaper/Section2RationalDomains.lean) | μ and τ are independent of polynomial/simple-pole representations, including different supports; their domains are characterized by reduced-denominator divisibility. Lifted linearity and actual rational substitution still need assembly. |
| [Principal-minor rank](src/LeanPaper/PrincipalMinorRank.lean) | Determinant degree and real-root count with multiplicity equal the rank of the actual slope, including singular cases. Interlacing is separate. |
| [Operator-norm disk](src/LeanPaper/OperatorNormDisk.lean) and [primitive theorem](src/LeanPaper/PrimitiveNormDisk.lean) | Identifies the exact radius with the inverse Euclidean operator norm of the whitened matrix and assembles Theorem 3.1 for the actual primitive integer polynomial, including a boundary root. |
| [Higher Turán inequalities](src/LeanPaper/HigherDerivativeTuran.lean) and [normalized Newton inequalities](src/LeanPaper/NormalizedNewton.lean) | All derivative orders, strict Turán away from roots, its equality criterion, and the complete weak Newton hierarchy for ordinary and normalized shifted coefficients. Strict Newton assertions remain separate. |
| [Nearest-root limit](src/LeanPaper/ReciprocalNearestRootLimit.lean) | Corrected finite negative-root bounds and convergence to an attained nearest actual determinant root, with multiplicities allowed. |
| [Logarithmic derivative](src/LeanPaper/ReciprocalLogDerivative.lean) and [second moment](src/LeanPaper/ReciprocalSecondMoment.lean) | Exact first and second derivatives and rational witnesses at rational non-root shifts. Orders three and above remain open. |
| [Manuscript obstructions](src/LeanPaper/ManuscriptObstructions.lean) | The actual root family's Hankel determinant vanishes at order h+1. Separate scalar examples diagnose the printed normalized fraction and odd-order sign errors. |

The [increment provenance](provenance/completion_increment.json) records exact files, imports and compiler evidence. Earlier source intakes remain documented in [the theorem rebuild report](docs/THEOREM_REBUILD_INTAKE.md) and [the snditeration exchange](docs/SNDITERATION_EXCHANGE.md).

## Build and verify

The toolchain is **Lean 4.33.0**. Mathlib is pinned to **`db584cd6d46c92f209a44c0f1c829460d327499d`**, with all transitive dependencies locked in `lake-manifest.json`. The new Lake configuration exposes every active source module under `src/`.

See [BUILD.md](docs/BUILD.md) for standard Linux setup and sequential compilation. The GitHub Actions workflow uses pinned actions, validates the complete module inventory, compiles sequentially and executes the independent audit. Workflow configuration is not itself evidence of a successful remote run; consult the actual Actions run for the commit.

The existing fingerprinted local runner remains unchanged; its setup and command are in [LOCAL_TESTING.md](docs/LOCAL_TESTING.md). The local receipt revalidates compiler, dependencies, source, object and log fingerprints before reusing prior passes.

The offline native Windows workflow is still the single unchanged `run.cmd`, documented in [NATIVE_RUNNER.md](docs/NATIVE_RUNNER.md). Native Windows execution has not been performed here. Linux objects and receipts do not certify Windows compilation.

## Proof integrity and organization

`LeanPaper/` contains manuscript-facing bridges and the new proofs; retained `Paper/`, `PaperChain/`, `ProofAdvances/`, `Zetahyperbolic/` and original root modules preserve their public APIs and source provenance. `modules.txt` is the complete dependency-ordered build plan, ending with `LeanPaper.KernelAudit`.

The audit independently traverses every imported project declaration and its dependencies, including private declarations. Only `propext`, `Quot.sound` and `Classical.choice` are permitted. The active proof scope contains no `sorry`, `admit` or project-specific axioms. Deliberate rejection fixtures under `tests/axiom_walk` are excluded from the active project. See [proof integrity](validation/linux/proof_integrity.json).

An axiom-audit pass checks exact Lean statements; it does not discharge explicit mathematical hypotheses or establish manuscript equivalence. Historical source comments retain their original status language; the current receipts and status report control present claims.

## Remaining mathematical obligations

[Manuscript issues](docs/manuscript_issues.txt) record the literal errors and their separate corrections. Other open work includes rational-functional assembly, continuous real-parameter and character integral constructions, principal interlacing and signature results, strict Newton assertions, all higher reciprocal-moment rationality, and effective spectral, determinant, height and arithmetic estimates. No irrationality, linear-independence or RH conclusion follows merely from the finite Gram results.

The frozen workflow identifiers remain `YOU_ARE_GOODWORKFLOWFRONTIER`, `LEAN_ANCHORINGS`, and `ZETA_HYPERBOLIC_ANCHOR_1` through `ZETA_HYPERBOLIC_ANCHOR_7`.
