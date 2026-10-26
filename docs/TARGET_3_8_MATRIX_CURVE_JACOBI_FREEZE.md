# FROZEN TARGET 3.8 — generic matrix-curve Jacobi logarithmic derivative

**Anchor:** `ZETA_HYPERBOLIC_TARGET_3_8_MATRIX_CURVE_JACOBI_1`  
**Tag:** `_construction` (a compiler-repair candidate, NOT accepted A-Tier in this receiving branch).  
**Exactly one source:** `src/LeanPaper/MatrixCurveJacobi.lean` (Git blob `5dacaee0aae1ef9e17840a0de80e081eff48fbe8`).  
**Base:** `main@c390e38cc9b8f56c7c4446882984f19a5a90e550`, accepted 221 Lean modules after PRs #2 and #3.  
**Lean / Mathlib:** `4.33.0` / `db584cd6d46c92f209a44c0f1c829460d327499d`.

## Donor and exact change

Donor: [snditeration@0cee4ea / Section3/MatrixCurveJacobi.lean](https://github.com/randogelist/snditeration/blob/0cee4ea2e32b1f476488f92b476c4eb224285160/Zetahyperbolic/Section3/MatrixCurveJacobi.lean), blob `d02de6fc9e0734a24ac1b4f4fb26dd9595a262ea`. [Donor CI 40188938699](https://github.com/randogelist/snditeration/actions/runs/40188938699) **FAILED** at line 145, on a `simpa only` proof of the derivative of the affine entry `(G+z•H) i j`; its transitive axiom audit was skipped.

The receiving project already contains [PaperAdvances.Theorem3_8_Jacobi.affineDet_hasDerivAt](../src/LeanPaper/ImportedSection3/Jacobi.lean) in its fully accepted module. Therefore this port:

1. Copies **only the donor's separate generic matrix-curve section**, not the duplicate affine-Jacobi precursor, preserving the donor's generic Leibniz determinant formula and theorem declarations.
2. Replaces the affine reference with the receiving A-Tier prerequisite; changes the singular `simpa only` to `simpa [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, id]` as a **candidate Lean typeclass/elaboration repair**.
3. Adds only four `#print axioms` commands. No external mathematical axiom or new proof field was inserted.

**The repair is unverified.** No Lean compiler is present in this execution environment. The mandatory receiving GitHub Actions run determines whether the generic module compiles.

## Exact target theorem after successful admission

For any finite real matrix curve `F : ℝ → Matrix (Fin n) (Fin n) ℝ` and any real `τ`, assume that every entry is differentiable at `τ` with derivative matrix `H`. Prove:

- `curve_det_leibniz`: determinant derivative is the permutation/finite-product Leibniz directional determinant.
- `directionalDet_eq_trace`: when `det G ≠ 0`, the directional determinant equals `det(G) ⋅ trace(G⁻¹H)`.
- `generic_det_hasDerivAt` and `generic_logDet_hasDerivAt`: at nonsingular `F(τ)`, the determinant and real-log-determinant derivatives equal the trace formulas. (The real logarithm here is differentiated at nonzero determinant, as in Lean's derivative-of-`log|x|` convention.)

**Open original manuscript Theorem 3.8:** no identification of this abstract `F` with the actual *Laplace-deformed odd-zeta Gram integral*, no justified differentiation under that integral and no proof of the actual Christoffel–Darboux polynomial kernel. This is only a reusable finite-dimensional differential bridge, not the printed theorem's closure.

## CI and serialization

This target branch adds exactly one mathematical module, and registers it exactly once in `modules.txt`, `lakefile.toml`, `src/LeanPaper/KernelAudit.lean`, plus this freeze receipt. It must pass the initial **222-module** Lean 4.33.0 project compilation and independent all-constant transitive axiom gate (`AXIOM_AUDIT_ACCEPTED=ALL_PROJECT_DECLARATIONS`; only `propext`, `Quot.sound`, `Classical.choice`). Do not merge if the CI fails. This standalone PR's success on an old main commit is insufficient for combined admission.

Existing pending targets, notably [PR #4 (4.2)](https://github.com/randogelist/zetahyperbolic-axiom/pull/4), [PR #5 (6.10)](https://github.com/randogelist/zetahyperbolic-axiom/pull/5), and the separate 6.9/5.1/3.4/3.3 drafts, are independent. **Do not merge this target ahead of an already queued predecessor without an explicit queue reordering**. After predecessors merge, reconcile this branch against *then-current* main, preserve every accepted module and source hash, and run a fresh complete combined compiler+axiom gate before merging. The combined module count must be measured from current `main` (never guessed from stale receipts).

**No new printed-paper item is yet completed; authoritative whole-item count remains seven of forty-five** until exact manuscript theorem equivalence is proved. No additional target is started in this PR.
