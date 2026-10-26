# Frozen target 3.3 — genuine shifted solid mixed Hankel minors

**Anchor:** `ZETA_HYPERBOLIC_TARGET_3_3_SOLID_MIXED_MINORS_1`  
**Status:** `_construction`: receiving CI and independent transitive axiom audit outstanding.  
**Donor:** [snditeration/ShiftedMomentPositivity@0cee4ea](https://github.com/randogelist/snditeration/blob/0cee4ea2e32b1f476488f92b476c4eb224285160/Zetahyperbolic/Section3/ShiftedMomentPositivity.lean), original Git blob `100a1b488999e3d5b9c6812cb1b67a42c7cbf51c`.  
**Receiving module:** `src/LeanPaper/ShiftedSolidMinors.lean`, source Git blob `a4bdf2e746f7681b8d685298e4c6c791f8435bce`.  
**Pinned receiving base:** `main@cb1abbe85bb277c823f31468142f7fdae8d0e9ba` (220 existing modules, Lean 4.33.0, pinned Mathlib `db584cd6d46c92f209a44c0f1c829460d327499d`).

## Exact target

The original odd-zeta positive moment measure `ManuscriptChain.ConcreteMoment.momentMeasure p` is **nonzero**, **atomless**, supported in the positive half-line, and has **all moments integrable**, by previously accepted receiving-repo theorems.

This frozen donor port aims to prove:
1. Any **monomial tilt** of this actual measure by `t^a` preserves positive, nonzero atomless measure and integrability.
2. Any finite **sparse principal** shifted monomial moment matrix is positive definite for injectively selected exponents.
3. Every arbitrary-size **solid mixed Hankel minor** formed by consecutive rows starting at `a` and consecutive columns starting at `b` has strictly positive determinant at the actual odd-zeta center.
4. Any translated **same sparse pattern** of rows and columns within the actual finite Gram is likewise strictly positive, subject to the exact index bounds.

**Crucial logical limitation:** This is a valid *partial* 3.3(1) target, not strict positivity of arbitrary mixed minors formed with unrelated gaps, nor Carleman determinacy. The printed whole Theorem 3.3 remains partial.

## Donor repair scope

The original donor [CI 40188938699](https://github.com/randogelist/snditeration/actions/runs/40188938699) **FAILED** in `ShiftedMomentPositivity` at lines 86 and 128: an `ext` tactic attempted to act on a `PosDef ↔ PosDef` proposition, and a coercion mismatch arose between `Matrix.of f` and a matrix-valued function in the translated-sparse determinant.

The receiving source changes only the repository-specific imports, supplies the already-proved actual `Hyperbolic.poleIntegralIdentity` parameter that the receiving `gram_eq_weighted_integral` requires, and replaces those two tactics with explicit matrix equalities. Proof heads are retained and `#print axioms` is added for three important declarations.

**This is a proposed Lean repair, not a claimed PASS.** Require the receiving 221-module CI and full visited-set axiom gate before marking even the narrow clauses as A-Tier.

## Single-target build and merge gate

The branch adds only the one 3.3 proof source; `modules.txt`, `lakefile.toml` and `LeanPaper.KernelAudit.lean` gain exactly one matching module registration each; the other 220 previously accepted mathematical module sources and Mathlib pin are unchanged.

Current accepted `main` already includes merged PR #2 (6.17 finite q-window). Concurrent target PRs #3 (6.16), #4 (4.2), #5 (6.10), #6 (6.9), #7 (5.1) and #10 (3.4 signature precursor) remain separate, with #8/#9 as closure preflight branches. **Do not merge this candidate while prerequisite verification/merge branches would be overwritten or bypassed.** Reconcile it with whatever set of accepted source modules exists on `main` at final merge time, and require a fresh full combined pinned-Lean build, axiom audit `AXIOM_AUDIT_ACCEPTED=ALL_PROJECT_DECLARATIONS`, no `sorryAx` or custom axioms, and original-data correspondence. The simple isolated 221-module CI is necessary but not sufficient after `main` moves.

Only `propext`, `Quot.sound`, `Classical.choice` permitted. The original 45-item count remains **7 complete** pending an exact theorem-by-theorem proof audit; no closure is claimed from this staging action.
