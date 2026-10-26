# Frozen target 5.2(1): rational-polynomial independence to real dual hyperbolicity

**Anchor:** `ZETA_HYPERBOLIC_TARGET_5_2_RATIONAL_POLYNOMIAL_INDEPENDENCE_1`  
**State:** `_construction` — isolated Lean port, compiler and independent axiom audit NOT YET VERIFIED.

## Immutable source provenance

- Upstream donor: [snditeration/Section5/RationalIndependence.lean at 0cee4ea](https://github.com/randogelist/snditeration/blob/0cee4ea2e32b1f476488f92b476c4eb224285160/Zetahyperbolic/Section5/RationalIndependence.lean), Git blob `3355b5ad478b6178379df74d7df78f41cf80012a`.
- Upstream CI: [failed run 40188938699](https://github.com/randogelist/snditeration/actions/runs/40188938699). That module failed at **lines 28, 41**; final all-declaration axiom gate was skipped. **No A-Tier admission transferred from that run.**
- Receiving source: `src/LeanPaper/Section5RationalIndependence.lean`, Git blob `ba40e1cf2c0531af573648c026b730859c090f75`; imported into current [main@54136b39](https://github.com/randogelist/zetahyperbolic-axiom/commit/54136b39ec280b200c108ee48e80a5c247b1fa6b) with 222 already accepted Lean modules (219 initial plus target 6.17, 6.16 and 4.2). Pin: Lean `v4.33.0`, Mathlib `db584cd6d46c92f209a44c0f1c829460d327499d`.
- Source port is **not byte-identical**: import/namespace changed to reference `LeanPaper.Section5DualSpectrum`; donor line 28 uses obsolete `Matrix.isUnit_iff_isUnit_det.mp`, replaced with `ne_of_gt hqpd.det_pos`; donor line 41 had a reversed `map_det` rewrite, replaced with `rw [hmap, (Rat.castHom ℝ).map_det]`. A `#print axioms` command was added. These candidate repairs **must be validated by receiving CI**, not asserted to compile now.

## Exact mathematical target

Prove, for arbitrary (h,K), that:

1. rational coefficient-row multiplication `Matrix.vecMul` being injective implies real `coefficientRowsSeparate` after the `ℚ → ℝ` cast via the exact rational Gram determinant;
2. `LinearIndependent ℚ c.row` therefore forces the **actual dual rational pencil** `Real.dualDelta s c` to have full degree `h` and only real complex roots;
3. `LinearIndependent ℚ A` for a finite family of actual rational polynomials of degree ≤`K` implies rational coefficient-row independence for their truncated monomial coefficient matrix;
4. applying these to the manuscript dual exponent `s=7` yields the precise finite-dimensional 5.2(1) spectral conclusion.

All these are conditional on the **explicit actual rational-polynomial linear independence and degree bound**, not an unproved assertion that every manuscript-chosen polynomial family satisfies them. The **analytic actual two-variable Beukers measure**, infinite-dimensional Krein cones and `ζ(7)` irrationality transfer remain separate open endpoints. Do not promote the entire manuscript Theorem 5.2 to A-Tier on this result alone.

## Minimal branch/diff gate

This branch adds **one** mathematical theorem file and **only** its required registrations in `modules.txt`, `lakefile.toml`, and `src/LeanPaper/KernelAudit.lean`, plus this freeze receipt. The 222 accepted mathematical sources are otherwise frozen.

Initial CI must compile 223 modules in Lean 4.33.0 and prove `AXIOM_AUDIT_ACCEPTED=ALL_PROJECT_DECLARATIONS` with only `propext`, `Quot.sound`, `Classical.choice`. This is **only an isolated test**, not permission to merge if `main` has advanced.

**Merge order:** existing frozen queue PR #5 (6.10), #6 (Hermite 6.9), #7 (Beukers 5.1), #10 (3.4 signature), #12 (3.3 solid minors), #14 (3.8 Jacobi), and their narrowly scoped repair dependencies must be independently resolved first, unless the user explicitly reorders them. This 5.2 target is to remain **DRAFT** while prerequisites are pending. After reconciliation with the exact then-current `main`, rerun a fresh combined Lean/axiom audit on the complete actual module count and **only then** mark ready and merge with expected branch-head SHA.

**No proof construction beyond this one 5.2(1) target is requested or claimed by this branch.**
