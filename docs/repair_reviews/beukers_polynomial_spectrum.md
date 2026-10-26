> **Final receiving verification:** All registered Lean sources discussed here are included in the 263-module [GitHub CI PASS](https://github.com/randogelist/zetahyperbolic-axiom/actions/runs/40339809027) at proof commit `cdcb1935aa73a7c7e65006c1c198d114e9dcc6db`, with a fresh all-project transitive axiom audit and negative regressions. See the [matching receipt](../../validation/github/20261026-prime/acceptance.json) and [current whole-result status](../FORMALIZATION_STATUS.md). References below to candidates, pending CI or failed runs describe historical investigation checkpoints; compilation does not extend the exact mathematical scope recorded here.

# Actual polynomial Beukers spectrum construction

## Source and status

New module: `src/LeanPaper/BeukersPolynomialSpectrum.lean`.

Dependencies: `LeanPaper.BeukersIntegralPencil` and `LeanPaper.Section5RationalIndependence`. Root owns registration and GitHub CI. Source/API review and whitespace checks completed; receiving compilation and axiom audit remain pending. No local Lean or Lake execution occurred.

## Underlying missing bridge

The existing finite spectral theorem uses a matrix of rational polynomial coefficients and the algebraically defined `Real.dualDelta`. The newly constructed analytic module identifies finite coefficient sums with actual density integrals. A direct theorem about the actual rational polynomials and their actual weighted-measure integral matrix still needed an explicit truncation/evaluation bridge and a proved equality of the integral-defined affine pencil with the rational pencil.

## Construction made

1. `coefficientEval_polynomialCoefficients`: the coefficients through `K` evaluate to the actual polynomial whenever its natural degree is at most `K`, using the pinned polynomial evaluation-over-range theorem.
2. `polynomial_integrable`: actual polynomial products are integrable under the constructed `beukersMeasure`. This prevents reliance on the default zero value for nonintegrable Bochner integrals.
3. `polynomialIntegralMatrix`: defines the entries by actual polynomial evaluations integrated against `beukersMeasure`.
4. `polynomialIntegralMatrix_eq_dualEntry`: proves those entries equal evaluation of the actual rational dual entry at zeta(7).
5. `integralPolynomialPencil`: defines the affine polynomial matrix from that integral matrix plus `(X−zeta(7))` times the coefficient-Gram slope.
6. `integralPolynomialPencil_eq_dualEntry`: identifies this integral-defined matrix with the coefficientwise real embedding of the rational dual pencil. Thus the zeta contributions cancel in its affine coefficients by proof, not by definition or assumption.
7. `integralPolynomialPencil_derivative` and `polynomial_slope_posDef`: identify the derivative with the actual coefficient Gram matrix and prove strict positivity from rational polynomial independence, without a separate real-independence hypothesis.
8. `integralPolynomialDeterminant_eq` and `integral_polynomial_hyperbolicity`: transfer exact degree `h` and reality of every complex root to the determinant defined by actual polynomial integrals.

## Exact hypotheses and boundary

The spectral endpoint quantifies over every family `A : Fin h → ℚ[X]`, with `LinearIndependent ℚ A` and `∀ i, (A i).natDegree ≤ K`. No positivity of the Beukers bilinear form is assumed; only the derivative coefficient-Gram matrix is proved positive. The theorem includes all finite dimensions allowed by these hypotheses and therefore includes the printed finite setup `K ≥ h ≥ 1`.

The integral moment identification itself requires only the degree cutoff, not independence. Existing original theorem statements and the original manuscript remain unchanged.

This construction does not prove the infinite-dimensional Krein decomposition or the prescribed polynomial cone construction in 5.2(2)–(3), and does not assert an irrationality measure. It supplies the actual analytic-to-algebraic bridge for the finite positive-slope spectral result.

## First receiving compilation: CI4 follow-up

CI4 first reached this module after `Section5RationalIndependence` passed. It found two elaboration/rewrite details: the generic finite-index sum lemma was not selected by `simp`, and the affine-pencil simplifier would not unfold the semireducible `Matrix` type when checking the coefficient family argument against a function-family API. The coefficient-evaluation proof now applies the explicitly instantiated `Fin.sum_univ_eq_sum_range` equality. The pencil proof introduces the actual coefficient family with its explicit function type, changes to that definitionally equal affine expression, and then applies the same polynomial evaluation/map identities. No hypotheses, conclusions, polynomial families, or integrals were changed. The receiving compile and audit for these two proof corrections remain pending.
