> **Final receiving verification:** All registered Lean sources discussed here are included in the 263-module [GitHub CI PASS](https://github.com/randogelist/zetahyperbolic-axiom/actions/runs/40339809027) at proof commit `cdcb1935aa73a7c7e65006c1c198d114e9dcc6db`, with a fresh all-project transitive axiom audit and negative regressions. See the [matching receipt](../../validation/github/20261026-prime/acceptance.json) and [current whole-result status](../FORMALIZATION_STATUS.md). References below to candidates, pending CI or failed runs describe historical investigation checkpoints; compilation does not extend the exact mathematical scope recorded here.

# Chapters 2–3 correction and completion work

Execution target: GitHub CI only. No local Lean, Lake, compiler installation or build was run.
Sources inspected: all Chapter 2/3 endpoint entries in the current status ledger; the actual
functional, Gram, signature, principal-minor, Newton, pole-kernel, Jacobi and character modules;
the exact pinned Mathlib LDL, matrix inverse/multiplication and SmoothSeries APIs; manuscript
PDF pp.12–13 for the precise two clauses of Theorem 3.8.

The contribution contains 64 named theorem declarations across seven source modules; this
count includes intermediate lemmas and does not mean 64 additional manuscript theorems.
An independent semantic review confirmed the fixed density power, parameter scaling,
rational weights, and kernel normalization. The last three analytic modules also received
an independent pinned-API review; receiving CI remains authoritative.

## Latest verification: CI5

GitHub Actions run [40326559574](https://github.com/randogelist/zetahyperbolic-axiom/actions/runs/40326559574),
commit `b1c99c0d25cf94ee2cfbb398f697b7e50c363f89`, compiled all seven spectral modules
and accepted their complete transitive dependencies in the 258-module completed-subset axiom
audit. The audited spectral results use only `propext`, `Classical.choice`, and `Quot.sound`.
This verifies both clauses of original Theorem 3.8 and the previously approved 3.3.alt.
The complete repository has not yet received a global PASS: an unrelated `BetaBeukersSpectrum`
compilation error remains. No spectral source change is required by CI5.

## Implemented corrections and additions

### Section3OrthogonalKernel.lean — Theorem 3.8(1)

- Original gap: monic polynomials and positive proposed norms were constructed, but their actual
  integral orthogonality and inverse-Gram kernel identification were not established. Existing
  pole-spectrum equivalence therefore had not been identified with the printed polynomial kernel.
- Cause: the LDL construction stopped before its matrix inverse and bilinear-integral consequences.
- Implemented: inverse Gram LDL factorization; normalized coefficient orthogonality; bilinear
  polynomial moment integration; actual monic-polynomial integral pairings and squared norms;
  inverse-Gram kernel equality at all real arguments; exact pole-node kernel identification;
  full characteristic-polynomial equality between the manuscript symmetric normalization and
  the constructed signed orthogonal-polynomial pole kernel.
- Exact premises: only `Real.Admissible p` for actual-family endpoints; no caller-supplied
  orthogonality, analytic measure realization, positivity or spectral witness was introduced.
- CI1: inverse-Gram identity compiled with only the allowed foundations. Failures in the later
  assembly exposed unreduced `if True`, opaque rational cast homomorphisms and an untyped
  `Function.charpoly` projection. Corrected by full `simp`, `Rat.coe_castHom`, and explicit
  `Matrix.charpoly`, respectively. No mathematical statement was changed.
- CI2: compiled successfully; endpoint axiom prints contain only `propext`, `Classical.choice`,
  and `Quot.sound`.
- Scope: this closes the intended construction route for 3.8(1). The
  independent Laplace integral derivative in 3.8(2) is not inferred from a finite matrix identity.

### LaplaceDensityDerivative.lean — actual analytic step in Theorem 3.8(2)

- Original gap: differentiating the actual infinite exponential series was not justified.
- Implemented: exact positive-scale series; explicit derivative of each summand; summable
  derivative majorant on the open neighborhood `τ > τ₀/2`; termwise differentiation by pinned
  Mathlib `hasDerivAt_tsum_of_isPreconnected`; exact identification at scale one; pointwise
  derivative of the printed density for every `τ>0` and `y>0`.
- Premises: positivity of scale and spatial variable, as in the printed statement. No derivative
  or convergence assumption is supplied by the caller.
- CI2 exposed scalar normed-module instance diamonds in tactic conversions, a no-progress
  simplification and an already-reduced interval-membership goal. Corrected with default-
  transparency `convert!`, optional power simplification before `ring`, and explicit inequality
  `change`. The analytic statements and their premises are unchanged.
- CI3: the density derivative module compiled successfully with the allowed axiom set.
- Does not alone exchange derivative with improper integral.

### LaplaceMomentBounds.lean — all scaled density/derivative moments

- Original gap: the derivative-density moments required an integrable majorant.
- Implemented: exponential integrals at every positive scale and arbitrary natural series
  exponent; absolute-integral summability reduced to the actual zeta series of exponent `2e+2`;
  all moments and polynomial-weighted integrability of the actual scaled density and derivative.
- The odd exponent in the derivative series is handled explicitly, not silently identified with
  an odd-weight density that has a different exponent.
- CI3: the moment-bounds module reached all proofs but one positivity tactic did not use
  half-line membership as an explicit nonnegativity fact. Replaced it with explicit multiplication
  and power nonnegativity using `le_of_lt hy`. No statement changed.
- CI4: the moment-bounds module compiled successfully with the allowed axiom set.
- Rational-weight and local-domination assembly
  have now been implemented in the following modules.

### LaplaceMomentDerivative.lean — actual integral differentiation

- Constructed measurability, positivity, scale monotonicity and an explicit derivative norm
  majorant at half the current positive scale.
- The numerator polynomial supplies rational-weight integrability because the positive
  denominator is at least one. Proved integrability of both actual weighted density and derivative.
- Applied the pinned dominated-local-derivative integral theorem to obtain
  `weightedMoment_hasDerivAt`, with the majorant constructed internally.
- Static review fixed the norm simplification to target the denominator explicitly; rewriting
  the first real norm generically could instead simplify the numerator.
- Only positive scale is assumed; no caller-provided domination or derivative certificate.
- CI4 exposed a renamed/qualified infinite-sum order API, an unsupported nonpositive tactic
  target, missing explicit numerator positivity, and hidden pointwise multiplication/negation
  obstructing tactic rewriting. Fixed with `Summable.tsum_le_tsum`, explicit sign lemmas and
  numerator positivity, an explicit pointwise `change`, and AE congruence for negation.
  All mathematical statements and their hypotheses are unchanged.
- CI5: compiled successfully and passed the completed-subset transitive axiom audit.

### LaplaceGram.lean — actual positive Gram curve

- Constructed the positive atomless weighted measure and its pushforward by `y ↦ y²` for every
  positive scale, proved all actual moments integrable, and proved the literal moment matrix
  positive definite using those facts.
- `gram_one` proves that scale one is exactly the manuscript Gram matrix at the true zeta value,
  rather than an unrelated generic matrix curve. This identification assumes only admissibility.
- `gram_hasDerivAt` proves every entry's actual integral derivative. Positivity holds without
  admissibility assumptions (only positive scale), so determinant invertibility is not assumed.
- `monicPolynomial_integral_pairing` and `squaredNorm_eq_integral` explicitly identify the
  deformed kernel's monic polynomials and norms with the actual measure at every positive scale.
- CI5: compiled successfully and passed the completed-subset transitive axiom audit.

### LaplaceKernelJacobi.lean — actual Theorem 3.8(2) endpoint

- Proved the finite Jacobi trace equals the integral of the constructed monic-polynomial kernel
  times the actual rational weight and density derivative; finite integral exchanges are
  justified by the weighted-derivative integrability proved above.
- `laplace_logDet_hasDerivAt` establishes the printed parameter formula at every positive scale.
  `actual_gram_laplace_logDet` includes the original-family base-point identification.
- Together with `Section3OrthogonalKernel`, this completes both clauses of original 3.8.
- CI5: compiled successfully, with the entire spectral dependency chain accepted by the
  completed-subset transitive axiom audit. Global project verification remains pending the
  unrelated Beta spectrum repair.

### Section3RestrictedSpectral.lean — the previously approved 3.3.alt

- Original gap: the pre-existing alternative had separately proved components but no exact
  assembled endpoint.
- Implemented `theorem_3_3_alt`: actual Gram positivity; positivity of every principal determinant
  at the true zeta value; exact residue-product leading coefficient and sign; intrinsic positive
  and negative ceiling/floor signature counts.
- Only `Real.Admissible p` is assumed. This is exactly the prior approved restricted target;
  arbitrary mixed-minor positivity and Stieltjes determinacy remain excluded, as before.
- CI2: compiled successfully with only the allowed foundations in its printed axiom set.
- CI5: accepted by the completed-subset transitive axiom audit. Only the approved alternative
  is covered, never original 3.3; final global-project verification remains separate.

## Result-by-result review and remaining obstacles

| Item | Reviewed state / action | Precise remaining requirement |
| --- | --- | --- |
| 2.2 | Retained exact rational-functional pullback and representation independence. | No new mathematical gap found; whole-project CI must retain its proof. |
| 2.3 | Retained exact reflection, admissible-pole difference and actual derivative construction. | Existing Bernoulli B₁ proof-prose correction remains necessary; theorem itself retained. |
| 2.4 | Retained genuine-basis congruence and primitive normalization up to sign. | No additional original-statement gap found. Nonzero determinant remains an explicit premise. |
| 2.5 | Retained original-denominator Lagrange functional matrix and nonzero diagonal slopes. | Alternative product spellings are not silently identified. The whole affine pencil is not claimed diagonal. |
| 3.1 | Retained actual primitive degree, real roots, zeta center and exact operator-norm disk. | Uniform exponential family rates belong to Chapter 4, not this endpoint. |
| 3.2 | Corrected full real-s density already exists; retained separately from false printed normalization. | The original coefficient differs by π/2 at odd weights and cannot be certified unchanged. |
| 3.3 | Assembled the pre-approved restricted alternative. Inspected shifted sparse/solid minors and intrinsic signature. | Original arbitrary mixed minors require a continuous Cauchy–Binet/Andreief identity and strict generalized Vandermonde signs; solid/principal positivity cannot replace this. Determinacy additionally needs a quantitative uniqueness argument. No corresponding finished bridge is present in the project. |
| 3.4 | Inspected exact slope-rank degree/root count, actual singular example, Dodgson and restriction-signature bounds. | Literal universal r-root list is contradicted by the actual k=2,m=1,N=1,K=6 constant first principal minor. Corrected ordered interlacing still requires connecting compression eigenvalue counts to reciprocal nonzero roots, including zero-eigenvalue crossings. Generic signature bounds do not by themselves establish that ordered statement. |
| 3.5 | Inspected actual scalar normalization counterexample and exact two-/three-level corrected Schur identities. | Literal formula is false. Full correction requires constructing the normalized tridiagonal/Krylov chain, proving cyclicity or exact rank termination, and retaining the Gram determinant prefactor. Existing finite determinant formulas do not supply that construction. |
| 3.6 | Retained complete corrected finite-support reciprocal endpoint. | Literal all-order strict Hankel positivity is impossible beyond the number of distinct atoms; printed signs/bounds also need the recorded corrections. |
| 3.7 | Inspected actual strict Newton/Turan and derivative distinct-root proofs against PDF p.12. Existing `ActualStrictNewton.actual_centered_newton_strict` and `actual_coefficient_strict_criterion` cover the previously approved restricted 3.7.alt; their `2 ≤ h` premise follows whenever the inequality range `k+2 ≤ h` is inhabited. | Original individual centered-coefficient nonvanishing remains separate: real distinct roots alone do not imply it (symmetric real-rooted polynomials have vanishing odd coefficients). The paper's appeal to genericity is not an actual-family proof. Need an exact sign/nonvanishing argument for the specific centered coefficients; no new assumption was substituted. |
| 3.8 | Completed both actual orthogonal kernel/pole-spectrum clause and actual Laplace integral log-determinant clause, including analytic bounds, derivative interchange, positive deformed Gram, scale-one identification and trace/kernel assembly. All seven spectral modules compiled and passed the transitive completed-subset audit in CI5. | No remaining spectral proof obligation. Final global-project PASS awaits an unrelated Beta spectrum repair. No additional mathematical hypothesis was introduced beyond admissibility and positive Laplace scale. It is not an asymptotic Taylor-remainder problem. |
| 3.9 | Inspected exact shifted-pole/slope algebra and five positive Fekete kernels; checked PDF p.13 statement. | Hurwitz: actual Hermite pole integral and Gram-functional identification. Character case: identify the specified real characters with the five periodic kernels, prove the actual generating-series identities/integrability and rational-functional matrix bridge. Generic positive finite kernels do not supply these identifications; no counterexample is established. |

No unexamined theorem was marked proved. False printed statements are kept distinct from open
corrected constructions. No claim is made that proof search has disproved the remaining open
mathematical assertions.
