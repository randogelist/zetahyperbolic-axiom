# Chapters 2–3 correction and completion work

Execution target: GitHub CI only. No local Lean, Lake, compiler installation or build was run.
Sources inspected: all Chapter 2/3 endpoint entries in the current status ledger; the actual
functional, Gram, signature, principal-minor, Newton, pole-kernel, Jacobi and character modules;
the exact pinned Mathlib LDL, matrix inverse/multiplication and SmoothSeries APIs; manuscript
PDF pp.12–13 for the precise two clauses of Theorem 3.8.

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
  `change`. The analytic statements and their premises are unchanged. Await CI3.
- Does not alone exchange derivative with improper integral.

### LaplaceMomentBounds.lean — all scaled density/derivative moments

- Original gap: the derivative-density moments required an integrable majorant.
- Implemented: exponential integrals at every positive scale and arbitrary natural series
  exponent; absolute-integral summability reduced to the actual zeta series of exponent `2e+2`;
  all moments and polynomial-weighted integrability of the actual scaled density and derivative.
- The odd exponent in the derivative series is handled explicitly, not silently identified with
  an odd-weight density that has a different exponent.
- Verification: CI2 skipped after the density module failed; awaiting CI3. Rational-weight and local-domination assembly
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
- Verification: source candidate queued for CI batch 3.

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
- Verification: source candidate queued for CI batch 3.

### LaplaceKernelJacobi.lean — actual Theorem 3.8(2) endpoint

- Proved the finite Jacobi trace equals the integral of the constructed monic-polynomial kernel
  times the actual rational weight and density derivative; finite integral exchanges are
  justified by the weighted-derivative integrability proved above.
- `laplace_logDet_hasDerivAt` establishes the printed parameter formula at every positive scale.
  `actual_gram_laplace_logDet` includes the original-family base-point identification.
- Together with `Section3OrthogonalKernel`, this supplies candidates for both clauses of 3.8.
  Neither clause is certified until the entire dependency chain compiles and passes the axiom audit.
- Verification: source candidate queued for CI batch 3.

### Section3RestrictedSpectral.lean — the previously approved 3.3.alt

- Original gap: the pre-existing alternative had separately proved components but no exact
  assembled endpoint.
- Implemented `theorem_3_3_alt`: actual Gram positivity; positivity of every principal determinant
  at the true zeta value; exact residue-product leading coefficient and sign; intrinsic positive
  and negative ceiling/floor signature counts.
- Only `Real.Admissible p` is assumed. This is exactly the prior approved restricted target;
  arbitrary mixed-minor positivity and Stieltjes determinacy remain excluded, as before.
- CI2: compiled successfully with only the allowed foundations in its printed axiom set.
  Only the alternative may be promoted after the whole-project audit, never original 3.3.

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
| 3.8 | Implemented both actual orthogonal kernel/pole-spectrum clause and actual Laplace integral log-determinant clause, including analytic bounds, derivative interchange, positive deformed Gram, scale-one identification and trace/kernel assembly. | Candidate whole endpoint; pending CI for the new source chain and its complete axiom audit. No additional mathematical hypothesis was introduced beyond admissibility and positive Laplace scale. It is not an asymptotic Taylor-remainder problem. |
| 3.9 | Inspected exact shifted-pole/slope algebra and five positive Fekete kernels; checked PDF p.13 statement. | Hurwitz: actual Hermite pole integral and Gram-functional identification. Character case: identify the specified real characters with the five periodic kernels, prove the actual generating-series identities/integrability and rational-functional matrix bridge. Generic positive finite kernels do not supply these identifications; no counterexample is established. |

No unexamined theorem was marked proved. False printed statements are kept distinct from open
corrected constructions. No claim is made that proof search has disproved the remaining open
mathematical assertions.
