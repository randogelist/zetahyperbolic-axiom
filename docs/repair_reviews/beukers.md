> **Final receiving verification:** All registered Lean sources discussed here are included in the 263-module [GitHub CI PASS](https://github.com/randogelist/zetahyperbolic-axiom/actions/runs/40339809027) at proof commit `cdcb1935aa73a7c7e65006c1c198d114e9dcc6db`, with a fresh all-project transitive axiom audit and negative regressions. See the [matching receipt](../../validation/github/20261026-prime/acceptance.json) and [current whole-result status](../FORMALIZATION_STATUS.md). References below to candidates, pending CI or failed runs describe historical investigation checkpoints; compilation does not extend the exact mathematical scope recorded here.

# Chapter 5 analytic repair audit

All verification below is through the parent's GitHub CI. No local Lean/Lake/compiler invocation or dependency installation was used. Candidate source is never described here as kernel-verified before that CI accepts it.

## 5.1: actual positive measure and all monomial moments

**Original problem.** The repository already proved the density's diagonal and off-diagonal moments, but its `BeukersKreinPolynomialActual` form was a formal finite sum of monomial integrals. The weighted measure and the equality with an integral of actual polynomials were missing.

**Cause.** Missing analytic interfaces between the actual geometric-series proof and the coefficient-matrix/spectral proofs; not an unproved special-value evaluation.

**Correction.** `src/LeanPaper/BeukersIntegralPencil.lean` constructs the measure using the actual positive density, derives its integrability from the existing proved nonzero integral, bounds every monomial by one, and supplies integrability and all moments against the constructed measure. It expands actual finite polynomial evaluations, integrates the finite sums, and identifies the result with the rational affine `dualEntry` at zeta(7). `theorem_5_1_actual_measure` assembles the full moment statement. `integral_polynomial_pair_eq_dualEntry` exposes the genuine polynomial-integral bridge for 5.2 and Chapter 6.

**Verification.** First CI compiled all statements except two implementation details: `fun_prop` did not unfold/register the measurable density, and distribution of the two finite sums reversed their index order. Fixed by explicitly multiplying `density_measurable` by measurable monomial powers, and applying `Finset.sum_comm` after distribution. GitHub CI2 (40318924083, commit 96ffaabc6051e7ebbf66b3f86aeea91cb7602111) compiled the corrected module. No mathematical assumption was added. Agent `repair_section5_build` uses this interface in `BeukersPolynomialSpectrum.lean`.

## 5.3: actual beta(4) measure, moments, and finite pencil

**Original problem.** No analytic construction established the printed beta-density moments or connected them to a positive coefficient-Gram slope.

**Correction.** `src/LeanPaper/BetaBeukersMoments.lean` defines beta(s) by its Dirichlet series, proves absolute convergence for s>1, and proves the even-tail identities. It constructs exactly the printed density `(-log(x*y))^2/(6*(1+(x*y)^2))`. Its signed geometric terms have integral norms bounded by `(n+1)^(-4)`, justifying exchange of series and integration. Mellin log-monomial integrals then give:

- diagonal moments beta(4) minus the rational harmonic sum through index `2*k-1`;
- off-diagonal moments `(H_beta,3(2*k)-H_beta,3(2*l))/(12*(k-l))`;
- actual weighted-measure integrability, strict density positivity, and rational off-diagonal values.

`src/LeanPaper/BetaBeukersSpectrum.lean` integrates actual rational polynomials evaluated at x^4 and y^4, calculates their rational symmetric constant matrix, and proves their X-derivative is the positive coefficient-Gram matrix. It transports rational polynomial independence through the shared repaired rational-independence interface and applies the existing positive-slope spectral theorem. The determinant has degree h and every complex root is real.

**Scope review.** Independently checked against PDF pp.24–25 by agent `repair_section5_build` (`repair_notes/semantic_53.md`). Q[x^4] is represented by rational polynomials in u evaluated at u=x^4; signs, normalization 1/12, harmonic index 2*k, and positive slope all match the original proposition. No positivity of the indefinite integral form is asserted or used. The result combines actual moments with the complete finite spectral conclusion.

**Verification.** CI2 compiled the analytic file except the geometric-series power identity: simplifying `neg_pow` recursively revisited `(-1)^n`, and denominator normalization left an inverse uncleared. Replaced this with one explicit negative-power identity and normalized inverse products directly. GitHub CI3 compiled the repaired analytic module. Spectrum awaits the repaired spectral dependencies. The known finite-sum ordering issue was proactively corrected in `fourth_pair_expansion`; matrix equality uses `funext` to avoid unintended polynomial-coefficient extensionality.

## 5.4: higher-zeta cancellation

**Review.** `src/LeanPaper/Section2TauLinear.lean`, theorem `evenPolePair_cancellation`, already covers the final simple-pole statement, including j=1 directly through the harmonic recurrence. It also contains explicit certificates `printed_evenPair_division_fails_at_zero` and `even_monomial_Bernoulli_exception` for the defective printed intermediate steps. The printed proof needs the documented sign/B1/pole-sum corrections, already recorded in repository audit files. No weakening or new axiom was needed; no source edit made here. Higher-order poles remain outside the stated theorem, consistently with Remark 5.5.

## 5.6(1): exact outer floor integral and false endpoint continuity

**Original problem.** The only active prior mapped source proved the sign of the rational number `453803/288000`; it did not evaluate the floor-function integral. `docs/SECTION5_PRIME_SUM_REVIEW.md` referred to `Section5OuterPrimePieces` and `Section5OuterPrimeIntegral`, but those sources did not exist in the checkout, repository history searched for those paths, or the 25 available attached ZIP archives inspected.

**Correction.** Added `src/LeanPaper/Section5OuterPrimeIntegral.lean` with the actual floor definition, alpha=3/40, lambda=37/40, all seven positive-part terms, and the actual piecewise R. It proves all eleven Table 1 affine expressions on their open interval interiors, proves integrability and the exact integral of every piece, and joins the adjacent intervals to obtain `453803/288000`. This is an actual integral theorem, not arithmetic about a supplied constant.

The literal actual values are T(1/3)=23/6, T(1/2)=67/20, T(1)=-1. The printed table instead gives right-hand affine limits 113/24, 4, 17/20. The module includes noncontinuity proofs for both printed half-open continuity intervals by uniqueness of one-sided limits. Endpoint modifications are not silently applied to the integrand; equality on open intervals suffices for integration.

**Verification.** CI3 confirmed the actual endpoint-value theorem with allowed axioms, but found tactic/API failures in the piece proofs and generic interval-integral helper. Replaced ineffective max/min simplification with explicit linear-condition case analysis; explicitly introduced the EqOn point binder and typed the constant/linear integrability witnesses; retained the buffered n=0 sequencing fix. CI4 exposed a deeper normalization issue: norm_num changed `1/y` to `y⁻¹` before the supplied floor equality rewrote it, leaving an unresolved floor factor and causing the branch-search timeout. Replaced search with an explicit floor rewrite before normalization, explicit v/u/t/r/min identities, and seven directly proved scalar positive-part values per piece; no heartbeat increase. Also corrected the pinned integral_id namespace. GitHub CI5 compiled the full integral and both noncontinuity endpoints, and the completed-subset axiom audit passed. Exact sum of the eleven displayed rational integrals was independently checked using rational arithmetic: 453803/288000. The literal T was also independently evaluated at three rational interior points of each of the eleven pieces and at all three exceptional endpoints; every result matched the formal source expressions.

**Remaining genuine obstacles to the whole 5.6.** The complete literal theorem cannot be proved because both stated endpoint-continuity assertions are false. Its corrected integral clause is independently recoverable as above. Part (2) needs the actual periodic integration-by-parts and quantitative inner-tail estimate. The printed variance expansion has coefficient 25 where b=4*l forces 16; a loose upper bound may survive but its analytic proof remains necessary. Part (3) assumes the two smallest actual tail poles are a and p-a, even when a is canceled by the numerator. Concrete counterexamples in the existing review include K=400,N=30,p=11,a=1 (remaining indices32,34) and p=101,a=1 (100,102). This invalidates that proof step, not by itself the final valuation bound. A repair must recompute the actual surviving harmonic residues and local minor valuations for every residue class. No fake gain theorem, premise that restates the desired bound, or weaker theorem relabeled as the original was introduced.

## 5.7: printed partial-fraction bridge is inconsistent

**Original problem.** The actual printed numerator contains `t^5` for every n>=1, whereas its denominator contains only `t^2` at zero. Consequently the double-pole coefficient at zero must vanish, but the printed coefficient A_(n,0)=n! does not vanish.

**Correction/certificate.** `src/LeanPaper/DoublePoleZeroCoefficientObstruction.lean` specializes the actual formula to n=1 and constructs its exact cleared polynomial numerator. Evaluation at zero proves that any valid decomposition requires A_0=0 because the omitted zero-pole cofactor evaluates to 518400. The printed coefficients give A_0=1, so no choice of simple-pole coefficients can satisfy the cleared identity. It also proves divisibility of the actual numerator by X^2.

**Scope.** This is a formal obstruction to the printed definition/proof bridge. It is NOT a refutation of the whole conditional determinant-valuation theorem: no integer relation a*zeta(5)+b*zeta(6)=c with b nonzero has been supplied, and no valuation counterexample under those hypotheses is claimed.

**Verification.** CI2 found unresolved nested Fin-index conditionals in a fully expanded polynomial product. Repaired by evaluating the product first; for k nonzero the zero-node factor vanishes directly, while k=0 reduces to one exact scalar product. CI3 exposed recursive simplification from Fin.ext_iff in that scalar calculation; repaired by separating index zero and eliminating all successor-equals-zero tests before evaluating the remaining product. GitHub CI4 compiled the repaired module; both printed obstruction endpoints use only allowed axioms.

**Remaining genuine obstacle.** A corrected actual rational function or corrected double-pole coefficients, a proved exact partial-fraction decomposition and functional, and q-adic/local-minor valuation estimates are required. Altering only the simple-pole coefficients cannot fix the literal n=1 bridge. No responsibly justified route to the printed full valuation assertion is currently available from the repository's proofs.

## CI4-to-CI5 finite beta pencil normalization

The separately owned weight-seven polynomial spectrum first reached its affine identity in CI4 and exposed a semireducible Matrix-versus-function elaboration mismatch. Applied the same preventive plain coefficient-function normalization in betaIntegralPencil_eq_spectral, without changing its mathematical statement or assumptions. Beta moments remain CI3-compiled; the full beta spectral module still requires receiving CI verification.

## CI5 final beta-spectrum repair

CI5 compiled 258/260 registered modules; all actual outer-integral endpoints passed. The only remaining source failure was betaConstant_swap using `h.symm` when h is a negated equality. Replaced it by the explicitly typed reverse inequality `htr : t ≠ r := fun htr => h htr.symm`, then eliminated both conditional branches. The integral polynomial bridge itself already showed only allowed axioms in the CI5 log; the full spectral endpoint awaits the final global run.
