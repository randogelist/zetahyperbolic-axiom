# Independent semantic review of original Proposition 5.3

Reviewed `BetaBeukersMoments.lean` and `BetaBeukersSpectrum.lean` against the supplied manuscript, pp. 24–25, Proposition 5.3, using the local PDF text extraction. This is source-level mathematical review; receiving CI and the kernel audit remain required.

## Printed analytic data and source match

The density is exactly `(-log(x*y))^2 / (6*(1+(x*y)^2))` on `(0,1)^2`. The source constructs the restricted product measure and its actual `withDensity` measure, establishes strict positivity on that square, and proves integrability before identifying its moments. There is no assumed moment identity or positivity-of-integral premise.

The printed alternating harmonic correction is the rational sum from `n=0` through `m-1` of `(-1)^n/(2*n+1)^s`; `betaHarmonic` has exactly those limits, exponent and sign. `betaValue` is the corresponding infinite Dirichlet series. The diagonal moment for powers `(4*k,4*k)` is `betaValue 4 - betaHarmonic 4 (2*k)`. For distinct `k,l`, the off-diagonal moment is `(betaHarmonic 3 (2*k)-betaHarmonic 3 (2*l))/(12*(k-l))`. The denominator is a difference of rational/real casts, not truncated natural subtraction. All constants and signs agree with the printed formula.

The proof sums absolutely integrable signed geometric terms, deriving the actual integral rather than using a default value for a possibly nonintegrable function. The dominating positive terms have integral bounded by `(n+1)^(-4)`, and the tail sums are proved for `s>1`.

## Printed finite spectral conclusion and source match

The printed polynomial space is `Q[x^4]` of degree at most `4*K`. The source represents its elements as rational polynomials `A_i(u)` of degree at most `K`, evaluated at `u=x^4`; this is the standard coefficient identification of the same space. The independence hypothesis is `LinearIndependent ℚ A`, so no independence over the reals is assumed. The rational-to-real coefficient separation is supplied by the repaired rational Gram determinant theorem.

`betaIntegralMatrix` consists of the actual integrals of `A_i(x^4)*A_j(y^4)` against this density. Its rational constant matrix is calculated from the moment formulas. The affine pencil is centered at the actual `betaValue 4` and has exactly the coefficient Gram slope. Symmetry follows from symmetry of the rational divided difference, and strict positive definiteness follows from the original rational polynomial independence. The determinant has exact degree `h` and every complex root has zero imaginary part, which implies the printed statement that all `h` roots are real, counted with multiplicity.

There is no need for the two-variable integral form at the center to be positive definite. The proof correctly establishes positivity only of the X-derivative. No root-side assertion, infinite Krein decomposition, or irrationality statement is added.

## Static review findings

The first version of `fourth_pair_expansion` had the same nested-sum reordering risk exposed by CI in `BeukersIntegralPencil.polynomial_pair_expansion`. The owner was notified and added the required `Finset.sum_comm` before termwise congruence. Polynomial-matrix equalities used `ext i j`, which may descend to polynomial coefficients; the owner changed them to `funext i j`.

`BeukersPolynomialSpectrum.lean` contains no independent product-of-two-sums expansion; it delegates that operation to the repaired integral-pair module. Its coefficient-evaluation identity uses pinned Mathlib's `Polynomial.eval₂_eq_sum_range'`, with `natDegree < K+1`, and `Fin.sum_univ_eq_sum_range`. Its matrix identifications already use `funext i j`, and its determinant-map identity is in the correct symmetric direction.

## Verdict

The combined moment and spectral endpoints implement the full mathematical content of original Proposition 5.3, subject to successful receiving CI and transitive axiom audit. The parameterization by `A_i(u)` is a coordinate representation of the printed `Q[x^4]` family, not a restricted alternative. This review does not itself certify compilation or authorize a verified-status claim.
