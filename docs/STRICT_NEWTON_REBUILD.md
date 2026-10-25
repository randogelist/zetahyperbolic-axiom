# Strict Newton inequalities: reconstructed proof

The modules `ConsecutiveDerivativeZeros`, `DerivativeDistinctRoots`,
`StrictLaguerreGeneral` and `StrictNormalizedNewton` passed targeted
Lean 4.33.0 compilation. Their printed public endpoint axioms are restricted
to `propext`, `Classical.choice` and `Quot.sound`. The expanded project audit
and the actual-family assembly are separate steps.

## Exact generic scope

For a real polynomial `P` whose roots are all real, with at least two
**distinct** roots, write `n = P.natDegree`. For `k + 2 <= n`, the theorem
`LeanPaper.StrictNormalizedNewton.coefficient_newton_strict_criterion`
proves exactly

\[
\frac{a_k}{\binom nk}\frac{a_{k+2}}{\binom n{k+2}}
<\left(\frac{a_{k+1}}{\binom n{k+1}}\right)^2
\iff
 a_{k+1}\ne0\ \lor\ (a_k\ne0\land a_{k+2}\ne0).
\]

This is the strictness condition in Theorem 3.7(2), with `m = k + 1`.
The already retained weak Newton hierarchy supplies the non-strict inequality.
No coefficient sign or root-simplicity hypothesis is added. Distinctness
here only means that the entire root multiset is not concentrated at one root.

At every real non-root center `x`, the full Taylor coefficient hierarchy is
strict. The endpoint
`LeanPaper.StrictNormalizedNewton.normalized_shifted_newton_strict`
also divides every Taylor coefficient by `P.eval x`, matching the paper's
normalized centered coefficients. Its hypotheses are real splitting,
two distinct roots, `P.eval x != 0`, and the stated index range. An actual
manuscript specialization must derive these hypotheses from the retained
analytic/spectral construction; the generic theorem is not itself counted
as a complete actual-family statement.

## Proof chain

1. `consecutive_derivative_zeros_force_root`: two consecutive derivative
   zeros at orders `k,k+1`, with `k < degree`, propagate backward to `P(x)=0`.
   The proof uses the already verified strict ordinary Turan inequality.
2. `consecutive_taylor_nonvanishing`: consequently, consecutive Taylor
   coefficients cannot both vanish at a non-root center. The module also
   specializes this conclusion to the actual primitive polynomial at the
   true zeta center, with no new premises beyond admissibility and index range.
3. `derivative_hasDistinctRoots`: if a derivative of degree at least two
   had only one repeated root, the previous result would force that root
   into `P`. The exact derivative root-multiplicity law would then force
   every root of `P` to be that same root. Contraposition proves distinct-root
   inheritance. Induction handles every derivative still of degree at least two.
4. `laguerre_strict_of_distinct_roots`: enumerate the actual multiset of
   roots, derive both logarithmic derivative identities, and identify the
   strengthened Laguerre expression with the squared polynomial value times
   a sum-of-squares variance. A pair of distinct roots makes it positive
   off the zero set. The finite factorization is constructed from splitting.
5. Apply that strict inequality to each derivative and normalize by the
   falling factorial. Root cases are handled separately and give the exact
   coefficient criterion above. The absence of consecutive Taylor zeros
   proves strictness throughout every non-root-centered hierarchy.

## Manuscript distinction

The proof does **not** assert that each centered coefficient is nonzero.
That assertion is unnecessary for strict Newton inequalities. The split
quadratic `X^2 - 1` has two distinct nonzero roots, nonzero value at zero,
and zero middle coefficient; the formal diagnostic
`distinct_nonzero_roots_allow_zero_coefficient` documents why generic
root distinctness does not justify individual coefficient nonvanishing.
It is a counterexample to that general inference, **not** an asserted
counterexample within the manuscript's parameter family. Any literal
actual-family assertion that every centered coefficient is nonzero must
remain a separate obligation or be explicitly removed in a corrected theorem.
