# Corollary 3.6: exact corrected finite-family theorem

The full **corrected** finite-family statement is proved by
`LeanPaper.CorrectedReciprocalCorollary.corrected_corollary_3_6`.
The three new modules `RationalLogJets`, `ReciprocalAllOrders` and
`CorrectedReciprocalCorollary` passed targeted Lean 4.33.0 compilation.
Their printed endpoint axiom lists contain only `propext`, `Classical.choice`
and `Quot.sound`. The expanded whole-project audit is a separate build step.
This does not certify Corollary 3.6 as printed.

## Original statement and corrections

Source: the supplied manuscript, Corollary 3.6 (the paragraph beginning at
line 713 of the preserved layout extraction).

For the paper's convention

\[
S_m(q)=\sum_{j=1}^{h}(r_j-q)^{-m},
\]

the correct identity is

\[
\frac{d^m}{dx^m}\log|P(x)|\bigg|_{x=q}=-(m-1)!S_m(q),\qquad m\ge1.
\]

Replace the printed prefactor \((-1)^{m-1}/(m-1)!\) by
\(-1/(m-1)!\). Alternatively, keep that prefactor and reverse every gap to
\(q-r_j\); that changes the odd-moment sign convention. Since the hypothesis
only excludes zeros and does not require \(P(q)>0\), the real statement must
use \(\log|P|\), or explicitly specify a local complex logarithm branch.
Mathlib's real logarithm agrees with \(\log|\cdot|\) off zero.

The positive atoms are the **distinct** numbers \((r_j-q)^{-2}\), with
positive multiplicity weights. Both ordinary and shifted Hankel matrices
are positive semidefinite at every size. If there are \(d\) distinct atoms,
the size-\(n\) ordinary Hankel determinant is positive exactly for \(n\le d\)
and is zero for \(n>d\). In particular, size \(h+1\) always has determinant
zero. Distinct roots alone do not give distinct atoms: opposite gaps have
the same inverse square. Replace the printed all-order strict-positivity
claim by these finite-support laws. The actual-family zero-determinant
obstruction remains in `LeanPaper.ManuscriptObstructions`.

For \(d_{\min}=\min_j|r_j-q|>0\), the correct finite bound is

\[
h^{-1/(2r)}\le
\frac{S_{2r}(q)^{-1/(2r)}}{d_{\min}}
\le1,\qquad r\ge1.
\]

The printed statement reverses the factor interval; the manuscript's own
proof gives the corrected inequality. The limit is still \(d_{\min}\).

## Constructed proof chain

`RationalLogJets` constructs rational numerator/denominator polynomial
pairs by repeated quotient-rule differentiation, proves denominator
nonvanishing on the original polynomial's nonzero locus, and identifies
those pairs with actual iterated derivatives of the logarithm. This is a
construction of rational witnesses, not an assumed derivative certificate.

`ReciprocalAllOrders` identifies all positive-order inverse-gap sums with
those derivatives for the actual manuscript root vector, including root
multiplicities. It constructs rational witnesses for every order and for
every even Stieltjes moment, including the zeroth moment. The same
identities and witnesses are proved directly for the actual primitive
integer polynomial. Positive primitive normalization preserves the
logarithmic derivative at all orders.

`CorrectedReciprocalCorollary` starts with exactly a rational non-root of
the primitive integer polynomial. It combines these results with the
retained coalesced positive-atom construction, exact Hankel rank laws,
finite-factor estimate and attained nearest-root limit. No caller-supplied
Gram certificate, root simplicity, distinct-gap assumption, analytic
realization or asymptotic estimate is added.

All clauses of the corrected fixed-family corollary are covered. Uniform
large-parameter root collapse is a separate theorem and is not asserted.
