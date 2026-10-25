# Spectral manuscript review and continuation

This note distinguishes the numbered printed statements from components of their proofs.
A declaration below is a candidate until its current source hash has a successful compiler
receipt and the combined transitive axiom audit accepts it. No item is promoted to complete
from the existence of this note.

## Theorem 3.3

The new `PoleWeightSigns` construction uses the actual rational residues. It derives
`sign(gamma_a) = (-1)^(N+a)` with zero-based `a`, equivalent to the manuscript's
`(-1)^(poleIndex-1)`. In particular both signs occur when `h >= 2`. It also derives
the actual determinant leading-coefficient sign `(-1)^(N*h+h*(h-1)/2)`.

`SlopeIndefinite` transfers the actual alternating signs through the Vandermonde
congruence and positive square-root normalization. It proves that every spectral
factorization has a negative and a positive factor; pairwise distinctness is not
asserted. This supplies the precise nonconstant-spectrum hypothesis used in the
strict center Laguerre inequality, without assuming the desired inequality.

`SlopeSignature` uses Mathlib's intrinsic positive/negative quadratic-subspace
dimensions, not an ad hoc definition by desired counts. Sylvester congruence gives
positive and negative index sets `{a | Even (N+a)}` and `{a | Odd (N+a)}`, followed
by ceiling/floor cardinalities. This targets the signature clause of 3.3(3).

Remaining independent obligations are strict positivity of **arbitrary mixed**
Hankel minors, Stieltjes determinacy, and the exact primitive weight-five parity
specialization if not separately linked. The existing principal-minor positivity
does not imply mixed-minor positivity. A proof needs an integral Cauchy–Binet /
Andreief identity, strict generalized-Vandermonde signs on an ordered simplex,
and the actual measure's positive support. Determinacy needs the quantitative
moment bound and a formal Stieltjes Carleman theorem (or a replacement uniqueness
argument). These are unproved obligations, not refuted claims and not ordinary
compiler errors. Difficulty alone does not justify calling them fatal.

## Theorem 3.4

The actual-family counterexample `SingularPrincipalMinorExample` remains decisive:
k=2, m=1, N=1, K=6 has a positive constant first principal minor. Thus the literal
universal r-root list and minimum over that list are undefined/false at that rank.
The verified rank correction is degree/root multiplicity equal to slope rank.

The new `DodgsonCondensation` proves the all-rank polynomial identity through a
Schur complement over a rational-function field and descends it by injectivity.
The central minor only has to be nonzero **as a polynomial**. In the actual family
this follows from the already proved positive Gram center. No nonvanishing at
the root under consideration is assumed. The actual submatrix specialization
and its root evaluation give the exact displayed 3.5 equality and nonpositive
sign, for every rank, including rank two and zero-dimensional central blocks.

The generalized-eigenvalue interlacing clause remains distinct. A correct version
must allow zero generalized eigenvalues and count only their nonzero reciprocal
images as roots; the no-root nearest distance must be infinity, or the statement
must restrict to positive rank. Cholesky-compatible compression plus Cauchy
interlacing is a reasonable proof strategy, and has not been classified fatal.

## Corollary 3.5

`JFractionActualObstruction` strengthens the prior arbitrary-matrix diagnostic to
an admissible **actual manuscript instance**: k=m=N=1, K=2, h=1. The exact slope
is -12 and the true zeta Gram center G is positive. Therefore the normalized
scalar coefficient a1=M/G is negative. At X=zeta(3), the printed fraction is
1/a1<0 while the actual ratio Delta_0/Delta_1=1/G>0. No numerical approximation
to zeta is involved. This is a false formula, not an absence of tactics.

The rank-one correction is `(1/G)/(1+(X-center)*a1)`, proved as an identity of
totalized real expressions. In higher dimension the factor det(G_{h-1})/det(G_h)
must be retained, and the normalized I+tT continued fraction uses diagonal
`1+t*a_j` and off-diagonal squares `t^2*b_j^2`. Full-length strict `b_j>0` also
requires a cyclic starting vector; otherwise Lanczos stops at the Krylov rank.
Those two corrections are logically separate. The exponential edge claim still
needs the actual-family quantitative estimate of Theorem 4.7.

## Theorem 3.8 — correction to the tracker

The printed theorem (manuscript-layout.txt lines 843–896, PDF pp.12–13) has two
clauses: (1) the monic orthogonal-polynomial inverse-Gram/CD kernel and exact
pole-matrix spectrum; (2) the Laplace-parameter integral logarithmic-derivative
identity. It does **not** state an asymptotic Taylor remainder estimate. That
extra target must not be listed as a missing condition for this numbered theorem.
The retained affine Jacobi derivative and polynomial Taylor remainder are useful
components, but neither is the printed derivative-under-the-integral statement.

`SymmetricPoleSpectrum` closes the bridge from the actual symmetric matrix
G^{-1/2} M G^{-1/2} to the previously constructed signed pole matrix, by equality
of characteristic polynomials and hence root multiplicities. This uses the
actual positive Gram base from the analytic realization. Remaining work is
constructing the monic orthogonal polynomials and identifying their sum-of-squares
kernel with inverse Gram; constructing the Laplace-deformed moment matrix; and
proving differentiability by a concrete integrable dominator before applying
Jacobi and exchanging finite sums with the integral. These are still unproved,
not counterexamples to the two clauses.

## Proposition 3.2 and Theorem 3.9

Proposition 3.2's continuous-real-exponent density and its normalization are owned
by the parallel Section 2/basis continuation; this note makes no duplicate claim
of its completion. The analytic identity at odd weights must match the exact
coefficient of the density, rather than only a positive scalar multiple.

For 3.9, the retained shifted-pole algebra, real-exponent slope scaling and five
explicit Fekete-numerator positivity proofs remain valid components. For 3.9(1), the stated Hurwitz pole evaluation and the actual Gram measure are
still needed. For 3.9(2), the printed functional already defines monomials by
integrals and pole values by an affine expression plus an integral. Therefore
an additional closed-form arithmetic evaluation of its moments is not required
for that numbered real-rootedness claim. The actual remaining work is exact
character-to-five-kernel identification, convergence/integrability and positive
Gram construction, and the functional partial-fraction bridge. A positive finite
kernel alone cannot substitute for those identities. No counterexample to 3.9 has been established in this
review, and these gaps must not be labeled fatal merely because they are large.
