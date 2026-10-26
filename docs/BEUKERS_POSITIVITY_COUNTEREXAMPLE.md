# Theorem 6.3(2): an actual-family positivity counterexample

The strict positive-definiteness conclusion on PDF pages 32–33 is false for
the stated subspace when `h=4`, `m0=8`, and `K=28`. This is separate from the
valid dimension lower bound and from the q-adic assertion in part (1).

The exact certificate is
`provenance/beukers_cone_h4_certificate.json`. Its arithmetic is reproduced by
`python3 tools/check_beukers_h4_counterexample.py`, using only Python integers
and rational numbers, with no floating-point sign decisions. This is a
rigorous rational certificate with the elementary analytic argument below;
it is **not yet a Lean kernel-checked counterexample**. The distinction is
intentional.

## Exact polynomial and admissibility

Let `V0,...,V3` be the four rational coefficient vectors `basis_Q` in the
certificate, in ascending powers of `x`. Define

```
t = 6478719102356089 / 10^15,
Q(x) = V1(x) - t V0(x),
P(x) = x^8 (1-x)^4 Q(x).
```

Each `Vj` has degree at most 15, so `P` has degree at most 27. The four
vectors' last four coordinates are the identity matrix, proving their
linear independence. For every one of the four corresponding polynomials
`Pj=x^8(1-x)^4 Vj` and every `0 <= m < 4`, `0 <= nu <= 2`, the checker
verifies the exact rational equality

```
sum_r [x^r]Pj * (nu!/(r+m+1)^(nu+1)
                 - (5-nu)!/(r+m+1)^(6-nu)) = 0.
```

The elementary Mellin formula
`integral_0^1 x^a (-log x)^b dx = b!/(a+1)^(b+1)` identifies these twelve
equalities with the manuscript's orthogonality conditions. That Mellin
formula is also independently kernel-checked in
`LeanPaper.UnitLogMoments.integral_pow_log`. Thus all four polynomials and
their nonzero combination `P` belong to the *actual* subspace `V_K^+`.
Dividing each `Vj` by its positive rational coefficient l1 norm gives the
required four-dimensional normalized basis with l1 norm exactly one.

## Exact negative quadratic evaluation

For the rational coefficient vector `p` of `P`, the printed pencil (5.3)
has quadratic evaluation

```
B(P,P) = A*zeta(7) + B,
A = sum_r p_r^2 > 0,
B = -sum_r p_r^2 H_r^(7)
    + sum_(r != s) p_r p_s (H_r^(6)-H_s^(6))/(6(r-s)).
```

The exact rational values `A` and `B` are `slope` and `constant` in the
certificate. The checker recomputes them from the actual coefficients.
It then proves with rational comparisons that

```
-1.2115 * 10^(-48) < B(P,P) < -1.2114 * 10^(-48).
```

The interval is narrow but its negativity is certified, not inferred from
rounding. The independently derived zeta interval has width less than
`5.75 * 10^(-73)`, more than sufficient after multiplication by `A`.

## Elementary rigorous enclosure of zeta(7)

Write

```
S_N = sum_(k=0)^(N-1) 2^(-k-1)
        sum_(j=0)^k (-1)^j choose(k,j)/(j+1)^7.
```

For `0 < x < 1`, the finite geometric identity gives

```
1/(1+x) = sum_(k=0)^(N-1) (1-x)^k / 2^(k+1)
          + (1-x)^N / (2^N(1+x)).
```

Multiply by `(-log x)^6/720` and integrate from zero to one. Expanding only
the finite polynomials and using the Mellin formula gives `S_N` for the
finite part. The remainder lies in `[0,2^(-N)]`, since
`0 <= (1-x)^N/(1+x) <= 1` and the normalized logarithmic weight has mass
one. Absolute convergence of the geometric integral expansion also gives

```
integral_0^1 (-log x)^6/(720(1+x)) dx
  = sum_(n=1)^infinity (-1)^(n-1)/n^7
  = (1-2^(-6))*zeta(7).
```

Consequently the rigorously valid enclosure is

```
(64/63) S_N <= zeta(7) <= (64/63)(S_N+2^(-N)).
```

The checker computes both endpoints exactly for `N=240`, multiplies by
the positive `A`, adds `B`, and checks the displayed negative interval.
This derivation needs no unproved numerical zeta estimate or asymptotic
expansion. The initial search used floating point only to find a candidate;
none of those exploratory values is used by the certificate checker.

## Consequence and required repair

The normalized four-polynomial basis is admissible in the exact printed
statement, yet its evaluation matrix has a negative quadratic direction.
Thus its strict positive definiteness is false. The printed proof's
concentration argument cannot be repaired merely by supplying omitted
estimates: the asserted tail positivity itself fails for this subspace.

A substantive repair must change the positive-cone construction, for
example by controlling the negative tail relative to a retained positive
spectral gap and choosing a truncation and polynomial approximation that
depend on this bound. It must then reprove the dimension, positivity and
decay rate together; the constants `m0=2h`, `K=7h` and the present twelve
conditions cannot be retained as a sufficient condition. Part (1)'s q-adic
claim is independent and still needs its own formalization.

Separately, the fixed-`K` reading of Theorem 5.2(3) is dimensionally
impossible when `K=h=2`: positive and negative h-dimensional subspaces in
a `(K+1)`-dimensional space require `2h <= K+1`. This obstruction is
kernel-checked in `LeanPaper.KreinDimensionObstruction`. Its intended
quantifier repair is to allow sufficiently large `K` depending on `h`.
Even with that repair, the printed proof discards an uncontrolled infinite
tail; the new counterexample explains why that analytic issue matters.
