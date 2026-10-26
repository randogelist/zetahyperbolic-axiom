# Theorem 5.6: exact prime-sum review

The definitions on manuscript p. 26 were transcribed literally, including
`floor(1/y)` at the interval endpoints and the seven positive-part summands.
`LeanPaper.Section5OuterPrimePieces` derives each affine formula from that
actual definition. `LeanPaper.Section5OuterPrimeIntegral` integrates those
pieces using equality on open subintervals; the formal acceptance status is
recorded separately by the build runner.

## Endpoint correction in part (1)

All eleven Table 1 affine expressions agree with the actual function on the
open interval interiors. Three printed endpoint values instead denote right
limits:

| y | Actual T(y) | Right affine limit |
|---|---:|---:|
| 1/3 | 23/6 | 113/24 |
| 1/2 | 67/20 | 4 |
| 1 | -1 | 17/20 |

Consequently the printed continuity on `[1/3,1/2)` and `[1/2,1)` is false.
Replace these with `(1/3,1/2)` and `(1/2,1)`, and identify the endpoint entries
of the table as one-sided limits. The exact integral `453803/288000` is
unchanged because values at finitely many points do not affect it. This
correction does not alter the integrand in the Lean definition.

## Variance coefficient in part (2)

With the printed `b(x,z)=4*l(alpha*x,z)`, writing
`A=l(x,z)-2x` and `B=l(alpha*x,z)-2*alpha*x` produces the variance contribution
`16*integral(B^2)`, not 25 times that integral. The exact expansion is

```
Q(x) = (tau*(tau-sigma) - max(0,tau-sigma) + eta*(1-eta))/2
       + 16*d(g)*(1-2*d(g)) - 4*integral(A*B).
```

For example at `x=101/5`, exact integration of the piecewise-constant floor
functions gives `R=-3403/100` and `R-x*F=219/625`. The printed expression with
coefficient 25 gives `9627/20000`; its discrepancy is `2619/20000`.
Replacing 25 by 16 repairs the equality. The looser printed upper bound
`Q <= 27/8` remains compatible with this correction because the variance is
nonnegative. The final inner-tail theorem still requires the analytic
integration-by-parts and periodic bounds to be formalized.

## Remaining-pole error in part (3)

The proof asserts that after canceling the largest `s_a-2` tail poles, the two
remaining positive poles are `a` and `p-a`, both less than p. The tail
polynomial has only indices `N<k<=K`, so this identification is not generally
true. Two concrete examples with the stated `K=40n,N=3n` are:

- `K=400,N=30,p=11,a=1`: the two smallest paired-class tail indices are 32
  and 34, and neither is below p.
- `K=400,N=30,p=101,a=1`: the two smallest indices are 100 and 102; `a=1`
  is canceled by the numerator and is not a tail pole. Under the coordinate
  `x=a+p*z`, the surviving pullback poles include `z=-1` and `z=1`, so the
  second harmonic argument is 1, not 0.

These are within the inner range for a sufficiently large fixed cutoff M.
Thus the proof cannot infer that both harmonic terms vanish for every class,
and the asserted uniform `+6` limiting gain for all `x>=3` is unproved.
The erroneous pole identification is a counterexample to that proof step;
it is not by itself a valuation counterexample to the final gain theorem.

A repair must recompute the surviving harmonic residues for the actual two
smallest tail poles in every class. The sufficient condition `N<a<=p/2`
does ensure both `a,p-a` are tail poles. Restricting the gain to these classes
suggests the lower gain profile `6*max(0,1-2*alpha*x)`, rather than the constant
6. At `alpha=3/40` its integral against `x^(-3)` on `[3,infinity)` is
`121/1200`, rather than `1/3`. This is a proposed repair requiring a proof of
the local valuation inequalities, not a completed replacement theorem.
