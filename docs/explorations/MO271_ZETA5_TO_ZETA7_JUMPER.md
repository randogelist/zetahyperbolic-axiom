# MO271 ζ(5) exploration IV — a structural ζ(5) → ζ(7) jumper

## Scope

This branch asks whether the completed MO271 ζ(5) arithmetic construction can seed the existing adjacent-weight Gram comparison and thereby isolate a finite, explicit ζ(5) → ζ(7) transfer problem. It makes no ζ(7) irrationality claim.

Pinned upstream reference: `mo271/Zeta5` commit `7fe736760f4b96bfdb4334b68e3b3124ecbe10b0`.

## Starting point

MO271 proves, for the profile

```text
m = 3, N = 3n, K = 40n, h = 37n,
```

an eventual family of integer polynomials `Q5_n` with

```text
deg Q5_n = 37n,
0 < Q5_n(ζ(5)) < exp(-c5 n²)
```

for some explicit proved `c5 > 0`.

The ZetaBetaHankel work already proves an adjacent raw Gram comparison of the form

```text
G7_n / G5_n = exp(O(n log n)).
```

At the quadratic scale, the analytic determinant shift therefore costs zero:

```text
n⁻² log(G7_n / G5_n) -> 0.
```

## Exact unresolved factor

Write schematically

```text
P5_n(ζ(5)) = G5_n / L5_n,
P7_n(ζ(7)) = G7_n / L7_n,
```

where `Pj_n` is the canonical primitive polynomial value and `Lj_n` collects the exact positive arithmetic normalization/content factor.

Then

```text
P7_n(ζ(7)) / P5_n(ζ(5))
  = (G7_n / G5_n) * (L5_n / L7_n).
```

The raw Gram ratio is already subquadratic. The decisive question is therefore:

```text
Is log(L5_n / L7_n) = o(n²),
```

or at least

```text
limsup n⁻² log(L5_n / L7_n) < c5?
```

## Structural reuse from MO271

The upstream normalizer is built prime-by-prime from three regimes:

1. small primes;
2. an inner range with water-filling allocation;
3. an outer range with rank loss.

The first exploration is to parameterize this machinery by odd weight `k` rather than hard-coding weight five.

Proposed abstractions:

```lean
structure WeightArithmeticData (k n p : ℕ) where
  localMomentValuation : ℤ
  smallPrimeBound : ℤ
  innerAllocationBound : Option ℤ
  outerRankBound : Option ℤ

noncomputable def LpWeight (k n p : ℕ) : ℤ := ...
noncomputable def mNWeight (k n : ℕ) : ℚ :=
  ∏ p ≤ 2*(37*n), (p : ℚ)^(-LpWeight k n p)
```

Weight five must recover the upstream definitions exactly.

## Four finite experiments

### Experiment A — hard-coded dependency inventory

Classify every theorem used by `integral_mN` and `growth_mN` as:

- weight-independent;
- polynomial in `k`;
- special to `k=2`;
- relying on a numerical constant that must be recomputed for `k=3`.

### Experiment B — local valuation comparison

For each prime regime, seek a bound

```text
LpWeight 3 n p ≥ LpWeight 2 n p - E(n,p)
```

with

```text
Σ_{p≤74n} E(n,p) log p = o(n²).
```

This would prove subquadratic normalizer loss directly.

### Experiment C — finite prime-window runner

For moderate `n`, compute exact values of

```text
log(mNWeight 2 n / mNWeight 3 n) / n²
```

and decompose the result by prime regime. The goal is not numerical proof, but discovery of the dominant obstruction and a candidate symbolic bound.

### Experiment D — primitive-content comparison

After identifying the MO271 and ZH weight-five families, compare

```text
content(Q5_n), leadingCoeff(P5_n), leadingCoeff(P7_n)
```

and test whether the ratio can be expressed through the same local prime exponents.

## Target transfer theorem

A successful arithmetic comparison should yield constants `C57 ≥ 0` and `n0` such that

```lean
∀ n ≥ n0,
  0 < P7_n(ζ(7)) ∧
  P7_n(ζ(7)) ≤
    Real.exp (C57 * n * Real.log (n+2)) * P5_n(ζ(5)).
```

Combined with the MO271 ζ(5) decay, this gives positive quadratic decay at ζ(7):

```text
P7_n(ζ(7)) < exp(-(c5-o(1)) n²).
```

The existing integer-polynomial criterion would then imply ζ(7) irrationality.

## Safety boundary

None of the following is asserted on this branch:

- a weight-seven integral normalizer;
- a proved primitive-content comparison;
- a cofinal ζ(7) certificate stream;
- irrationality of ζ(7).

The branch exists to turn the broad transfer problem into a concrete prime-by-prime comparison against a completed ζ(5) baseline.