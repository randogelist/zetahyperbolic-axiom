# MO271 ζ(5) exploration III — cofinal certificate engine

## Scope

This branch treats the completed MO271 ζ(5) formalization as a benchmark instance of the structured certificate architecture developed in this repository. It makes no new theorem claim until the determinant-family bridge is proved.

Pinned upstream reference: `mo271/Zeta5` commit `7fe736760f4b96bfdb4334b68e3b3124ecbe10b0`.

## Upstream theorem chain

The upstream chain is:

```text
local p-adic valuation bounds
  -> positive rational normalizer mN(n)
  -> integral polynomial Q_n
  -> real determinant upper bound
  -> quadratic decay main_estimate
  -> general integer-polynomial criterion
  -> Irrational ζ(5).
```

`Apery/MainEstimate.lean` proves:

```lean
∃ c > 0, ∀ᶠ n in atTop, ∃ Q : ℤ[X],
  Q.natDegree = 37*n ∧
  0 < Q(ζ(5)) ∧
  Q(ζ(5)) < exp(-c*n²),
```

with the additional fact that `Q` is a positive rational multiple of the rational determinant polynomial `F n`.

`Apery/Main.lean` feeds this directly into the general denominator-clearing criterion and proves ζ(5) irrationality.

## Structured-certificate interpretation

For every sufficiently large `n`, define a certificate node

```text
W_n = (
  index          := n,
  polynomial     := Q_n,
  degreeBound    := 37*n,
  valueUpper     := exp(-c*n²),
  positivity     := 0 < Q_n(ζ(5)),
  integrality    := Q_n ∈ ℤ[X]
).
```

Its denominator reach is any `B_n` satisfying

```text
B_n^(37*n) * exp(-c*n²) < 1.
```

For example, every fixed

```text
0 < γ < c/37
```

gives eventual reach

```text
B_n = floor(exp(γ*n)).
```

Hence the upstream proof is not merely an irrationality proof: it is an explicit cofinal stream of finite denominator-exclusion certificates.

## Target interface in this repository

Introduce a reusable structure:

```lean
structure CofinalPolynomialCertificateEngine (ξ : ℝ) where
  polynomial : ℕ → ℤ[X]
  degreeScale : ℕ → ℕ
  upper : ℕ → ℝ
  start : ℕ
  degree_le : ∀ n ≥ start, (polynomial n).natDegree ≤ degreeScale n
  value_pos : ∀ n ≥ start, 0 < evalReal (polynomial n) ξ
  value_le : ∀ n ≥ start, evalReal (polynomial n) ξ ≤ upper n
  cofinal_squeeze : ∀ b > 0,
    Tendsto (fun n => (b : ℝ)^(degreeScale n) * upper n) atTop (𝓝 0)
```

Then prove once:

```lean
theorem irrational_of_cofinal_engine
    (E : CofinalPolynomialCertificateEngine ξ) : Irrational ξ
```

The MO271 proof should instantiate this with

```text
ξ             = ζ(5)
polynomial n  = chosen Q_n
degreeScale n = 37*n
upper n       = exp(-c*n²).
```

## Bridge to canonical primitive certificates

After the normalization bridge is proved, define a second engine using the canonical primitive ZH polynomial `P_n`. Primitive minimality gives

```text
0 < P_n(ζ(5)) ≤ Q_n(ζ(5)) < exp(-c*n²).
```

This would produce:

```lean
GeneralIrrationality.AffineFamilyDecay 2
```

for the exact `N=3n, K=40n, m=3` family, after the index convention is aligned.

## Comparison with the current n=0 candidate

The current candidate package establishes a single finite point at

```text
n = 0, N = 3, K = 40, h = 37
```

conditional on six semantic coordinate fields. The MO271 theorem supplies an eventual cofinal family for the shifted indices `n ≥ 1`, but in a separate formalization and polynomial presentation.

The important structural question is therefore not whether ζ(5) has a cofinal certificate family—it does upstream—but whether that family is the same canonical determinant family used here.

## Success condition

A successful branch produces two compiled standard-only results:

```lean
theorem mo271_has_cofinal_certificate_engine :
  CofinalPolynomialCertificateEngine zeta5
```

and, after the determinant-family bridge,

```lean
theorem zh_affine_family_decay_five :
  GeneralIrrationality.AffineFamilyDecay 2
```

The latter would close the ζ(5) instance of the canonical ZH framework unconditionally, independently of the finite `n=0` custom admission.