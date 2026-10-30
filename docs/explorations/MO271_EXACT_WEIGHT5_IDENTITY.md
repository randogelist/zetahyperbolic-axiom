# MO271 exact weight-five identity

## Evidence level

Mathematical structural derivation only. No new Lean compilation or theorem-level axiom audit is asserted by this file.

Pinned upstream source: `mo271/Zeta5` commit `7fe736760f4b96bfdb4334b68e3b3124ecbe10b0`.

## Parameter object

For `n : ℕ`, define

```lean
def p5 (n : ℕ) : ManuscriptChain.Real.Parameters :=
  ⟨k := 2, m := 3, N := 3*n, K := 40*n⟩
```

Then

```text
p5(n).weight = 5,
p5(n).h = 40n - 3n = 37n.
```

MO271 uses exactly the same profile:

```text
K = 40n, N = 3n, h = 37n.
```

## 1. Equality of the denominator polynomials

MO271 defines

```text
Apery.D r = ∏_{j=1}^r (t+j²).
```

Zetahyperbolic defines

```text
Real.D r = ∏_{j=0}^{r-1} (t+(j+1)²).
```

Hence, after the elementary reindexing `j ↦ j+1`,

```text
Apery.D r = Real.D r.
```

Moreover,

```text
D_(40n) = D_(3n) · tailD(p5 n),
```

where

```text
tailD(p5 n) = ∏_{a=3n+1}^{40n}(t+a²).
```

## 2. Equality of the polynomial moments

MO271 defines

```text
μmono(e)
 = (-1)^e B_(2e+2) (2e+3)(2e+4)(2e+5) / 24.
```

The general ZH moment at `k=2` is

```text
monomialMoment 2 e
 = (-1)^e B_(2e+2) (2e+5)! / (4! (2e+2)!).
```

Since

```text
(2e+5)!/(2e+2)! = (2e+3)(2e+4)(2e+5)
```

and `4! = 24`,

```text
Apery.μmono e = Real.monomialMoment 2 e.
```

By linearity,

```text
Apery.μpoly q = Real.polynomialMoment 2 q
```

for every rational polynomial `q`.

## 3. Equality of the harmonic and pole data

MO271 defines

```text
H5(a) = ∑_{v=1}^a v^(-5),

poleValue(a)
 = a^4 (X-H5(a)) - 1/4 + 1/(2a).
```

ZH gives

```text
harmonic 5 a = ∑_{v=1}^a v^(-5),

poleConstant 2 a
 = -a^4 harmonic(5,a) + 1/(2a) - 1/4,

slope = a^(2·2) = a^4.
```

Therefore

```text
Apery.H5 a = Real.harmonic 5 a,

Apery.poleValue a
 = C (Real.poleConstant 2 a) + C (a^4) * X.
```

## 4. Cancellation of the common `D_(3n)` factor

The `(i,j)` numerator used by MO271 is

```text
P_MO = D_(3n)^6 · t^(i+j),
```

and its denominator is `D_(40n)`.

Using

```text
D_(40n) = D_(3n) · tailD(p5 n),
```

the rational function becomes

```text
P_MO / D_(40n)
 = D_(3n)^5 · t^(i+j) / tailD(p5 n).
```

The reduced numerator on the right is exactly

```text
Real.numerator (p5 n) i j
```

because `2*m-1 = 5` when `m=3`.

The polynomial quotients therefore agree:

```text
(P_MO /ₘ D_(40n))
 = Real.quotient (p5 n) i j.
```

A Lean proof can use uniqueness of division by a monic polynomial: if

```text
A = q·B + r,  degree(r)<degree(B),
```

then multiplying by the common monic factor `D_(3n)` gives the division decomposition for `D_(3n)A` by `D_(3n)B` with the same quotient `q`.

## 5. Equality of residues

For `1 ≤ a ≤ 3n`,

```text
P_MO(-a²)=0,
```

so the corresponding MO271 residue terms vanish.

For `3n < a ≤ 40n`, differentiate

```text
D_(40n) = D_(3n) · tailD.
```

At the root `t=-a²` of `tailD`, the product rule gives

```text
D_(40n)'(-a²)
 = D_(3n)(-a²) · tailD'(-a²).
```

Hence

```text
P_MO(-a²) / D_(40n)'(-a²)
 = D_(3n)(-a²)^5 (-a²)^(i+j) / tailD'(-a²),
```

which is exactly

```text
Real.residue (p5 n) i j a.
```

Thus the full MO271 pole sum over `1 ≤ a ≤ 40n` reduces to and agrees with the ZH sum over

```text
3n+1 ≤ a ≤ 40n.
```

## 6. Entrywise matrix identity

Combining polynomial-part equality, residue equality and pole-value equality yields

```text
Apery.μX (40*n)
  (Apery.D (3*n)^6 * t^(i+j))
=
Real.pencil (p5 n) i j.
```

Therefore, after the definitional identification of the index types `Fin (37*n)` and `Fin ((p5 n).h)`,

```text
Apery.G n = Real.pencil (p5 n).
```

## 7. Determinant identity

Taking determinants gives the exact rational-polynomial identity

```text
Apery.Δ n = Real.delta (p5 n).
```

This is stronger than a basis-change or scalar-equivalence claim: the two determinant polynomials are the same polynomial after unfolding the respective presentations.

## 8. MO271's `F` is a positive rescaling of the ZH determinant

MO271 defines

```text
Apery.F n = C (Apery.S n) * Apery.Δ n
```

and proves

```text
0 < Apery.S n.
```

Consequently,

```text
Apery.F n
 = C (Apery.S n) * Real.delta (p5 n),
```

with a positive rational scale.

## 9. Immediate transport of the MO271 main estimate

MO271 proves eventually that there are `Q_n : ℤ[X]` and `c'_n : ℚ_{>0}` with

```text
Q_n.map (Int.castRingHom ℚ)
 = C c'_n * Apery.F n,

0 < Q_n(ζ(5)) < exp(-c n²)
```

for one fixed `c>0`.

Using the exact identity above,

```text
Q_n.map (Int.castRingHom ℚ)
 = C (c'_n * Apery.S n) * Real.delta (p5 n),
```

and the new scale is still positive.

Therefore the existing theorem

```lean
GeneralIrrationality.normalizedQuadraticDecay_of_integral_rescalings
```

applies directly. Since `K=40n`, the rate conversion is

```text
exp(-c n²) = exp(-(c/1600) K²).
```

Thus the MO271 main estimate should imply the canonical ZH statement

```lean
NormalizedQuadraticDecay (fun n => p5 (n+1)).
```

No primitive-content conjecture is needed at weight five.

## 10. Lean theorem targets

```lean
theorem mo_D_eq_real_D (r : ℕ) :
  Apery.D r = Real.D r

theorem mo_monomialMoment_eq (e : ℕ) :
  Apery.μmono e = Real.monomialMoment 2 e

theorem mo_poleValue_eq_real (a : ℕ) :
  Apery.poleValue a =
    Polynomial.C (Real.poleConstant 2 a) +
      Polynomial.C ((a : ℚ)^4) * Polynomial.X

theorem mo_G_eq_real_pencil (n : ℕ) :
  Apery.G n = Real.pencil (p5 n)

theorem mo_delta_eq_real_delta (n : ℕ) :
  Apery.Δ n = Real.delta (p5 n)

theorem mo_F_eq_positive_scale_real_delta (n : ℕ) :
  Apery.F n = Polynomial.C (Apery.S n) * Real.delta (p5 n)

theorem mo271_main_estimate_implies_zh_weight5_decay :
  GeneralIrrationality.NormalizedQuadraticDecay
    (fun j => p5 (j+1))
```

## Consequence for the jumper project

The ζ(5) seed is no longer an open part of the jumper once this bridge is formalized. The remaining new mathematical obligation is solely the adjacent weight-five to weight-seven transfer for the canonical `K=40n` family.