# MO271 ζ(5) exploration II — normalization and primitive-polynomial bridge

## Scope

This branch studies the exact algebraic relation between the MO271 ζ(5) determinant polynomial and the canonical primitive determinant polynomial in Zetahyperbolic. It makes no new irrationality claim and is not registered as an A-Tier module.

Pinned upstream reference: `mo271/Zeta5` commit `7fe736760f4b96bfdb4334b68e3b3124ecbe10b0`.

## Upstream normalization

`Apery/Norm.lean` defines a positive rational normalizer

```lean
mN (n : ℕ) : ℚ
```

from local prime exponents and proves, for `n ≥ 1`, that there is an integer polynomial obtained from

```text
mN(n) · F_n.
```

The normalizer combines small-prime, inner-range and outer-range valuation bounds. The key endpoint is not merely integrality: `Apery/Growth.lean` also controls `log mN(n)` quadratically.

## Existing canonical normalization

Zetahyperbolic constructs, for every nonzero rational determinant polynomial `Δ`, a positive primitive integer polynomial `P` and positive rational scale `s` with

```lean
P.map (Int.castRingHom ℚ) = C s * Δ.
```

The theorem

```lean
primitiveNormalization_abs_eval_int_le
```

shows that any other positive integral rescaling `Q = C a * Δ` is an integer multiple of `P` in the relevant sense, hence

```text
|P(x)| ≤ |Q(x)|.
```

This is the exact structural mechanism needed to import the MO271 decay estimate into the canonical ZH polynomial.

## Central identity target

For `n ≥ 1`, define the ZH parameter object

```lean
p5 n := ⟨k := 2, m := 3, N := 3*n, K := 40*n⟩.
```

Prove one of the following, in decreasing order of strength.

### Target A — definitional identity

```lean
Apery.F n = Real.delta (p5 n)
```

### Target B — positive scalar identity

```lean
∃ c : ℚ, 0 < c ∧
  Apery.F n = Polynomial.C c * Real.delta (p5 n)
```

### Target C — invertible basis-change identity

```lean
∃ A B : Matrix (Fin (37*n)) (Fin (37*n)) ℚ,
  Matrix.det A ≠ 0 ∧ Matrix.det B ≠ 0 ∧
  Apery.pencil n =
    BasisInvariance.changeBasisPencil (Real.pencil (p5 n)) A B
```

Target C implies Target B by determinant multiplicativity. The positive sign must then be fixed by evaluation at ζ(5).

## First finite comparison

Use `n = 1` as the smallest nontrivial exact test:

```text
N = 3, K = 40, h = 37.
```

Compare:

1. rational determinant polynomial coefficients;
2. primitive integer coefficient vectors;
3. positive normalization scales;
4. leading coefficient sign;
5. evaluation sign at ζ(5).

The existing candidate miner already generated the ZH degree-37 primitive polynomial for this geometry. This provides a direct finite comparison point against MO271's `F 1` and its integer rescaling.

## Structural experiments

### Experiment 1 — entry-by-entry convention map

Build a table comparing:

```text
MO271 moment functional / pole terms / basis
ZH    moment functional / pole terms / basis.
```

Classify every discrepancy as:

- exact equality;
- row/column basis change;
- constant scalar;
- sign convention;
- index shift.

### Experiment 2 — primitive association

Without proving full polynomial equality, try to prove that the two primitive integer polynomials are associated:

```lean
P_MO n = P_ZH n ∨ P_MO n = -P_ZH n.
```

Positivity at ζ(5) should eliminate the negative alternative.

### Experiment 3 — normalizer domination

Let `Q_MO n` be the integral MO271 polynomial. Prove directly:

```lean
|P_ZH n (ζ(5))| ≤ |Q_MO n (ζ(5))|.
```

This may require only a positive scalar identity, not a full coefficient-by-coefficient equality.

## Success condition

A successful branch proves a standard-only theorem of the form

```lean
theorem mo271_integral_rescaling_is_zh_rescaling
    (n : ℕ) (hn : 1 ≤ n) :
    ∃ a : ℚ, 0 < a ∧
      (Apery.integralPolynomial n).map (Int.castRingHom ℚ) =
        Polynomial.C a * Real.delta (p5 n)
```

Once available, the existing primitive-minimality theorem transfers MO271 decay to the canonical ZH family automatically.