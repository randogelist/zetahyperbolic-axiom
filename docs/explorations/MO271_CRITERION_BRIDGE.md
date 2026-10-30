# MO271 ζ(5) exploration I — integer-polynomial criterion bridge

## Scope

This branch isolates the final Diophantine endpoint of `mo271/Zeta5` and compares it with the existing Zetahyperbolic primitive-polynomial endpoint. It makes no new irrationality claim and is not registered as an A-Tier module.

Pinned upstream reference: `mo271/Zeta5` commit `7fe736760f4b96bfdb4334b68e3b3124ecbe10b0`.

## Upstream endpoint

`Apery/Criterion.lean` proves a general theorem of the following shape:

```lean
theorem irrational_of_eventually_exists_int_poly
    (ξ : ℝ) (d : ℕ → ℕ) (ε : ℕ → ℝ)
    (hε : ∀ b > 0, Tendsto (fun n => (b : ℝ) ^ d n * ε n) atTop (𝓝 0))
    (hQ : ∀ᶠ n in atTop, ∃ Q : ℤ[X],
      Q.natDegree ≤ d n ∧ 0 < aeval ξ Q ∧ aeval ξ Q ≤ ε n) :
    Irrational ξ
```

For ζ(5), the upstream specialization uses

```text
d(n) = 37 n
ε(n) = exp(-c n²), c > 0.
```

## Existing Zetahyperbolic endpoint

`src/MAIN_CHAIN_IRRATIONALITY.lean` already contains:

- `NormalizedQuadraticDecay` for the canonical primitive determinant polynomial;
- `normalizedQuadraticDecay_of_integral_rescalings`;
- `irrational_zeta_of_normalized_decay`;
- the concrete affine-family wrapper.

The two endpoints therefore have the same denominator-clearing spine. Their structural difference is where the integer polynomial comes from:

```text
MO271: arbitrary positive integral rescaling Q_n of F_n
ZH:    canonical positive primitive normalization P_n of Δ_n
```

## Primary theorem target

After identifying the two rational determinant families, prove a transport theorem with no analytic work:

```lean
theorem mo271_eventual_polynomials_to_zh_normalized_decay
    (p : ℕ → Real.Parameters)
    (Q : ℕ → ℤ[X])
    (scale : ℕ → ℚ)
    (hscale : ∀ n, 0 < scale n)
    (hid : ∀ n,
      (Q n).map (Int.castRingHom ℚ) =
        Polynomial.C (scale n) * Real.delta (p n))
    (hdecay : ∃ c > 0, ∀ᶠ n in atTop,
      |RealTransfer.evalReal (Q n) (Real.zeta 5)| ≤
        Real.exp (-c * ((p n).K : ℝ)^2)) :
    GeneralIrrationality.NormalizedQuadraticDecay p
```

This is expected to be an immediate application of
`normalizedQuadraticDecay_of_integral_rescalings` once the family identification is available.

## Index alignment

MO271 uses

```text
N = 3n, K = 40n, h = 37n, n ≥ 1.
```

The current Zeta357 candidate uses

```text
N_j = 3(j+1), K_j = 40(j+1), h_j = 37(j+1), j ≥ 0.
```

Use the exact reindexing

```text
n = j + 1.
```

No asymptotic loss is introduced.

## Questions to resolve

1. Is MO271's `F n` definitionally the same rational determinant polynomial as `Real.delta` at `k=2,m=3,N=3n,K=40n`?
2. If not definitionally equal, is it related by a positive rational basis-change scalar?
3. Does the upstream positivity convention agree with the positive primitive normalization used here?
4. Can the bridge avoid importing the whole MO271 tree by porting only `Criterion.lean`?

## Success condition

A successful branch ends with a small compiled theorem converting upstream eventual integer-polynomial data into `NormalizedQuadraticDecay`, with a standard-only theorem-level axiom audit. It does not need to reconstruct the MO271 normalizer or analytic estimate.