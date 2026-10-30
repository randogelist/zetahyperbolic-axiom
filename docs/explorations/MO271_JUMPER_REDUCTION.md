# MO271 jumper reduction: the remaining theorem is purely 5 -> 7

## Evidence level

Mathematical structural reduction only. No new Lean build or axiom audit is asserted here.

Pinned upstream source: `mo271/Zeta5` commit `7fe736760f4b96bfdb4334b68e3b3124ecbe10b0`.

## 1. Weight-five seed is structurally available

For

```text
p5(n) = (k=2,m=3,N=3n,K=40n),
```

the MO271 Hankel determinant polynomial `Δ n` agrees entrywise with the ZH determinant polynomial `Real.delta (p5 n)`.

MO271's polynomial

```text
F n = S(n) * Δ(n)
```

is therefore a positive rational rescaling of the ZH determinant.

Its `main_estimate` gives a cofinal family of integer polynomials with degree `37n`, positive value at ζ(5), and quadratic exponential decay. Primitive minimality transfers this to the canonical ZH primitive polynomial at weight five.

Thus the ζ(5) seed can be treated as discharged once the exact cross-repository identity is formalized.

## 2. Canonical 40-profile families

Use shifted zero-based indices:

```lean
def family40 (k j : ℕ) : Real.Parameters :=
  ⟨k, 3, 3*(j+1), 40*(j+1)⟩
```

Then

```text
family40(2,j) has weight 5,
family40(3,j) has weight 7,
h = 37(j+1).
```

Write

```text
P5_j = primitivePolynomial (family40 2 j),
P7_j = primitivePolynomial (family40 3 j),
V5_j = P5_j(ζ(5)),
V7_j = P7_j(ζ(7)).
```

Positivity of the Gram determinant implies `V5_j>0` and `V7_j>0`.

## 3. Minimal transfer premise

The required jumper premise can be stated without mentioning MO271 internals:

```lean
def Transfer57_40 : Prop :=
  ∃ C57 : ℝ, 0 ≤ C57 ∧ ∃ j0 : ℕ, ∀ j ≥ j0,
    V7_j ≤
      Real.exp
        (C57 * ((j+1 : ℕ) : ℝ) * Real.log (j+3)) *
      V5_j
```

Equivalent `K`-scaled form:

```text
V7_j ≤ exp(C'_57 K_j log(K_j+2)) V5_j,
K_j = 40(j+1).
```

No quadratic transfer loss is needed; the raw adjacent Gram comparison already predicts `O(j log j)`.

## 4. MO271 seed plus transfer implies weight-seven decay

Assume the imported MO271 weight-five decay gives

```text
0 < V5_j ≤ exp(-c5 (j+1)^2)
```

for some fixed `c5>0` and all sufficiently large `j`.

Combine with `Transfer57_40`:

```text
V7_j
 ≤ exp(C57 (j+1) log(j+3)) · exp(-c5 (j+1)^2)
 = exp(-c5 (j+1)^2 + C57 (j+1) log(j+3)).
```

Since

```text
(j+1) log(j+3) = o((j+1)^2),
```

there exists `j1` such that for all `j≥j1`,

```text
C57 (j+1) log(j+3) ≤ (c5/2)(j+1)^2.
```

Hence

```text
0 < V7_j ≤ exp(-(c5/2)(j+1)^2).
```

With `K_j=40(j+1)`, this is

```text
0 < V7_j ≤ exp(-(c5/3200) K_j^2).
```

Therefore

```lean
GeneralIrrationality.NormalizedQuadraticDecay (family40 3)
```

holds, and the existing denominator-clearing theorem gives irrationality of ζ(7).

## 5. Lean root theorem target

```lean
theorem zeta7_decay_of_mo271_seed_and_transfer57
    (h5 : GeneralIrrationality.NormalizedQuadraticDecay (family40 2))
    (h57 : Transfer57_40) :
    GeneralIrrationality.NormalizedQuadraticDecay (family40 3)
```

followed by

```lean
theorem irrational_zeta7_of_mo271_jumper
    (h5 : GeneralIrrationality.NormalizedQuadraticDecay (family40 2))
    (h57 : Transfer57_40) :
    Irrational (Real.zeta 7)
```

The first theorem should be standard-only and independent of the MO271 implementation details. The MO271 bridge discharges `h5`; all new mathematics is concentrated in `h57`.

## 6. Three candidate realizations of `Transfer57_40`

### Route A — primitive normalization comparison

Prove directly

```text
P7_j(ζ(7))
 ≤ exp(C57 (j+1) log(j+3)) P5_j(ζ(5)).
```

This is the cleanest endpoint but requires control of the primitive-scale ratio.

### Route B — reuse the MO271 normalizer

Let `a_j>0` be the MO271 integral scale at weight five, so

```text
Q5_j = a_j Δ5_j ∈ ℤ[X].
```

Test whether

```text
a_j Δ7_j ∈ ℤ[X].
```

If yes, the same normalizer cancels from the raw Gram comparison, yielding `Transfer57_40` directly.

### Route C — correction factor

Define the least positive integer `d_j` clearing all coefficient denominators of `a_j Δ7_j`:

```text
Q7_j = d_j a_j Δ7_j ∈ ℤ[X].
```

It is sufficient to prove

```text
log d_j = O(j log j)
```

or, more generally,

```text
limsup (log d_j)/(j+1)^2 < c5.
```

Route C is likely the most computationally discoverable.

## 7. Immediate finite experiment

At `j=0`, equivalently MO271 index `n=1`, use

```text
N=3, K=40, h=37.
```

Compute:

1. the exact MO271 positive integral scale `a_0`;
2. the coefficient denominators of `a_0 Δ7_0`;
3. the correction factor `d_0`;
4. the prime-factor decomposition of `d_0`;
5. whether every active prime belongs to one of the MO271 small/inner/outer regimes.

Repeat for the next feasible indices and classify the growth of

```text
log d_j / ((j+1) log(j+3))
```

and

```text
log d_j / (j+1)^2.
```

The desired signature is bounded first ratio or vanishing second ratio.

## 8. Exact frontier

After the weight-five identity bridge, the adjusted ζ(7) route has only one unresolved theorem:

```text
Transfer57_40.
```

The current single-point coordinate admission is not used in this route. Its log correctly records that finite `GoodAt 0` is conditionally closed while cofinality and irrationality are not established.