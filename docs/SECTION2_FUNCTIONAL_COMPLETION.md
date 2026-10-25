# Exact rational-function completion: 2.2, 2.3, 5.4

The seven modules `Section2PoleLinearSpace`, `Section2TauLinear`,
`Section2RatFuncReflection`, `Section2RatFuncTranslation`,
`Section2RatFuncPullback`, `Section2DifferenceDerivative`, and `Section2MuLinear`
under `src/LeanPaper/` have passed targeted Linux Lean 4.33 compilation with the
pinned Mathlib. The repository-wide transitive axiom audit is a separate acceptance
gate; this review does not assert that gate has already run for these sources.

## Semantic correspondence

| Printed result | Exact verified endpoint and meaning | Verdict |
|---|---|---|
| Lemma 2.2, PDF p.4, (2.5) | `Section2MuLinear.mu_pullback`, together with `pullback_coe`: on the exact `MuDomain`, the constructed linear map μ equals τ of the actual rational function `X^(2*k+1) * R(-X^2)`, for `1 ≤ k`. `MuSpace` has carrier definitionally equal to `MuDomain`, whose reduced-denominator characterization was already proved. | Complete printed statement. |
| Lemma 2.3(1), PDF p.5, (2.6) | `Section2RatFuncReflection.tau_reflection`: every rational function in the entire simple-integer-pole subspace satisfies the reflection identity. The operator is a field substitution, with its polynomial/pole action and domain preservation proved. | Complete printed clause. |
| Lemma 2.3(2), PDF p.5, (2.7) | `Section2RatFuncTranslation.tau_difference_pole` gives the exact polynomial-valued difference for `r ≠ 0,1`; `tau_difference_derivative` identifies it with the actual real derivative iterated `2*k` times at zero, divided by `(2*k)!`. `Section2DifferenceDerivative.tau_difference_span_derivative` extends this to every finite rational linear combination of these admissible poles. | Complete printed clause and its stated linear-span extension. |
| Theorem 5.4, PDF p.25, (5.5) | `Section2TauLinear.evenPolePair_cancellation`, with `evenPolePair_coe`: τ of the actual rational difference `(X-j)^(-1)-(X+j)^(-1)` is `C((j^(2*k+1))^(-1))`, including `j=1`. | Complete final theorem statement; printed proof needs the corrections below. |

All namespaces above are prefixed by `LeanPaper.`. The target μ and τ are the
same Bernoulli/harmonic functionals as the existing sources, not alternative
functionals defined to make a desired equality hold. Their equality with the
prior functions is proved by `Section2MuLinear.mu_eq_existing` and
`Section2TauLinear.tau_eq_existing`.

## Integrity and exact boundaries

- `Section2PoleLinearSpace.liftMoment` is a linear map on actual `RatFunc ℚ`
  elements. Choice selects partial-fraction data; independently proved
  representation uniqueness makes the value independent of that choice.
- `Section2MuLinear.MuSpace` excludes the zero pole exactly. The ambient linear
  extension in `Section2LagrangeFunctional.mu` is only used after restriction
  to this exact domain; arbitrary complement values are never paper inputs.
- `weightedPullback_coe` proves the literal rational-function substitution.
  The output is not a symbolic name with the desired moment imposed.
- The derivative theorem uses Mathlib's genuine `deriv`/`iteratedDeriv` over
  the reals. At every included pole label `r`, `r ≠ 0` gives regularity at the
  evaluation point; no singular derivative is used in the paper endpoint.
- These completions assert no Mellin-measure realization, asymptotic estimate,
  irrationality result, or closure of later manuscript sections.

## Required printed-proof corrections

1. Lemma 2.3's proof says only odd monomial degrees contribute. This omits the
   Bernoulli `B₁` exception: `tauMonomial 1 2 = -1/2`, formally proved by
   `Section2TauLinear.even_monomial_Bernoulli_exception`. The statement of the
   reflection identity is nevertheless correct; its proof must retain this
   exceptional term (the established binomial-convolution proof does so).
2. In Theorem 5.4, the reflected-pole intermediate equality must be
   `τ((x+j)^(-1)) = τ((x-(j-1))^(-1))`, with a plus sign.
   `evenPolePair_reflection_relation` proves that equality. The substitution
   itself contributes a minus sign, which cancels the minus from τ reflection.
3. The special `j=1` polynomial-division display must use the **sum** of the
   two simple poles, not the even difference `E₁`. The printed difference gives
   `0=1` at `k=1,x=0`, ruled out by
   `printed_evenPair_division_fails_at_zero`. The correct division is proved
   uniformly by `Section2RatFuncPullback.pole_division_identity`.
4. The final `j=1` cancellation value is correctly `1`. It follows directly
   from the stated harmonic pole moments, as in the new proof, without the
   incorrect special-case division argument.

## Source provenance

The canonical project definitions and previously verified partial-fraction
uniqueness are preserved. Read-only comparison used the corresponding
`snditeration` Section2 sources at commit
`78472dfe8b5d4fe91ac69e726b69a6b6b2d53e5e`. No external working-directory import
or external compilation receipt is used as proof evidence for these modules;
the adapted code was compiled in this project's own pinned environment.
