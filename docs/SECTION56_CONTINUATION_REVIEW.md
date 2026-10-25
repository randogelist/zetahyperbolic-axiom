# Section 5–6 continuation review

This review preserves the difference between a complete printed theorem, a proved component,
a corrected formula, and an unresolved proof obligation. A missing tactic is not a fatal blocker.
Compilation status is given by the final module receipts, not by this source review.

## Constructive additions

- `CentralFactorialSecant.lean`: actual repeated differential operators on `1/(2 cosh z)`,
  their all-order factorial closed form, final-derivative strict positivity on `z>0`, and
  annihilation of the first odd exponential modes. The finite multiplier sign is explicit.
  The termwise differentiated infinite series, accelerated asymptotic bound, identification
  with the coupled beta moment functional, and non-scalar/strict-Newton assertions remain
  independent obligations.
- `DyadicQuotientThreshold.lean`: actual square-pole denominator and shifted numerator,
  exact degree, zero polynomial quotient below the threshold, `6n` leading-block
  specialization, and `42n-1` full quotient degree bound. These facts alone do not prove
  dyadic integrality of residues or the irrationality estimate.
- `BeukersDenominator.lean`: actual rational dual constants, the adjacent moment identity,
  and the common least-common-multiple denominator `6*d_K^7`. Continuous integral
  realization remains distinct.
- `BetaHarmonicIndexObstruction.lean`: exact rational counterexamples to intermediate
  assertions in the printed 6.17 local valuation argument.
- `ExternalPi/` and `OddPiPowers.lean`: a candidate imported full Lindemann pi proof,
  its rational-power/linear-independence consequences, and the ordered beta-one series.
  See `provenance/external_pi_intake.json` for the source pin and adaptation record.
  No general beta/Euler closed-form identity is silently assumed.

## Corrections established from the actual formulas

### Theorem 6.13(1), equation (6.5), PDF pp. 43–44

The operator is `-D product_{r=1}^{k-1}((2r-1)^2-D^2)`. Applied to
`exp(-(2l+1)z)`, its multiplier is
`(2l+1) product((2r-1)^2-(2l+1)^2)`. The printed series instead writes every
factor in the reverse order. It therefore needs the prefactor `(-1)^(k-1)`.
At `k=2,l=1`, the actual product is `-8`, while the printed reversed product
is `8`. After the alternating-series coefficient `(-1)^l`, the actual first
surviving term is positive and the printed one negative. The closed form
itself is the correct positive expression. The finite differential identities
and sign discrepancy are formalized; they do not assume a series interchange.

Required repair: reverse the displayed factors or multiply the series by
`(-1)^(k-1)`. Then prove convergence and termwise differentiation, for example
uniform convergence of the exponentially decaying differentiated series on
`[epsilon,infinity)` for every positive epsilon. This repair is implementable.
The analytic identification with the full beta pencil and strict Newton clause
still requires its own proof.

### Theorem 6.15(2)(ii), PDF p. 46: exterior Christoffel rate

The printed factor `h^(-2k)` is incompatible with the fixed-weight exterior
Szegő asymptotic for every `k >= 1`. This diagnosis uses an established analytic
theorem; the Szegő theorem has not been imported into Lean and this paragraph
is not a kernel-checked asymptotic proof.

Put `t=u^2`. The Gram matrix is the monomial moment matrix on `(0,1)` for

```
W(t) = t^(N-1/2) (-log t)^(2k) / (2^(2k+1) (2k)! (1+t)).
```

It is a finite strictly positive weight. Under `x=2t-1`, its transformed weight
is `w(x)=W((x+1)/2)/2`. The Szegő condition holds: near `t=0`, `log W(t)`
is a linear combination of `log t`, `log(-log t)` and bounded terms; near
`t=1` it equals `2k log(1-t)` plus bounded terms. These are integrable against
`dt/sqrt(t(1-t))`. Equivalently `w(cos theta)|sin theta|` belongs to Szegő's
class G (finite positive integral and integrable absolute logarithm).

[Original source: G. Szegő, *Orthogonal Polynomials*, fourth edition (1975),
Theorem 12.1.2, equation (12.1.3), printed p. 297](https://people.math.osu.edu/nevai.1/SZEGO/szego%3Dszego1975%3Dops%3DOCR.pdf).
The theorem and equation were visually checked in the source PDF. It states
the exterior orthonormal-polynomial asymptotic with a nonzero analytic Szegő
factor and no power of the degree. In our coordinates `t=-1` means `x=-3`,
and the exterior conformal coordinate is `z=-(3+2 sqrt 2)`. Thus for some
nonzero real constant `A=A(k,N)`,

```
p_n(-1) / (-(3+2 sqrt 2))^n -> A.
```

Writing `R=3+2 sqrt 2`, the elementary geometric-series squeeze gives

```
(sum_{n=0}^{h-1} p_n(-1)^2) / R^(2h) -> A^2/(R^2-1),
(v_-^T G_h^-1 v_-)^-1 ~ (R^2-1)/A^2 * R^(-2h).
```

The latter inverse is exactly the rank-one root displacement stated in the
manuscript. Its ratio to `h^(-2k) R^(-2h)` therefore tends to infinity for
`k>=1`, contradicting the printed two-sided comparison. The required repair
is to delete `h^(-2k)` and state the positive-constant geometric asymptotic.
The `k=0` printed rate is consistent. The claimed endpoint logarithmic power
belongs to a different asymptotic regime and cannot alter a fixed exterior
point's degree-free Szegő factor. Formalizing the Szegő theorem or a sufficient
Jacobi-weight comparison remains an analytic development task, separate from
correcting this false manuscript statement.

### Theorem 6.17(3)(ii), PDF p. 49

The printed definition is `H_M^(beta,s)=sum_{j=0}^{M-1}(-1)^j/(2j+1)^s`.
The argument uses `2n0<q` to assert that `H_(2n0)` has no q-divisible denominator.
That implication is false: its odd denominators extend to `4n0-1`.
For the permitted choice `q=11,rho=n0=3`, the lower sum `H_6^(beta,2)` already
contains `1/11^2`; its reduced numerator is not divisible by 11 and its
reduced denominator is divisible by 11. The exact value is
`10956424/12006225`.

There is a stronger obstruction to the claimed invertible scalar leading block.
With the printed basis `x^(4rho)+2*x^(4(rho+(q+1)/2))`, later rows contain both
odd poles `q` and `3q` in the upper harmonic sum, and `q` in the lower sum.
Their leading diagonal coefficient is proportional to `5-4/3^s`, rather
than the asserted constant `4`. At weight `s=2`, the permitted prime `q=41`
divides `5*3^2-4`. The actual rational diagonal for `rho=11,n0=11,n1=32`
has valuation -1, whereas the displayed scalar-block argument requires -2.
The exact finite-arithmetic Lean statement says that multiplying that
rational diagonal by 41 gives a reduced rational with neither numerator nor
denominator divisible by 41.

This is a refutation of the supplied arithmetic proof steps, not a logical
refutation of the full theorem with its additional hypothetical integer
linear relation. A repair must recalculate every odd-pole class, and either
exclude additional primes or change the basis to restore an invertible
leading block. Altering only explanatory prose is insufficient. The concrete
basis change and resulting valuation theorem remain further mathematical work.

## Reassessment of all sixteen previously unformalized items

| Item | Work attempted / concrete remaining requirement | Status boundary |
| --- | --- | --- |
| 5.6 | Read the exact floor-function integrands and outer rational integral. The arithmetic partition must include all floor/min/max breakpoints; the inner tail and prime-sum limiting argument still require uniform estimates. | No counterexample established. Not called fatal. |
| 5.7 | Read the double-pole rational function and Hermite local-block proof. Existing finite Hermite machinery does not instantiate its explicit coefficients or p-adic valuations. Exact local numerator/residue valuations and minor expansion are missing. | Unproved arithmetic construction. |
| 6.1 | Checked the multiplicative fiber Jacobian and the harmonic divided-difference formula. The `d_K` arithmetic mechanism is now proved in 6.2 support; change-of-variables and exact p-adic pole extraction remain. | Unproved analytic/p-adic components. |
| 6.2 | Constructed least-common-multiple clearing for the actual dual constants and exact adjacent moment algebra. Need the two-variable Mellin integral realization, justified monotone convergence, and finite polynomial expansion to identify the complete integral. | New exact arithmetic components; no full-item claim. |
| 6.3 | Read the q-adic and finite-negative-mode construction. The dimension count is elementary, but orthogonality to finitely many negative modes does not by itself control the infinite negative tail. The printed concentration sentence supplies no signed-polynomial uniform dominance estimate. | Requires a rigorous positive-tail lemma; no counterexample established. |
| 6.5 | Checked the odd-square pole indexing and separate r=0/r>0 valuations. Needs actual Euler functional, q-integrality of quotient moments, exact single-pole valuations, and determinant dominant-term lemma instantiated to the family. | Precise p-adic obligations; not a compilation blocker. |
| 6.7 | Checked the paired-power Krein algebra and highest-weight local coefficient. Finite algebra is reusable, but convergence and existence of rational positive/negative subspaces need controlled tail/projection estimates. | Infinite analytic realization still unproved. |
| 6.8 | The b=0 clause requires Apéry; b≠0 and the effective bound depend on the actual 4.5 family estimates, including a=0,b=1. Finite Gram or nonvanishing statements cannot substitute for those estimates. | Downstream of unproved quantitative 4.4–4.5. |
| 6.11 | Proved the odd-square scaling identity and consecutive-product parity. The exact quotient threshold is addressed in 6.18. Euler distribution, prime-counting limits and the claimed strict linear growth need their stated uniform estimates. | New elementary support only. |
| 6.12 | Examined rational cutoff perturbation: finite-dimensional positive definiteness is open, so continuity would give rational cutoffs once a positive continuous Gram is established. The latter measure and q-adic compatibility are not yet instantiated. | Constructive continuity strategy, analytic realization required. |
| 6.13 | Constructed the all-order differential identity and actual exponential annihilation. Found and formalized the missing finite-product sign. Infinite differentiated-series convergence and coupled-pencil identification remain. | Literal formula requires correction; corrected components proved. |
| 6.14 | Read the even-pole scaling and comparison argument. Need actual beta derivative/moment integral identities and globally bounded ratios with endpoint limits. Finite cone algebra does not supply those estimates. | Analytic comparison unproved. |
| 6.15 | Investigated trusted external formal libraries; obtained a six-module pi-transcendence proof for porting. Ordered beta1 series is already in Mathlib. General beta/Euler evaluation and effective fixed-degree pi transcendence measure remain. The printed exterior h^(-2k) factor contradicts the Szegő theorem, as detailed above. | Pi dependency obtainable; asymptotic requires correction for k>=1. |
| 6.16 | Algebraic slope combination is finite, but the actual combined densities require 6.6/6.14. The highest-weight valuations require explicit residue estimates, not generic positive-matrix hypotheses. | Downstream analytic/arithmetic gaps remain. |
| 6.17 | Recomputed odd-harmonic indexing; q=11 lower-pole and q=41 leading-coefficient obstructions found. Requires revised local basis/primes plus infinite analytic realization. | Supplied local proof is incorrect; full conditional theorem not refuted. |
| 6.18 | Proved exact shifted-degree/quotient disappearance and weight-five specializations. Odd denominator harmonic sums alone do not clear residue denominators; full q-adic/2-adic multiplier proof remains. Irrationality rate depends on 4.5. | Exact degree components, not full arithmetic closure. |

## Retained partial results in the same sections

| Item | Original statement / retained proof / exact repair requirement |
| --- | --- |
| 5.1 | Original: the continuous two-variable Beukers measure has explicit diagonal zeta(7) and off-diagonal harmonic moments. Retained: actual rational dual constants and coefficient-Gram slope. Attempt: derive the adjacent harmonic difference and exact denominator from these constants. Missing: integrability, Mellin/log moment evaluation, interchange of the geometric sum and integral. Repair: establish the measure realization first; the finite pencil definition then follows by finite linearity. OPEN. |
| 5.2 | Original: dual hyperbolicity plus infinite Krein decomposition/cones. Retained: finite coefficient-row independence gives positive slope and unconditional finite real spectrum; explicit rank-one negative zeta7 example. Attempt: inspected the paired-power expansion and finite negative-mode construction used later in 6.3. Missing: convergent Krein expansion, infinite-rank and rational projection/tail bounds. Repair: prove a quantitative tail estimate before using projection to infer the cones. OPEN; finite algebra does not prove the infinite statement. |
| 5.3 | Original: beta4 Beukers measure and dual pencil. Retained: finite tensor/Gram algebra. Missing: convergence and evaluation of the actual continuous beta4 moments, then exact identification with the affine pencil. Repair: construct the signed density and prove its integral formulas before transferring finite spectral lemmas. OPEN. |
| 5.4 | Original: cancellation for the full rational functional on specified even pole pairs. Retained: generator identities. Repair: combine the representation-independent linear functional with the full-domain substitution and pole restrictions; Section2 domain work owns this bridge. OPEN until the exact operator identity is compiled. |
| 6.4 | Original: character/Vandermonde cancellation and beta hyperbolicity. Retained: exact raw residual sign `(-1)^N` and explicitly normalized positive finite model. Correction: a universal positive raw sign is false for odd N; orientation/normalization must be stated. Missing: actual beta analytic moment realization and q-adic nonvanishing. Repair: preserve the raw parity, define the oriented pencil, then prove measure and arithmetic identification. OPEN with stated sign correction. |
| 6.6 | Original: actual infinite multiweight density, comparison and universal signature. Retained: finite positive/semidefinite cone closure with a positive anchor. Missing: actual combined derivative density, positive-cone comparison estimates, arithmetic multiplier and asymptotics. Repair: instantiate component analytic moments and prove uniform comparison before invoking finite cone results. OPEN. |
| 6.9 | Original: actual triple-pole/multiweight determinant and q-adic valuation. Retained: exact finite Hermite-jet/block determinant algebra. Attempt: inspected the actual highest Laurent coefficient and formal degree constraints. Missing: actual Hermite table invertibility over the required local ring, coefficient nonvanishing/valuation and determinant leading-block domination. Repair: instantiate confluent interpolation for the distinct nodes, then separately prove each local arithmetic coefficient. OPEN. |
| 6.10 | Original: finite potential-gap identity plus quadratic asymptotic claims. Retained: finite determinant/spectral identities. Missing: one-variable logarithmic potential limit and its strict gap; for the two-variable part, quantitative integral coefficient-size bounds and rank in the growth family. Repair: prove a finite Hadamard upper bound and integer determinant lower bound, then squeeze the normalized logarithm; the one-variable limit needs the actual equilibrium calculation. OPEN. |

## External proof investigation for Theorem 6.15

Pinned Mathlib has `irrational_pi` and Lindemann's `AnalyticalPart`, but no complete
pi-transcendence endpoint. A primary-source search located:

1. [gotrevor/lean-formalizations](https://github.com/gotrevor/lean-formalizations/tree/a216ec2d29bbb3f76403a62358e9ca606d0b42f1),
   `src/LeanFormalizations/NumberTheory/Transcendence/PiTranscendental.lean`.
   The exact endpoint is `LeanFormalizations.Transcendence.transcendental_pi_axiomClean :
   Transcendental ℚ Real.pi`. Its transitive project closure has six files and uses
   Mathlib's analytic Lindemann engine plus symmetric-polynomial/conjugate arguments.
   It is Apache-2.0, originally Lean 4.31.0. The sources are obtainable and a 4.33.0 port
   is attempted here; comments containing historical axiom names are not active declarations.
2. [frenzymath/PiIrrationalityMeasure](https://github.com/frenzymath/PiIrrationalityMeasure/tree/3ee5d4d080b440469d331a2fb3862aee88c23ca0)
   targets the exact current Lean and Mathlib pins. Its README identifies 309 proof
   modules and an unconditional bound `IrrationalityMeasure Real.pi <
   7101862832357/10^12`. The challenge file intentionally contains placeholders;
   only the independent Solution proof closure would be admissible. This is a potential
   source for the k=0 effective estimate, not for all odd powers. It has not been imported
   or certified by this project.

For all odd powers the exact further requirement is an effective, degree-dependent
lower bound for nonzero integer polynomials evaluated at pi (or directly for
`q_k*pi^(2k+1)-a/b`), together with the nonzero rational Euler coefficient identity.
Ordinary irrationality measure of pi alone does not imply such a bound for its powers.
No matching complete Lean source was found by the targeted search. This is a located
missing mathematical dependency, not a proof of impossibility; a formal Mahler measure
argument or an independently audited external implementation would supply it.
