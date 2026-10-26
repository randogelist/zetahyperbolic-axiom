# Exact semantic review of the already listed Chapter 4 alternatives

Reviewed the fixed README text for 4.1.alt, 4.4.alt, 4.5.alt, 4.7.alt and
4.8.alt, against the present source declarations. This is a correspondence
review only: receiving compilation and the transitive axiom audit remain
separate prerequisites for A-Tier. No target text or source was changed here.

## Complete fixed-target match: 4.1.alt only

### 4.1.alt — existential / effective-data split

The fixed alternative explicitly separates the eventual-hypothesis result
from the computable-threshold result. Both branches are present:

- `LeanPaper.Section4TransferComplete.spectral_transfer_real_exponent`:
  arbitrary `Q : Nat -> Int[X]`, center `xi`, positive real `lam, epsilon, rho`,
  and every real `mu > lam*rho/epsilon`; eventual degree, nonzero quadratic
  center decay and separation of all actual complex roots imply an existential
  denominator onset. The lattice version is
  `LeanPaper.Section4TransferComplete.spectral_transfer_lattice`, with arbitrary
  fixed positive lattice modulus `d0`.
- `LeanPaper.Section4EffectiveBudget.effective_spectral_measure`: explicit
  natural onset `n0`, natural exponent `mu`, and rational rate/margin data
  `lam, epsilon, rho, c, sigma` satisfying `lam/c < epsilon`, `rho < sigma`,
  `sigma*c <= mu`, `c>0`, `sigma>0`, `lam>=0`; the corresponding bounds hold
  at every index at least `n0`. Its conclusion is `RationalMeasure xi mu`
  at the actual natural-number `denominatorThreshold n0 lam epsilon rho c sigma`.
  That definition uses only rational arithmetic, natural ceilings, maxima,
  and a power of 3. The effective branch is specifically the rational-data,
  natural-exponent construction named in the fixed README row; do not expand
  the claim to an algorithm from arbitrary unspecified real input data.

No analytic rate, center-decay assertion, or computable onset is smuggled into
the existential branch. This is an exact whole-alternative match.

## Generic transfer coverage, without an assembled exact alternative certificate

### 4.4.alt — conditional manuscript-family measure: keep Partial

The fixed row explicitly assumes the integer-polynomial family, degree bound,
nonzero quadratic center decay, root separation, effective onsets, certified
rational rate margins, and the strict threshold below 25687. Its conclusion
is conditional on those inputs, so missing proofs of the original numerical
family bounds are not missing premises of this already conditional alternative.

The relevant generic implication is supplied by the universally quantified
`Section4EffectiveBudget.effective_spectral_measure`. The required specialization
for the given `K=30*n` family would be:

| Theorem argument | Fixed alternative's datum |
| --- | --- |
| `Q` | `fun n => Q_K (30*n)` for the stated actual integer family |
| `xi` | `ManuscriptChain.Real.zeta 5` |
| `mu` | `25687` |
| `lam` | `30*lam_original` |
| `epsilon` | `900*epsilon_original` |
| `rho` | `30*rho_original` |
| `c` | `c_original/30` |
| `sigma` | `30*sigma_original` |
| `n0` | the supplied effective index onset (or any larger computable one) |

The rate ratio and certified margin product are unchanged by this exact
reindexing: `(30*lam)*(30*rho)/(900*epsilon)=lam*rho/epsilon` and
`(30*sigma)*(c/30)=sigma*c`. The three supplied bounds become exactly the
three theorem hypotheses after natural casts are distributed. There is no
additional mathematical assumption. The existential statement at the exact
lattice is also directly `spectral_transfer_lattice` with `d0=30, mu=25687`.

This mapping explains why no new analytic argument is needed for the conditional
implication. However, it is not an assembled Lean declaration for the actual
`K=30*n` family and its effective numerical measure. The mapped hypothesis
casts, effective onset, rational margins and family identity have not been
registered together as that exact endpoint. Under the inventory's exact-
statement evidence boundary, retain this alt as Partial rather than promote
it from the generic transfer alone. The missing original numerical estimates
remain separate from this formal assembly gap.

### 4.8.alt — cluster-restricted exclusion: keep Partial

Subject to receiving CI for the repaired source, the denominator component
is `LeanPaper.Section4RationalCluster.eventual_rational_cluster_exclusion`:

- Input: positive measure exponent `mu`, positive cluster rate `tau`, and
  an eventual rational approximation measure with onset `b0`.
- Input for each candidate rational point: `b>0` and the independent upper
  closeness `abs(xi-a/b) <= exp(-tau*K)`.
- Output: eventually in `K`, `exp((tau/mu)*K) < b` for every such rational
  point, including all positive denominators below `b0`. Roothood is an
  optional additional premise; the proved assertion holds for every rational
  point in that disk and hence every rational root there.

The arithmetic/approximation measure can mathematically be supplied by the
transfer theorems under their stated family bounds. No implication from a lower
root-distance bound to upper closeness is used, and no exclusion outside the
disk is claimed. However, the new theorem receives `hmeasure` directly. No
existing actual-family endpoint assembles the fixed alternative's arithmetic/
height budgets into that measure and then into the root-exclusion conclusion.
Adding roothood as an unused premise alone would not supply that assembly.
The independent review and root agent therefore retain the whole alt as
Partial, despite completion of the uniform denominator component.

The unchanged conditional factor-degree component is supplied by
`Section4FactorDegreeBounds.manuscript_divisor_log_degree_lower` and
`manuscript_divisor_log_degree_upper`, instantiated with `a=rho*K` and
`b=tau*K`. These concern actual integer divisors, derive center nonvanishing
from the exact norm disk, retain the integer leading coefficient, and require
the independent upper cluster radius only in the upper-degree clause.

**Numerical boundary:** the completed component uses the valid symbolic rate `tau/mu`.
It does not retain the invalid printed numerical consequence `exp(K/2251)`
at `tau=11.411, mu=25687`. The exact rate is strictly below `1/2251`; the invalid
numerical consequence cannot be retained in any eventual assembled correction.

## Do not promote from the present source correspondence

### 4.5.alt — actual coupled-family measure

The generic effective transfer applies to any real center, including
`b*zeta(5)+a*zeta(3)`, once an integer-polynomial family and its degree/value/root
bounds are supplied. However, the fixed alternative explicitly ties those
inputs to the paper's actual coupled density identity, coefficient cone and
its own multiplier/valuation losses. There is no exact assembled declaration
or formal hypothesis package representing that complete actual coupled-family
correspondence. `PaperChain.Stage07` proves finite shift algebra and defines
a weight-sandwich predicate, not that package. The independent single-weight
`linearFamily` construction is not the coupled family. Do not promote this
row solely from the universal transfer theorem or from single-weight inputs.

### 4.7.alt — collapse / separation with symbolic constants

The actual spectral fraction and root-closeness conversion are proved by
`Section4ManuscriptBridge.manuscript_spectral_cluster_fraction` and
`manuscript_large_exponent_gives_close_root`. New sources additionally prove
actual straddling-root separation, integer divisor heights, and real
closest-root existence from center decay.

These are substantial complete components, but the fixed alternative still
says "collapse/separation", without deleting the original same-irreducible-
factor separation clause. That clause still lacks the needed root separation
inequality. The root-mean / inverse-matrix-trace identity is likewise not an
assembled source endpoint. The new height estimate is not a substitute for
either missing conclusion. Do not assign a whole-alternative A-Tier by
silently restricting its conclusion to the already proved fraction count.

## Certification condition

Only 4.1.alt is recommended as a complete fixed-alternative candidate in this
review. It depends on the existing transfer/effective-budget declarations.
The final receiving head must compile and pass the full transitive audit
before any current-head A-Tier update. This note alone supplies no compiler
certificate. 4.4.alt, 4.5.alt, 4.7.alt and 4.8.alt remain Partial at the current
exact-assembly evidence boundary.
