# Autonomous formalization corrections

Scope: the 45 manuscript results in `randogelist/zetahyperbolic-axiom`, starting at `41674aac3544bf314a53b4302266ad22a30ae707`. Mode: `A_TIER_LEAN`; verification target: `GITHUB_CI`. No local Lean compilation is authorized or used. Historical Linux and Windows evidence remains separate.

Every entry records an actual source correction or proof construction. Compilation, transitive axiom audit, and whole-manuscript equivalence are separate checks. No new proof tier is claimed before the matching CI result.

## Initial corrections and proof constructions

| Target | Original problem and cause | Correction or construction | Verification |
| --- | --- | --- | --- |
| Finite 5.2: rational coefficient independence | CI 40281177876 failed in `Section5RationalIndependence`: invalid documentation/`set_option` placement and real/complex ordered-star Gram APIs applied over the rationals. Raising heartbeats would not supply the missing instance. | Preserve all four declarations and hypotheses. Prove rational Gram positivity directly as a sum of squares, use injectivity for a nonzero summand, and derive determinant nonvanishing through `PosDef.isUnit`. | Source repaired; receiving CI pending. Infinite Krein assertions remain separate. |
| 3.8(1): actual orthogonal kernel | Constructed monic polynomials and positive proposed norms lacked the actual integral orthogonality and inverse-Gram identification. | `Section3OrthogonalKernel` derives the LDL inverse-Gram identity, orthogonality and actual integral norms, and connects the pole kernel to the constructed symmetric spectrum. | Source candidate; CI pending. Laplace differentiation in 3.8(2) remains separate. |
| 4.8: factor-degree bounds | Earlier components did not assemble the logarithmic degree estimates for genuine polynomial factors. An upper cluster bound cannot be inferred from lower separation. | `Section4FactorDegreeBounds` constructs root-product estimates, proves both logarithmic bounds, and transfers them to genuine divisors using the actual norm disk. Required numerical norm and upper-cluster premises remain explicit. | Source candidate; CI pending. No unconditional family estimate is asserted. |
| 5.1: actual measure and polynomial pencil | Integrated moment formulas had not been assembled into a weighted measure with integrable monomials and the actual polynomial/dual-entry identity. | `BeukersIntegralPencil` constructs the measure, proves integrability, assembles both moment cases, and identifies finite polynomial bilinear integrals with the existing rational affine pencil. | Source candidate; CI and exact-clause review pending. |
| Full-project verification | The previous workflow stopped at the first failed module and repeatedly invoked Lake, replaying dependency logs while hiding independent failures. | Fresh isolated project objects, a dependency-aware CI compiler scheduler, source/import/object fingerprints, and preserved global transitive axiom audit. Deliberate bad-axiom fixtures run separately and must pass their rejection regression checks. | Python-only scheduler checks passed; actual GitHub CI pending. |

## Evidence rules

The CI artifact contains per-module logs, a machine-readable summary, the exact commit, compiler/Mathlib fingerprints, and the all-project axiom audit. A successfully compiled helper does not complete a larger paper theorem. False printed statements retain their original status and separate corrected endpoints. Unfinished analytic or arithmetic hypotheses are never silently added to an original theorem.

## Receiving CI and follow-up repairs

First receiving run: [40316513854](https://github.com/randogelist/zetahyperbolic-axiom/actions/runs/40316513854), commit `d2a86b7095128cd898f337fb39a1a46f40f94806`: **237/241 compiled**, three modules failed and the global audit was correctly skipped. The isolated negative-audit regressions passed. This is not an A-Tier or full-project PASS.

The subsequent source corrections preserve statements: ordered matrix rewrites and the correct determinant-cast direction in rational independence; explicit simplification of self-pairings, rational casts and matrix characteristic-polynomial typing in the orthogonal kernel; explicit density measurability and finite double-sum ordering in the Beukers integral assembly.

Additional constructed candidates, all awaiting their receiving verification:

| Target | Implemented proof content | Scope retained |
| --- | --- | --- |
| Approved 3.3.alt | `Section3RestrictedSpectral`: actual Gram/principal minors, residue-product leading sign, and intrinsic signature assembled. | Exactly the previously listed alternative; mixed-minor positivity and determinacy in the original remain separate. |
| 3.8(2) | `LaplaceDensityDerivative` and `LaplaceMomentBounds`: differentiate the actual exponential series with a summable local majorant; prove integrability of scaled density and derivative moments. | Rational-weight integral differentiation and complete Jacobi assembly remain separate. |
| 4.7 / 4.8 | Actual straddling-root gap, finite polynomial factor degree bounds, and all-denominator cluster exclusion, including small denominators. | Numerical norm/height estimates and a genuine upper-cluster premise remain explicit. |
| 4.6 / 4.8 proof diagnostics | Exact rational counterexample to using an upper arithmetic rate as a lower rate; exact `1/2252 < (11411/1000)/25687 < 1/2251`. | These diagnose proof steps, not counterexamples to every conclusion of the full conditional theorems. |
| Finite 5.2(1) | `BeukersPolynomialSpectrum`: actual polynomial evaluations and measure integrals identified with the affine pencil, then positive derivative, exact degree and real roots. | Infinite Krein subspaces and tail control remain separate. |
| 5.3 | `BetaBeukersMoments` and `BetaBeukersSpectrum`: actual beta density and measure, integrable fourth-power moments, exact rational off-diagonal entries, and the actual polynomial spectral pencil. | Exact whole-statement review and receiving audit required. |
| 5.7 proof/definition obstruction | `DoublePoleZeroCoefficientObstruction`: at `n=1`, the defined numerator cancels the pole at zero, contradicting the printed nonzero double-pole coefficient. | This refutes the partial-fraction bridge, not by itself the full conditional valuation conclusion. |
| 6.2 | `BeukersSimultaneous`: actual adjacent/extra-denominator integrals, justified series exchange, polynomial simultaneous zeta-6/zeta-7 formula, and exact `6*d_K^7` clearing. | Actual measure and printed rational-part identification included; receiving audit pending. |
| 6.4 | `BetaOddResidueSigns`: all three factors in the printed odd-square residue formula, including the numerator sign, give positivity. | Corrects the historical two-factor-only sign diagnosis; actual beta analytic realization remains separate. |
| Corrected 6.13 | `CentralFactorialMoments`: all moments of the actual accelerated secant density, an explicit factorial bound and all finite Hankel positive definiteness. | Does not identify the beta functional or close the full corrected theorem. |

The original manuscript is unchanged. The full per-item review and final verification receipts will be recorded after these candidates are checked.

## Complete per-item investigation trail

Every one of the 45 original results is tracked in [formalization_repair_status.json](formalization_repair_status.json). Status describes the whole original, not the number of compiled helper lemmas. Existing proofs are retained; unproved clauses are recorded with the attempted route and the specific missing construction.

Detailed reviews: [Chapters 2–3](repair_reviews/spectral.md), [Chapter 4](repair_reviews/section4.md), [Chapter 5](repair_reviews/beukers.md), [5.2 compilation repair](repair_reviews/section5_build.md), [Chapter 6](repair_reviews/section6.md), and [CI/audit implementation](repair_reviews/ci.md). Independent statement comparisons cover [3.8](repair_reviews/semantic_38.md), [4.2](repair_reviews/semantic_42.md), and [5.3](repair_reviews/semantic_53.md).

The next verification batch also includes actual Laplace rational-weight differentiation, deformed Gram positivity and integral kernel/Jacobi assembly for 3.8; actual closest-root existence from center decay for 4.7; all eleven actual floor-function integrals and endpoint noncontinuity in 5.6; and an exact differential-coupling correction for the displayed weight on manuscript page 34 in 6.4. The page 33 signed density is a different formula and is not refuted merely by the page 34 identity. These changes retain their exact source-level hypotheses and are candidates until CI accepts them.

Failed CI remains failed even when independent modules compile. Reusable outputs from an incomplete run require a separate transitive audit of precisely the completed dependency-closed subset and passing negative-audit regressions. Such a receipt is explicitly scoped `COMPLETED_PROJECT_SUBSET`; it never certifies the whole repository. A full pass still requires a fresh `ALL_PROJECT_DECLARATIONS` audit and fresh negative regressions.

## Second receiving CI

[Run 40318924083](https://github.com/randogelist/zetahyperbolic-axiom/actions/runs/40318924083), commit `96ffaabc6051e7ebbf66b3f86aeea91cb7602111`, compiled **241/253** modules. Eight new/repaired modules failed and four dependency closures were skipped. The negative-audit regressions passed. The orthogonal kernel, restricted 3.3 endpoint, actual Beukers measure, factor-degree bounds and divisor-height proofs compiled, but no whole-project or A-Tier promotion follows from this failed run.

Follow-up repairs address exact compiler diagnostics: normalize the bundled rational matrix-cast homomorphism before determinant transport; separate absolute-value bars from multiplication in the parser; simplify limit-function composition explicitly; resolve the actual series-derivative expression; normalize finite-sum casts and product factors; avoid a reserved identifier in the odd-square prefix polynomial; and simplify finite pole-cofactor evaluations structurally. Original theorem statements remain unchanged.

## Third receiving CI

[Run 40320889232](https://github.com/randogelist/zetahyperbolic-axiom/actions/runs/40320889232), commit `bdcbb8bbd54d9837e3230cd50c28358eec37ee42`, compiled **246/259** modules. Seven failed and six dependent modules were skipped. The separately isolated audit of exactly those 246 completed modules passed with the three allowed foundational axioms, and the negative-audit regressions passed. This is a `COMPLETED_PROJECT_SUBSET` receipt, not a full-project PASS.

The actual beta moments, complete simultaneous 6.2 construction, corrected secant moment measure, actual density differentiation and rational cluster bounds are now included in that audited subset. Follow-up repairs explicitly expose rational casts and half-line positivity to Lean, transport actual roots through polynomial evaluation, simplify finite polynomial products and normalise the derivative expressions. No conclusion or hypothesis is weakened.

Independent reviews also map the existing 4.1.alt split exactly: existential real-exponent/lattice transfer, and a computable threshold with supplied rational margins/onset and a natural exponent. The fixed 4.4.alt, 4.5.alt, 4.7.alt and 4.8.alt remain partial; generic implications do not close their actual-family assembly requirements. See [independent comparison](repair_reviews/semantic_41_48_alternatives.md) and [Chapter 4 alternative mapping](repair_reviews/semantic_section4_alternatives.md).

## Additional finite 6.10 bound during CI

`CoefficientGramGrowth` now constructs the exact finite Hadamard inequality from LDL decomposition: each diagonal entry bounds its corresponding nonnegative LDL diagonal contribution, and their product bounds the determinant. It then proves the actual integer coefficient-Gram upper bound `(K+1)^h * B^(2h)` from a real entry-height budget `B`, and the printed polynomial-height specialization together with the retained integer lower bound 1. Existing factorial/asymptotic declarations are preserved. The new bound awaits receiving CI; potential-energy limits and the strict one-variable/two-variable gap remain separate.

## Fourth receiving CI

[Run 40323993835](https://github.com/randogelist/zetahyperbolic-axiom/actions/runs/40323993835), commit `e83810004eb5e2392beb208e5d85bc3843ae5214`, compiled **251/259** modules, reusing 245 only after the preceding independent subset audit and exact source/import/object/log checks. Four modules failed and four dependents were skipped. The fresh completed-subset audit and negative regressions passed; full-project state remains FAIL.

The rational-independence repair, all Chapter 4 additions, full actual beta residue positivity, corrected differential weight and double-pole obstruction now compile. Remaining repairs: preserve the dependent LDL witness when applying matrix-entry/determinant equalities; make coefficient-family evaluation and matrix representation explicit; use the pinned summation/pointwise analytic APIs; and replace exponential max/min case branching in the floor integral with directed affine inequalities. Compilation failures are retained as failed evidence rather than hidden by the cache.

## Actual outer-prime arithmetic for 6.1(2)

`BeukersOuterValuation` proves the actual positive harmonic interval has exactly one term with valuation `-s`, derives the literal weight-seven off-diagonal rational value's valuation `-7`, reduces the full outer-prime congruence hypotheses to the shifted-index case, and identifies that rational value with the actual Beukers integral. This removes an actual arithmetic obstruction instead of assuming a generic local-valuation interface. The source is queued for receiving CI. The independent Mellin change of variables and full local two-by-two leading-congruence clause remain unproved.
