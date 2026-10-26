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
