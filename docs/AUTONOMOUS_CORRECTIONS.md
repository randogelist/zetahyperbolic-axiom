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

The full per-item review, precise remaining obstacles, and final verification receipts will be added after the independent repairs are checked.
