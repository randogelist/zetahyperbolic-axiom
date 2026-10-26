# ZETAHYPERBOLIC manuscript Theorem 5.1 actual-moment integration

**Build stage:** _construction; proposed 231-module complete-manuscript-5.1 candidate, no recipient A-tier claim.  
**Branch:** `merge/gwf-theorem-51-complete-after-batch-v0_1_0_construction`  
**Base:** [PR #26](https://github.com/randogelist/zetahyperbolic-axiom/pull/26) head `79093f5badec777a29eb0f51fe223d97214a1225`, 228 modules.

## Source provenance

Three exact *receiving-repo translated* proof sources from [PR #28](https://github.com/randogelist/zetahyperbolic-axiom/pull/28), all unchanged here:

- `src/LeanPaper/BeukersOffDiagonalActual.lean`: blob `f7f6cd208ce587d01e58a829b96e040edf1ca2c2`. Donor source `snditeration@8c6bd26`, blob `1701d3fba9a425d86f59ba7ac89c3f926229d214`.
- `src/LeanPaper/BeukersDensityActual.lean`: blob `9e1bb8066fd01b00ad251a5fbc89be31d2235d2b`. Donor blob `bc3d755c3068b1cd6d9066076321c45167bf862a`.
- `src/LeanPaper/BeukersRationalityActual.lean`: blob `7ed9310ff921c9fc5e0827c8791c68157390c819`. Donor blob `115bbae9a01745fe2593b852920e202ecd0d5e4c`.

Original [donor full Lean+axiom audit 40268502325](https://github.com/randogelist/snditeration/actions/runs/40268502325) reportedly succeeded, but cannot substitute for receiving repository verification. The three prior files change only their import lines compared to donor (as recorded in PR #28); this integration changes **no** theorem statement or proof body beyond those established imports.

## Mathematical scope

- The printed positive two-variable weight-seven density and both diagonal and off-diagonal moment identities.
- Exact off-diagonal harmonic-six quotient, and a rational witness.
- No assertion of ζ(7) irrationality, complete Section 5.2 Krein-space theorem, or downstream irrationality measure.

## Integration gates and locks

1. Accept PR #26 full 228-module exact SHA Lean 4.33.0 + independent complete project axiom audit, and merge to main (preserve all its exact proof blobs and frozen source dependencies).
2. Reconcile this three-source addition onto then-current `main` if required; require fresh exact-head **231-module** Lean 4.33.0 build plus `AXIOM_AUDIT_ACCEPTED=ALL_PROJECT_DECLARATIONS` (only `propext`, `Classical.choice`, `Quot.sound`).
3. Only after checking the declaration matches literal manuscript 5.1 may mark one additional printed manuscript theorem proved. Standalone donor or generic helper proof alone does not justify promotion.

**Proof execution lock:** LOCAL_COMPILER unchanged; GitHub CI is integration verification, not native Windows PASS.
