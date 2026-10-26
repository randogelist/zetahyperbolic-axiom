# Reconciliation: manuscript 3.4/3.8 helpers after merged Beukers 5.1 moment series

**Stage**: _construction (not merged; combined recipient Lean gate outstanding).  
**Receiving parent main**: `db4db45e35c5f98e9bd38402222d700847b17e2f` (PR #23 already merged, 225 active modules).  
**Frozen source donor**: [PR #26](https://github.com/randogelist/zetahyperbolic-axiom/pull/26), exact head `79093f5badec777a29eb0f51fe223d97214a1225`.  
**New registration plan**: 228 unique active modules; 227 project-owned audit roots.

## New proof-bearing modules

- `src/LeanPaper/SignatureRestriction.lean` Git blob `d1f107761de75eead018d29b69a4f86a476c2efc`, mathematical prerequisite to corrected Theorem 3.4.
- `src/LeanPaper/Section3MonicOrthogonal.lean` Git blob `7638ff43138e47a73e76c64652e887cc87955954`, actual Gram monic LDL basis for partial Theorem 3.8.
- `src/LeanPaper/MatrixCurveJacobi.lean` Git blob `5dacaee0aae1ef9e17840a0de80e081eff48fbe8`, generic Jacobi matrix-curve derivative for partial Theorem 3.8.

All three source blobs and their corresponding frozen scope receipts are **verbatim copies**, without proof or theorem changes. All preexisting 225 mathematical source files, Beukers moment series, pinned Mathlib/Lean, and Windows runner remain unchanged.

## Strong registry reconciliation

The exact three target registrations are the **only** differences in all three infrastructure files. Removing them from the new `modules.txt`, `lakefile.toml` and `LeanPaper.KernelAudit.lean` reproduces the current 225-module main files **byte for byte**. The 228-module registry/source layout is also byte-identical to the corresponding original [PR #26](https://github.com/randogelist/zetahyperbolic-axiom/pull/26) combined source (apart from manuscript documentation lineage).

## Merge gate

- Main PR #23 historical exact source [CI 40272835793](https://github.com/randogelist/zetahyperbolic-axiom/actions/runs/40272835793) has passed, adding the actual Beukers series.
- Old PR #26 combined-source CI [40273812000](https://github.com/randogelist/zetahyperbolic-axiom/actions/runs/40273812000) may serve as a source-fingerprint reference **only if successful**; it does **not** replace the mandatory new exact-head recipient CI on this reconciled branch.
- Require complete Lean 4.33.0 / pinned Mathlib compilation of all 228 modules, all-project independent transitive axiom audit with only `Quot.sound`, `Classical.choice`, `propext`, review of diff, and re-check final main SHA before merge. No sorry, custom mathematics axioms or admitted premises.
- This merge cannot upgrade full literal Theorems 3.4 or 3.8, and cannot change the existing 7/45 complete-manuscript result count.

**Proof execution lock**: LOCAL_COMPILER remains unchanged; GitHub CI is a separate integration gate and not native Windows PASS.
