# Main-based deduplicated source intake: actual Zetahyperbolic paper 3.3, 5.1 and finite 5.2

Workflow YOU_ARE_GOODWORKFLOWFRONTIER, status `_construction`.

Base: `dea277cc309e863f84fbf392ac13a08cd8c369f4` (accepted main PR #36, 228-module merged structure).
Frozen donor HEAD: `0e68cf7ba268b2a498c299659796ba2c66e32c5b` (PR #38, 234-module source assembled from independent audited donor proofs, including snditeration).
Exact new-source filenames, unchanged Git blobs:
- `src/LeanPaper/BeukersOffDiagonalActual.lean`: `f7f6cd208ce587d01e58a829b96e040edf1ca2c2`
- `src/LeanPaper/BeukersDensityActual.lean`: `9e1bb8066fd01b00ad251a5fbc89be31d2235d2b`
- `src/LeanPaper/BeukersRationalityActual.lean`: `7ed9310ff921c9fc5e0827c8791c68157390c819`
- `src/LeanPaper/BeukersKreinMonomialActual.lean`: `3a0cb3795036a114af28094ef9733a223051ecca`
- `src/LeanPaper/BeukersKreinPolynomialActual.lean`: `f64d1da65450652368ea704d153610fa53279971`
- `src/LeanPaper/ShiftedSolidMinors.lean`: `e6c8c22df1f4fb085b356d61f8820b684a365b99`

The existing 228 main-owned Lean modules remain byte-for-byte unchanged, in the same dependency order. New plan has 234 unique modules with a full owned-source KernelAudit inventory. The only changed existing files are the mechanically extended `modules.txt`, `lakefile.toml`, and `src/LeanPaper/KernelAudit.lean`. No Mathlib, Lean, runtime, or workflow pin changes. This is a fresh integration source tree, not proof certification.

Mathematical scope: 3.3 actual shifted solid Gram minor positivity, not arbitrary mixed minors/Carleman; 5.1 real Beukers off-diagonal integral identity, positivity and rationality for all natural indices; 5.2 actual finite monomial and rational coefficient signed Krein identities, not arbitrary L² nor all-dimensional cones. No zeta5 or zeta7 irrationality, no claim of completed 3.3 or 5.2.

Donor 3.3 independently passed [CI 40273397775](https://github.com/randogelist/zetahyperbolic-axiom/actions/runs/40273397775); full 5.1 independently passed [snditeration CI 40268502325](https://github.com/randogelist/snditeration/actions/runs/40268502325); finite 5.2 separately passed [snditeration CI 40271072845](https://github.com/randogelist/snditeration/actions/runs/40271072845). Donor PASS does not certify the combined 234-module source.

Merge gate: fresh exact HEAD Lean 4.33.0 / Mathlib db584cd6d46c92f209a44c0f1c829460d327499d full compile, independent transitive `AXIOM_AUDIT_ACCEPTED=ALL_PROJECT_DECLARATIONS` with only `propext`, `Classical.choice`, `Quot.sound`, no sorryAx, and SHA/content source review. GitHub is an integration validation, not a change of user's LOCAL_COMPILER target. No merge before actual PASS. Old overlapping drafts must not be blindly merged.
