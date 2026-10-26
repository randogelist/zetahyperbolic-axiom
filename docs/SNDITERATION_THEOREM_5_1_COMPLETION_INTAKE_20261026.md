# Staged completion: snditeration → Zetahyperbolic Theorem 5.1

Status: `_construction`, **not yet merged or source-audited on receiving main**.

This branch is based on receiving PR #23 at `1356856b2f38e4e13f79a6f43345a2c0c70cf7c6`, whose source provides `LeanPaper.BeukersMomentSeries` for the actual Beukers measure and its diagonal moments. The donor supplies the remaining exact two-variable theorem components; do not duplicate or overwrite the existing source module.

- Receiving repo: `randogelist/zetahyperbolic-axiom`, target `main`.
- Donor: `randogelist/snditeration@8c6bd26acb12ec7f606bcb8f414302774894d141`.
- Lean: 4.33.0; Mathlib: `db584cd6d46c92f209a44c0f1c829460d327499d`.

## Incoming source provenance
- `src/LeanPaper/BeukersOffDiagonalActual.lean` ← `Zetahyperbolic/Section5/BeukersOffDiagonal.lean` (donor Git blob `1701d3fba9a425d86f59ba7ac89c3f926229d214`). Exactly the import line changes; declarations, statements, all theorem proof lines unchanged.
- `src/LeanPaper/BeukersDensityActual.lean` ← `Zetahyperbolic/Section5/BeukersDensity.lean` (donor Git blob `bc3d755c3068b1cd6d9066076321c45167bf862a`). Exactly the import line changes; declarations, statements, all theorem proof lines unchanged.
- `src/LeanPaper/BeukersRationalityActual.lean` ← `Zetahyperbolic/Section5/BeukersRationalMoments.lean` (donor Git blob `115bbae9a01745fe2593b852920e202ecd0d5e4c`). Exactly the import line changes; declarations, statements, all theorem proof lines unchanged.

Verified donor source: [Theorem 5.1+offdiagonal rationality run 40268502325](https://github.com/randogelist/snditeration/actions/runs/40268502325), [donor main run 40272229860](https://github.com/randogelist/snditeration/actions/runs/40272229860), both successful Lean/axiom checks.

### Exact contribution
- Printed actual Beukers diagonal + off-diagonal integral equality (Theorem 5.1), with ζ(7) diagonal and harmonic-six divided-difference off-diagonal.
- Strict positivity and measurability of printed density.
- Explicit rational witness for every off-diagonal value.
- No claim of arbitrary-L² Krein theorem 5.2, indefinite cones or ζ(7) irrationality.

### Admission boundary
- 228 candidate modules including `LeanPaper.KernelAudit`, three new Lean source modules plus module-list/Lake/audit registrations. All earlier math files remain unchanged.
- After parent PR #23 integration and reconciliation to final main HEAD, require a fresh full Lean 4.33.0/Mathlib compile and independent `AXIOM_AUDIT_ACCEPTED=ALL_PROJECT_DECLARATIONS` with no `sorryAx` and only `propext`, `Classical.choice`, `Quot.sound`.
- Donor CI is not receiving CI. Source-staging cannot upgrade the manuscript-wide 7/45 count by itself. The existing LOCAL_COMPILER proof execution target remains unchanged.
