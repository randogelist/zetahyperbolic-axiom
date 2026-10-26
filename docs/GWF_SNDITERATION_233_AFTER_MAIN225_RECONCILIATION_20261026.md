# YOU_ARE_GOODWORKFLOWFRONTIER: selective source merge onto 225-module main

Receiving repo: randogelist/zetahyperbolic-axiom
Pinned base: db4db45e35c5f98e9bd38402222d700847b17e2f
Source of exact validated frozen file blobs: consolidated 233-module PR #34 at 4c3f17500a53b3bd5cc43819758b9bab7a00220a (components independently proved in PRs #26/#30 and snditeration).

This branch ports exactly EIGHT new Lean mathematical modules, without modifying any previously accepted module or the shared Lean 4.33.0/Mathlib pin. Existing BeukersMomentSeries from accepted main PR #23 is not duplicated. New modules: LeanPaper.SignatureRestriction; LeanPaper.Section3MonicOrthogonal; LeanPaper.MatrixCurveJacobi; LeanPaper.BeukersOffDiagonalActual; LeanPaper.BeukersDensityActual; LeanPaper.BeukersRationalityActual; LeanPaper.BeukersKreinMonomialActual; LeanPaper.BeukersKreinPolynomialActual.

The three module/Lake/KernelAudit registries are the exact frozen PR #34 files. Their source-level comparison with main showed 225 preexisting module names retained in the same order plus exactly eight unique additions, with a complete corresponding KernelAudit owner/import list. Existing module source bytes are preserved by Git tree inheritance. Source freezes are included and refer to original donor commits and proofs.

Theorem scopes: 3.4 only corrected signature-restriction helper; 3.8 only finite monic/LDL and generic Jacobi helper; 5.1 actual unit-square Beukers integral diagonal, off-diagonal and rationality and density positivity; 5.2(2) only monomial and finite polynomial Krein signed identities, not all L² and cones. No unconditional zeta irrationality or entire manuscript assertion. Current 7/45 printed completions remain until receiving proof audit confirms exact 5.1 statement.

Required independent receiving gate before merge: exact HEAD successful Lean 4.33.0 all-233-module compile and AXIOM_AUDIT_ACCEPTED=ALL_PROJECT_DECLARATIONS, with only Quot.sound, Classical.choice, propext, no sorryAx or hidden axioms. Successful donor runs and main-225 receipt do not substitute. The user's LOCAL_COMPILER target is unchanged; GitHub CI here is for integration validation. No automatic certification, no merge before exact-run PASS. Status=_construction.
