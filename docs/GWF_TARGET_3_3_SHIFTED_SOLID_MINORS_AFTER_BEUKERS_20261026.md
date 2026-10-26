# 3.3 real-moment shifted solid minors — accepting current main, proof source frozen

Original source: PR #25 `src/LeanPaper/ShiftedSolidMinors.lean`, Git blob `e6c8c22df1f4fb085b356d61f8820b684a365b99`, unchanged.
Receiving base: `db4db45e35c5f98e9bd38402222d700847b17e2f`, after original unit-square Beukers moment PR #23.
Single new Lean module plus full unchanged frozen mathematical sources, exact modules.txt/lakefile.toml/KernelAudit registrations and documentation receipts.
Frozen original scope receipt: `docs/TARGET_3_3_SOLID_MIXED_MINORS_FREEZE.md`.

Full prior CI PASS and independent transitive axiom gate: https://github.com/randogelist/zetahyperbolic-axiom/actions/runs/40273397775 at `00700d6b4709dbfbcf5397672fdac123d3f7893f`, a *different* 225-module source assembly. This is NOT receiving-base certification.

Actual result: shifted sparse Gram/moment positive definiteness, positive determinants of all solid mixed Hankel minors and same-pattern translated positive minors for admissible actual odd-zeta parameters.
Not proved: arbitrary unrelated-gap minors, Stieltjes determinacy or complete Theorem 3.3.
Repaired donor mathematical source unchanged; no custom axioms, sorry, or hidden premise introduced by this merge candidate.
New intended 226-module source assembly must compile under Lean 4.33.0 and pinned Mathlib `db584cd6d46c92f209a44c0f1c829460d327499d` and pass independent complete `AXIOM_AUDIT_ACCEPTED=ALL_PROJECT_DECLARATIONS` on the exact SHA before main merge.
If `main` changes (e.g., PR #35), reconcile again and require a new exact-source build and audit. Do not merge alongside PR #35 without removing duplicate registry edits.
Proof execution target `LOCAL_COMPILER` unchanged; GitHub CI is an independent source-integration check.
