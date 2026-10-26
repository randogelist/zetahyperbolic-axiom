# Beukers Theorem 5.1 integration following PR #26 — construction

Receiving repository: randogelist/zetahyperbolic-axiom
Base PR: #26 (head 79093f5badec777a29eb0f51fe223d97214a1225)
Base active Lean modules: 228; resulting combined plan: 231.
Proof target remains LOCAL_COMPILER. GitHub CI is an independent integration gate, not a native Windows proof receipt.

Three source modules copied verbatim from PR #28 head 762f8cf640b652099cf2c05eb5c7c765b198083b, whose donor mathematics originated at randogelist/snditeration@8c6bd26acb12ec7f606bcb8f414302774894d141.
- src/LeanPaper/BeukersOffDiagonalActual.lean — blob f7f6cd208ce587d01e58a829b96e040edf1ca2c2
- src/LeanPaper/BeukersDensityActual.lean — blob 9e1bb8066fd01b00ad251a5fbc89be31d2235d2b
- src/LeanPaper/BeukersRationalityActual.lean — blob 7ed9310ff921c9fc5e0827c8791c68157390c819

Original donor Lean 4.33.0/Mathlib source and axiom run: https://github.com/randogelist/snditeration/actions/runs/40268502325 (successful).
PR #28 receiving integration is separately awaiting its own Lean CI; no donor pass transfers automatically to this new source configuration.

New contribution: exact off-diagonal unit-square Beukers moments of Theorem 5.1, density positivity and measurability, explicit rational number for off-diagonal moment. These depend on the previously copied actual diagonal Beukers moment series in PR #26. The three new source contents are identical to the staged PR #28 receiving contents; only the three registration files and this document are edited or added in the new commit.

Acceptance requires: PR #26 exact-head combined 228-module Lean compilation + all-project independent axiom audit pass and merge, then reconciliation to updated main, then 231-module exact-head Lean 4.33.0 pinned Mathlib full compile and AXIOM_AUDIT_ACCEPTED=ALL_PROJECT_DECLARATIONS with only propext, Quot.sound and Classical.choice. Do not upgrade 5.1's 45-item full theorem count without checking complete printed correspondence and new receiving integration PASS. Do not confuse this with 5.2 Krein cones or irrationality of zeta(7).
