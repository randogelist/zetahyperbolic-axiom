# Manuscript 3.4/3.8/5.1 combined source-intake checkpoint

Current receiving main base: `7d09dce140f83fddd13a8d9c3a0050072076a0f9` (224 previously accepted modules, including Hermite #6).
Frozen mathematical sources selected from exact standalone GitHub Actions successful heads:
- `LeanPaper.SignatureRestriction` / Git blob `d1f107761de75eead018d29b69a4f86a476c2efc` / [run 40270783080](https://github.com/randogelist/zetahyperbolic-axiom/actions/runs/40270783080) / head `cc8cff2cfeb3b3e1293d0eedfbf5131af4bb6440` / scope receipt `efa9ad79f387cd52e1b80b7326b4f7a6da26a0f1`.
- `LeanPaper.Section3MonicOrthogonal` / Git blob `7638ff43138e47a73e76c64652e887cc87955954` / [run 40271486561](https://github.com/randogelist/zetahyperbolic-axiom/actions/runs/40271486561) / head `95c81e55704716773c34e867df68e1a86f69b6f4` / scope receipt `bc1f1efc86ec002301f30be633c95caa8c692dd2`.
- `LeanPaper.MatrixCurveJacobi` / Git blob `5dacaee0aae1ef9e17840a0de80e081eff48fbe8` / [run 40266602343](https://github.com/randogelist/zetahyperbolic-axiom/actions/runs/40266602343) / head `38c9a38a6ec5fd05a37da960f5a03c44d3d3f80b` / scope receipt `2367b69df417650fd201979ead3beb33f00a115a`.
- `LeanPaper.BeukersMomentSeries` / Git blob `5eff67223443f63e2447a6409ed33cf13458b038` / [run 40264406071](https://github.com/randogelist/zetahyperbolic-axiom/actions/runs/40264406071) / head `b55e7c1a93348e318b23af40355607f00150408f` / scope receipt `9af3743d56899440964c033fef69bf2ab83e2613`.

The four Lean files and the four original scope receipts are byte-identical to their donors.
Changed registrations only: `modules.txt`, `lakefile.toml`, `src/LeanPaper/KernelAudit.lean`; additions are one-per-module, order after prior 224 modules.
New combined build plan = 228 modules, 227 project-owned audit roots. Old mathematical Lean sources, compiler/Mathlib pins, Windows runner, prior proof receipts unchanged.
None of these four proves any currently open complete printed manuscript item: 3.4 correction prerequisite is not false literal 3.4; 3.8 Gram basis and Jacobi matrix identity do not prove actual Christoffel–Darboux and Laplace differentiation; 5.1 series does not prove all off-diagonal rational moments.
This composite branch is not an A-Tier certified endpoint unless its own exact-head **complete** Lean 4.33.0 build and independent axiom audit pass (allowed foundations only). Separate donor audits are not a combined-source PASS. Do not confuse the test-only preflight PR #18 with this candidate.
Proof execution target remains LOCAL_COMPILER; GitHub Actions is only an additional merge-integrity test; no native Windows PASS inferred.
