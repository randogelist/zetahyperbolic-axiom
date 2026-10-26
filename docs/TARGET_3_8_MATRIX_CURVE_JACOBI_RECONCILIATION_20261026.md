# Target 3.8 — current-main reconciliation checkpoint

- Mode: source integration only; GITHUB_CI proof claim not promoted; LOCAL_COMPILER target lock unchanged.
- Main source parent: `32727778c7e01373ee8f07d7d47ded0873b1b66c`.
- Original frozen PR: #14, head `38c9a38a6ec5fd05a37da960f5a03c44d3d3f80b`.
- Imported module: `src/LeanPaper/MatrixCurveJacobi.lean`, byte-identical Git blob `5dacaee0aae1ef9e17840a0de80e081eff48fbe8`.
- Frozen target receipt: `docs/TARGET_3_8_MATRIX_CURVE_JACOBI_FREEZE.md`, identical blob `2367b69df417650fd201979ead3beb33f00a115a`.
- Previous independent 222-module full Linux CI/audit at original branch source: [run 40266602343](https://github.com/randogelist/zetahyperbolic-axiom/actions/runs/40266602343), `MODULE_PLAN_ACCEPTED=222`, `AXIOM_AUDIT_ACCEPTED=ALL_PROJECT_DECLARATIONS`, foundational axioms only.
- Current-main proposed inventory: 224 modules, 223 owned by the audit; one mathematical source newly added relative to 223-module main.
- All existing Lean sources, source dependencies, Lean/Mathlib pins, runner and all pre-existing proof receipts are untouched. Modified only `modules.txt`, `lakefile.toml` and `src/LeanPaper/KernelAudit.lean` to register the new module.
- This clean integration **is not independently audited** until its **combined 224-module exact-head CI** passes with full axiom traversal. No native Windows PASS is implied.
- The generic finite Jacobi identity does not prove the actual Laplace differentiation or Christoffel-Darboux identification required by printed Theorem 3.8.
