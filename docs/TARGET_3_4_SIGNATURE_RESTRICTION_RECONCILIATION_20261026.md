# Manuscript 3.4 signature-restriction intake — current-main reconciliation

**Branch:** `merge/gwf-target-34-signature-restriction-after-hermite-v0_1_0`  
**Baseline main commit:** `7d09dce140f83fddd13a8d9c3a0050072076a0f9`, 224 modules  
**Proposed modules:** 225, with exactly one new Lean source  
**Target:** prerequisite for corrected manuscript Theorem 3.4, not the false literal full principal-minor claim  
**Proof target lock:** LOCAL_COMPILER unchanged; GitHub integration CI is an independent gate

## Frozen source and evidence

- Immutable donor: [PR #10](https://github.com/randogelist/zetahyperbolic-axiom/pull/10), source at `feat/gwf-target-34-signature-restriction-v0_1_0`.
- `src/LeanPaper/SignatureRestriction.lean` Git blob `d1f107761de75eead018d29b69a4f86a476c2efc`, reused **without any byte changes**.
- Preserved frozen scope receipt blob `efa9ad79f387cd52e1b80b7326b4f7a6da26a0f1`.
- Donor head `cc8cff2cfeb3b3e1293d0eedfbf5131af4bb6440` passed initial [224-module Lean 4.33.0 CI #40270783080](https://github.com/randogelist/zetahyperbolic-axiom/actions/runs/40270783080), with `AXIOM_AUDIT_ACCEPTED=ALL_PROJECT_DECLARATIONS`, only `Quot.sound`, `Classical.choice`, `propext`.
- This new intake changes only new theorem source, unchanged donor receipt, this reconciliation receipt, and one registration each in `modules.txt`, `lakefile.toml`, and import/owner slots of `LeanPaper.KernelAudit`.
- All 224 prior project-owned Lean source files, Lean toolchain/Mathlib pins, and native Windows run.cmd are unchanged.

## Mandatory receiving-main gate

**DRAFT / DO NOT MERGE** until this exact *combined* SHA passes the full sequential 225-module Lean 4.33.0 build and independent transitive all-project axiom audit. If main moves, reconcile and repeat the new combined-head check. Standalone donor PASS alone is not receiving-main PASS. This is a finite signature-restriction helper only; the manuscript's complete result count stays 7/45.
