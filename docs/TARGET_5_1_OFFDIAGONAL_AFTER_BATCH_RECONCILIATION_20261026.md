# ZETAHYPERBOLIC — Beukers off-diagonal finite-kernel intake

**Status:** _construction, dependent integration only; NO merged-main proof claim.  
**Scope:** manuscript Theorem 5.1 finite six-term off-diagonal divided-difference kernel, not the full integral or rational moment identity.  
**Stacked base:** [PR #26](https://github.com/randogelist/zetahyperbolic-axiom/pull/26) head `79093f5badec777a29eb0f51fe223d97214a1225` (228 modules).  
**Result:** 229-module combined candidate; new source `LeanPaper.BeukersOffDiagonalKernel`.

## Source chain

- Frozen theorem source imported verbatim from [PR #22](https://github.com/randogelist/zetahyperbolic-axiom/pull/22): Git blob `75067da07668d2306efd4350715789c97a4c22f4`.
- Frozen scope receipt imported verbatim: Git blob `b3f7a77009e2d4f34b6f0b6de2659398ca8901fa`.
- Donor original [PR #17 CI 40270209335](https://github.com/randogelist/zetahyperbolic-axiom/actions/runs/40270209335) FAILED due to redundant final `ring` tactic. The above donor branch removes that redundant tactic without theorem changes.
- PR #22 exact combined-source Linux CI is **not yet established PASS** at this staging checkpoint.
- Four predecessor source files and their existing proofs in PR #26 remain byte-identical and their three build/audit registries gain only one entry each.
- Pinned Lean 4.33.0 / Mathlib, native Windows `run.cmd` and all existing mathematical source files unchanged.

## Mandatory gates

Do **not merge** until PR #26 passes its exact 228-module full build+independent axiom gate and merges into main with source content unchanged; then rebase/reconcile this one-source addition against updated main, require a fresh **229-module** full build and `AXIOM_AUDIT_ACCEPTED=ALL_PROJECT_DECLARATIONS` with only foundational `propext`, `Quot.sound`, `Classical.choice`. Maintain the LOCAL_COMPILER proof-target lock; GitHub CI is an integration gate only.

No full printed result, ζ(7) irrationality, or extra 45-item manuscript completion is claimed.
