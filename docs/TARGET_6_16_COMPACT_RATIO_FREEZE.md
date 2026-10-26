# Frozen target: 6.16 compact positive-ratio comparison

**Anchor:** `ZETA_HYPERBOLIC_TARGET_6_16_COMPACT_RATIO_1`  
**Package status:** `_construction` until receiving repository 220-module Lean CI and complete transitive axiom audit pass.  
**Donor:** uploaded `zeta5-spectral-lean (1).zip`, path `zeta5-spectral-lean/Zeta5Merge/Theorem6_16.lean`.  
**Transferred byte-identical:** `src/Zeta5Merge/Theorem6_16.lean`.  
**Source SHA-256:** `6507a2fe8cd759efac516d4f01576363c18ad18e8b65210a58e827b046b82517`.  
**Git blob SHA-1:** `1d435d2f251f7e9852cfd258c321fe5bf8367735`.  
**Historical donor evidence:** `verification/MERGE_BUILD.json` marks this exact SHA-256 `PASS`; `verification/repairs/Zeta5Merge.Theorem6_16.log` lists only `propext`, `Quot.sound` and `Classical.choice` for the four exported theorems.
**Receiving baseline:** `zetahyperbolic-axiom/main@86ca99a23d65cde4880a9005a49076c43e7bc968`; Lean `4.33.0`, Mathlib `db584cd6d46c92f209a44c0f1c829460d327499d`.

## Exact theorem scope

- `uniform_bounds_of_positive_continuous`: compactness gives a strictly positive lower and finite positive upper bound for a continuous **strictly positive** ratio on the **closed** interval `[0,1]`.
- `uniform_bounds_of_positive_interior_and_endpoints`: discharges positivity on the closed interval only when it holds in the open interval **and separately at both endpoints**.
- `weight_comparison_of_compact_ratio`: pulls that inequality back to two weights through an explicitly supplied compactification and **ratio identity**, assuming the comparison weight is nonnegative.
- `missing_zero_endpoint_counterexample`: a continuous ratio positive on `(0,1]` can still have no strictly positive global lower bound because its value at zero vanishes.

These are **mathematical finite/compactness helpers**, not an identification with the actual mixed Dirichlet–beta/odd-zeta paper weights. They neither prove Theorem 6.16 in full nor discharge the open analytic ratio identity, endpoint behavior, mixed moments, determinant multipliers or p-adic clauses.

## Only-this-target branch changes

1. Add exactly one previously absent `Zeta5Merge.Theorem6_16` source file, verbatim.
2. Register that module once in `modules.txt`, `lakefile.toml`, and the complete `LeanPaper.KernelAudit` import and project-owned module array.
3. Preserve all 219 old mathematical source files and pinned dependencies unchanged. The module is positioned near `LeanPaper.ImportedSection56.FiniteKreinCone` to avoid touching PR #2's appended `6.17` window module insertion.
4. Require passing 220-module PR CI and `AXIOM_AUDIT_ACCEPTED=ALL_PROJECT_DECLARATIONS` before this target is promoted. No new result is claimed from the historical source alone.

## Serialized integration with currently pending target 6.17

The earlier [PR #2](https://github.com/randogelist/zetahyperbolic-axiom/pull/2) adds **a different module**, `Zeta5Merge.Theorem6_17`. This 6.16 branch was created from the **original frozen main** while PR #2 is pending, at the user's explicit direction. **Never merge both PRs simultaneously.** First require PR #2 CI and axiom PASS and merge PR #2. Then update/reconcile the 6.16 branch against the new `main` and require successful **221-module combined CI and transitive axiom audit** before merging 6.16. The baseline 220-module CI on this branch is insufficient evidence for the 221-module combined state.

Until that gate passes, keep this candidate as a draft/staged PR; do not alter the accepted 45-item full-manuscript tally (7/45). Selecting any third target must wait for a separate decision.
