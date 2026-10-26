# FROZEN TARGET 6.17 — corrected q-prime harmonic windows

**Checkpoint tag:** `ZETA_HYPERBOLIC_TARGET_6_17_Q_WINDOW_1`  
**Intake state:** `_construction` until receiving-repository Lean 4.33.0 compilation and independent all-declaration axiom audit pass.  
**Only target in this branch:** the **finite arithmetic index-window part of manuscript Theorem 6.17**, NOT its entire printed theorem.

**Source:** `src/Zeta5Merge/Theorem6_17.lean` (unmodified donor source).  
**Source archive:** uploaded `zeta5-spectral-lean (1).zip`, `Zeta5Merge/Theorem6_17.lean`.  
**Source SHA-256:** `6117841ec643d5abe560d93ece84ea8bfb13777c213def2b638ae5ed1488af98`.  
**Git blob SHA-1:** `19b50be824106eb6561109f37eaf75c5fbcc198b` (exact archive byte match).  
**Historical donor evidence:** `verification/repairs/Zeta5Merge.Theorem6_17.log` printed only `propext`, `Classical.choice`, `Quot.sound` for its selected endpoint declarations, and `verification/MERGE_BUILD.json` marked this file `PASS` for Lean 4.33.0. Not yet evidence that it passed in the receiving repo.
**Receiving base:** `main@86ca99a23d65cde4880a9005a49076c43e7bc968`, Lean `4.33.0`, Mathlib `db584cd6d46c92f209a44c0f1c829460d327499d`.

## Exact admitted finite-math scope after recipient audit

- `parameters`: odd `q>=3`, `height=(q+1)/4`, `shift=(q+3)/4`, `degree=(q-1)/2`.
- `harmonic_windows`, `low_no_multiple`: no `q`-multiple in the lower odd-harmonic denominator range.
- `high_multiple_iff`, `high_unique_multiple`: exactly one high-range index with a `q`-divisible odd denominator.
- `row_support_disjoint`, `index_difference_not_dvd`, `shift_not_dvd`: finite polynomial row support disjointness and elementary index nondivisibility.
- `shift_mod_four_one`, `shift_mod_four_three`, `q41_regression`: parity-specific shift and the omitted first-row regression.

These lemmas address the **index error diagnosed** by the accepted `LeanPaper.BetaHarmonicIndexObstruction` (`q=11` and `q=41`). The adjusted high shift is **not a proof** that the original manuscript's concrete β-pencil rows have the required q-adic leading block, coefficient integrality or determinant valuation.

## Merge gate

1. Preserve all 219 old mathematical modules and the pinned compiler/Mathlib fingerprints.
2. Add exactly one source module `Zeta5Merge.Theorem6_17`; the only modifications to existing implementation files are the build plan (`modules.txt`), Lake roots (`lakefile.toml`) and the aggregation audit (`LeanPaper.KernelAudit`).
3. Verify the original source's exact byte SHA and compare the PR diff to the frozen `main` head.
4. GitHub pull-request CI must pass its sequential **220-module build** and `AXIOM_AUDIT_ACCEPTED=ALL_PROJECT_DECLARATIONS`. No unexplained custom axioms or placeholders.
5. Only then merge to `main`. Do not promote the original Theorem 6.17 to whole-item A-Tier until the missing actual β-moment and q-adic valuation endpoints are proved.
6. **Stop** after this one target. The next merge target must be selected in a separate subsequent turn.

**Receipt fields to fill on acceptance:** PR number, passing workflow ID and SHA, final merge SHA, 220-module axiom gate, and source hash. No accepted new compiler claim is made by this frozen-target definition.
