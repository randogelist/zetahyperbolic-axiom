# FROZEN TARGET 6.10 — integer coefficient-Gram quadratic-growth bound

**Anchor:** `ZETA_HYPERBOLIC_TARGET_6_10_COEFFICIENT_GRAM_1`  
**Build name-tag:** `_construction`. **Do not promote this proof or merge into main until the exact combined Lean/audit gate passes.**  
**One-target source:** `src/LeanPaper/CoefficientGramGrowth.lean`; source Git blob `6bf29a9e97b5d2803f7a4f56b7c1fd5895f8bc13`.

## Original donor and scoped repair

- Original donor: [snditeration@0cee4ea — Section6/CoefficientGramGrowth.lean](https://github.com/randogelist/snditeration/blob/0cee4ea2e32b1f476488f92b476c4eb224285160/Zetahyperbolic/Section6/CoefficientGramGrowth.lean), original Git blob `7565126709a8cb010566a7f3998e1aad99be0f14`.
- [Donor CI 40188938699](https://github.com/randogelist/snditeration/actions/runs/40188938699) **FAILED**, including this source: the original line 126 reported **`field_simp made no progress on the goal`**. Its complete axiom-audit step was skipped. The donor is *not* historically PASS for this file.
- Receiving branch is based on the frozen [main@86ca99a](https://github.com/randogelist/zetahyperbolic-axiom/commit/86ca99a23d65cde4880a9005a49076c43e7bc968), pinned Lean 4.33.0 and Mathlib `db584cd6d46c92f209a44c0f1c829460d327499d`.
- Exact source repair: the failing terminal proof tactic
  ```lean
  convert hbound using 1 <;> field_simp <;> ring
  ```
  was changed **only** to
  ```lean
  convert hbound using 1 <;> (try field_simp [ne_of_gt hKpos]) <;> ring
  ```
  This prevents the `field_simp` "no progress" diagnostic on trivially simplified subgoals while retaining the positive-`K` nonzero denominator evidence. **This is a candidate tactic repair; a new compiler check must establish that it works.**
- Added `#print axioms ManuscriptChain.CoefficientGramGrowth.normalized_log_det_tendsto_zero`; all mathematical theorem statements and the other proof terms are untouched.

## Exact standalone mathematical claim

For **arbitrary** families of integer matrices `C_K : Fin(h K) → Fin(K+1) → ℤ`, assuming:

1. `h(K) ≤ K+1`;
2. the real row-vector multiplication of `C_K` is injective (full row rank), for each `K`;
3. every entry satisfies `|C_K(i,j)| ≤ (K+1)^A` for a **fixed natural** `A`;

the derived Gram `G_K = C_K C_Kᵀ` satisfies
```text
1 ≤ det(G_K) ≤ (K+1)^((2A+2)(K+1))
log(det(G_K))/K² → 0  as K→∞.
```
Source theorem `ManuscriptChain.CoefficientGramGrowth.normalized_log_det_tendsto_zero` includes no unsupplied numerical bounds.

**Critical open manuscript bridge:** This source does **not** prove that the *actual* Theorem 6.10 coefficient matrix has integer entries, independent rows, or polynomially bounded coefficients with exponent uniform in `K`; nor does it identify the **actual manuscript Gram/determinant** with this constructed matrix. In the original paper, the asymptotic potential gap and irrationality transfer remain open. Thus even a passing proof is only an A-Tier *conditional standalone lemma*, not original 6.10 closure.

## One-target branch and serialized merging

Exactly one mathematical file is added. Only three existing integration files change: `modules.txt`, `lakefile.toml`, and `src/LeanPaper/KernelAudit.lean` (full automatic transitive proof/audit inventory). All 219 baseline mathematical sources remain unchanged. The initial PR CI checks the **220-module** receiving program, including Mathlib pin and complete axiom gate; it is not equivalent to final combined acceptance.

**Merge order is strictly serialized:** [PR #2: 6.17](https://github.com/randogelist/zetahyperbolic-axiom/pull/2) → [PR #3: 6.16](https://github.com/randogelist/zetahyperbolic-axiom/pull/3) → [PR #4: 4.2](https://github.com/randogelist/zetahyperbolic-axiom/pull/4) → **this 6.10 PR**.

When #2–#4 have individually passed and merged, reconcile only this branch's intended source/registrations against the updated accepted main. Verify and independently axiom-audit **all 223 modules** together under Lean 4.33.0 with only `propext`, `Quot.sound`, `Classical.choice`, no `sorryAx` or hidden research axioms. **Do not merge on stale 220-module CI**.

On success, record passing CI/run SHA and final merge commit, and mark only the standalone lemma as accepted; do not change the whole-item manuscript count of 7/45 without proof of the actual-family bridge. No other target is added in this PR.

## Receiving-base combined 223-module repair candidate (2026-10-26)

Source replacement is taken from [isolated repair PR #8](https://github.com/randogelist/zetahyperbolic-axiom/pull/8), git blob `b58764606ad898f27236c293245bfb54365192cf`. It replaces the previous terminal `convert ... (try field_simp ...)` step with explicit `calc`, `field_simp [ne_of_gt hKpos]`, and `ring`. The historical donor still failed and this later patch is NOT yet independently accepted. The source in this branch must be verified by **fresh combined 223-module GitHub CI**, rather than borrowing either the old failed 220-module run or the repair branch's separate check.

The accepted main baseline is now `54136b39ec280b200c108ee48e80a5c247b1fa6b` (contains passing 6.17, 6.16 and 4.2 modules). This branch is merged with that base for exact plan comparison, while still contributing **only** the one new 6.10 proof and its frozen receipt.
