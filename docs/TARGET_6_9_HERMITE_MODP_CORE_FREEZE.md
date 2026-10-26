# Frozen single target: Hermite interpolation / mod-p unimodularity core

**Target ID:** `ZETA_HYPERBOLIC_TARGET_6_9_HERMITE_MODP_CORE_1`  
**Mode:** `_construction`; freeze the exact standalone target scope, not an assertion that original paper Theorem 6.9 is complete.  
**Receiving branch:** `feat/gwf-target-69-hermite-modp-core-v0_1_0`.  
**Receiving baseline:** `main@cb1abbe85bb277c823f31468142f7fdae8d0e9ba` (already accepted PR #2, 220 modules, pinned Lean 4.33.0 and Mathlib `db584cd6d46c92f209a44c0f1c829460d327499d`).

## Donor provenance and exact transformation

Donor ZIP: `ODD_ZETA_3X3_MERGED_v0_3_0.zip` supplied in the project; donor member `ODD_ZETA_3X3_MERGED_v0_3_0/Zeta5/HermiteBasisCore.lean`. Historical donor **`CACHED_PASS`** receipt is at `evidence/ODD3_selected_sourcehash_receipts.json` in `GOODWORKFLOWFRONTIER_CROSS_PROJECT_INTAKE_v0_1_0_construction.zip`; original Lean 4.33 source hash SHA-256 `d7e0291ea1f2f2dac394802639f3266789359dee940cf529a785a614a69ae1bf`, historical `.olean` SHA-256 `2f72549db92b5b578bffb8f624c840e21de3056bb9ad011dfef91e4c31f720b1`. These are **donor-history evidence**, not a receiving-build receipt.

One source file was ported: `src/Zeta5/HermiteBasisCore.lean`. The introductory donor documentation and internal theorem docstrings were removed to keep the source minimal; the **five theorem statements and their Lean proof terms remain unchanged**. The resulting portable file has SHA-256 `6e3ac9dab67fcbbcfc36fbcc138dfefa58188894a473f489448b4309dec060d5` and Git blob `9a53b2bddaad5d2ea60ccc4d4c269c31f6cf618c`. It imports only `Mathlib`; no assumed research axioms, no admitted proof fields, and no `sorry` or `admit` occur in the source.

## Finite algebra theorems to certify

The exact selected theorem is `Zeta5.HermiteBasisCore.det_coeffMatrix_unimodular'`. Under a **prime** `p`, pairwise distinct nodes `u : κ → ZMod p`, finite multiplicities `m`, an explicit equivalence identifying the rows with `Σ_a Fin(m a)`, and **an actual congruence `hg`** identifying each integer polynomial row modulo `p` with the Hermite row:

- the rational coefficient matrix formed from those integer rows has **nonzero determinant**;
- its rational determinant has `padicValRat p` equal to **zero**.

Dependencies `X_add_C_pow_isCoprime_prod`, `natDegree_hermite`, `hermite_sum_eq_zero`, and `det_coeffMatrix_hermite_ne_zero'` prove generic coprimeness, degree, linear independence, and determinant nonsingularity over an arbitrary field.

**Missing bridge:** this is the generic p-adic Hermite interpolation basis used in another `Zeta5` project. An independent receiving-project theorem must identify the actual triple-pole / multichannel manuscript polynomial rows, verify distinct nodes mod `p`, prove their dimension and the precise `hg` congruence. Neither the **printed 6.9 q-adic valuation** nor the separate 6.17 arithmetic theorem follows from this standalone module. Status of those printed items is unchanged.

## Single-target merge gate and ordering

The branch adds **one** donor Lean source, and only the three existing CI integration files are updated: `modules.txt`, `lakefile.toml`, `src/LeanPaper/KernelAudit.lean`. All existing 220 mathematical modules remain untouched. Initial standalone branch requires a successful **221-module** Lean 4.33.0 build and actual independently traversed full transitive axiom audit, allowed axioms `propext`, `Quot.sound`, `Classical.choice` only.

This target is queued **after** the already frozen PRs in their strict serial merge order:

1. [PR #3 — 6.16 compact ratio](https://github.com/randogelist/zetahyperbolic-axiom/pull/3): merged after combined 221-module audit;
2. [PR #4 — 4.2 algebraic lattice](https://github.com/randogelist/zetahyperbolic-axiom/pull/4): merged after combined 222-module audit;
3. [PR #5 — 6.10 coefficient Gram](https://github.com/randogelist/zetahyperbolic-axiom/pull/5): merged after combined 223-module audit;
4. **This one 6.9 Hermite core target:** reconcile against accepted `main`, require **224-module combined build and full transitive axiom audit on that new exact SHA**, then merge only if it passes.

Do not confuse an earlier standalone passing 221-module run with acceptance of the later 224-module combined code. Do not add any other donor module or change the 45-item full manuscript ledger on this PR. **The user may select the next single target independently only after a merge.**
