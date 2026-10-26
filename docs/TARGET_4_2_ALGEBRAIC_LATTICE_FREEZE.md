# FROZEN TARGET 4.2 — algebraic approximation transfer on the manuscript lattice

**Anchor:** `ZETA_HYPERBOLIC_TARGET_4_2_ALGEBRAIC_LATTICE_1`  
**One-target status:** `_construction` — **no acceptance, merge, or whole-item promotion** before independent receiving-repo compilation + transitive axiom audit.

## Reproducible provenance

- Donor repository and immutable commit: [snditeration@0cee4ea](https://github.com/randogelist/snditeration/blob/0cee4ea2e32b1f476488f92b476c4eb224285160/Zetahyperbolic/Section4/AlgebraicLattice.lean).
- Original source Git blob SHA-1: `ea8a842e1b9af4aa78b5efbdc9e1d50b95b0690e`.
- Receiving source: `src/LeanPaper/Section4AlgebraicLattice.lean`.
- Porting changes **only**: import `Zetahyperbolic.Section4.AlgebraicLimsup` → `LeanPaper.Section4AlgebraicLimsup`; namespace `ManuscriptChain.Section4AlgebraicLattice` → `LeanPaper.Section4AlgebraicLattice`. The theorem's hypotheses, conclusion and proof steps are unmodified.
- Original donor CI [run 40188938699](https://github.com/randogelist/snditeration/actions/runs/40188938699) reported **`Built Zetahyperbolic.Section4.AlgebraicLattice`**, but the **overall build FAILED** for ten other modules. Its downstream all-declaration axiom gate was **SKIPPED**. Therefore the port is **not yet A-Tier accepted** in this repository.
- Receiving baseline `main@86ca99a23d65cde4880a9005a49076c43e7bc968`; Lean 4.33.0 and pinned Mathlib `db584cd6d46c92f209a44c0f1c829460d327499d`; 219 pre-existing module sources are frozen.

## Exact target statement

`LeanPaper.Section4AlgebraicLattice.proposition_4_2` uses:

- arbitrary positive lattice spacing `d0`, `d≥1`, `Q : ℕ → ℤ[X]`;
- explicitly supplied eventual linear degree, nonzero *quadratically decaying actual polynomial values*, and root separation along `Q(d0*n)`;
- a real upper limsup of the logarithmic naive coefficient height;
- explicit strict exponent-rate gap and exponent `λρd/(ε−(d−1)Λ)`;
- the uniform conclusion for **every irreducible integer polynomial representing an algebraic approximant of degree at most `d`**, with its chosen complex root and a large enough coefficient height.

It applies accepted `LeanPaper.Section4AlgebraicLimsup.algebraic_transfer_upperHeight` and `eventual_height_of_limsup`. **All quantitative hypotheses remain hypotheses.** This does not establish those bounds for the original ζ(5) primitive integer-polynomial family, nor any unconditional irrationality measure.

## CI / integration order

**Earlier frozen single-target PRs have priority:** [#2 — 6.17 corrected q-window](https://github.com/randogelist/zetahyperbolic-axiom/pull/2), [#3 — 6.16 compact positive ratio](https://github.com/randogelist/zetahyperbolic-axiom/pull/3).

1. This branch from frozen original `main` adds only one new theorem module, its `modules.txt`/Lake roots, the `LeanPaper.KernelAudit` import+project-array entry, and this receipt. A 220-module PR CI is the first isolated diagnostic; require it to PASS and print `AXIOM_AUDIT_ACCEPTED=ALL_PROJECT_DECLARATIONS`.
2. **Never merge this branch while PR #2 or PR #3 has not been accepted and merged.** Keep this PR draft until both predecessors are in `main`.
3. Reconcile the frozen branch against the updated accepted `main`, verify that all three new modules are retained and that the combined **222-module build + full transitive axiom audit** passes; test against that exact combined commit, not against the old baseline.
4. Only then merge this specific PR, verify `main` has all three donor modules, and update paper-status ledger. **No other target in this branch**.

**Current status:** source port and local manifest consistency verified; native Windows Lean build and receiving Linux CI results are pending. No theorem count promotion: the manuscript remains **7/45 complete A-Tier literal items**.
