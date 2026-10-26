# ZETA_HYPERBOLIC_TARGET_3_4_SIGNATURE_RESTRICTION_1

**Frozen single target:** finite-dimensional quadratic-signature restriction, a prerequisite for corrected Cauchy interlacing in manuscript 3.4.  
**Status:** `_construction`; no claim of full printed 3.4, source-target A-Tier admission in receiving main, or native Windows Lean verification.

## Exact donor provenance

- Historical donor: [snditeration/Section3/SignatureRestriction.lean@0cee4ea](https://github.com/randogelist/snditeration/blob/0cee4ea2e32b1f476488f92b476c4eb224285160/Zetahyperbolic/Section3/SignatureRestriction.lean).
- Donor source Git blob: `d1f107761de75eead018d29b69a4f86a476c2efc`.
- Recipient source: `src/LeanPaper/SignatureRestriction.lean`. **Verbatim identical blob**; no proof statement, import, namespace or tactic modifications.
- Donor [workflow 40188938699](https://github.com/randogelist/snditeration/actions/runs/40188938699) showed **Built Zetahyperbolic.Section3.SignatureRestriction** (without fatal Lean error in this file), but overall continuation CI **FAILED** on other modules, and its transitive axiom-audit step **was skipped**.
- Receiving baseline: [main@cb1abbe](https://github.com/randogelist/zetahyperbolic-axiom/commit/cb1abbe85bb277c823f31468142f7fdae8d0e9ba), containing the already-merged, independently audited 6.17 q-window target, **220** modules, Lean 4.33.0, pinned Mathlib `db584cd6d46c92f209a44c0f1c829460d327499d`.

## Admitted *if independent new CI and axiom gate pass*

The generic `ManuscriptChain.SignatureRestriction` namespace exports five explicit finite-dimensional `QuadraticForm ℝ E` theorems:

1. `sigPos_comp_le`: injective linear pullback cannot increase the positive quadratic index.
2. `sigPos_le_restrict_add_codimension`: restricting a quadratic form loses at most the codimension from the positive index.
3. `signature_restriction_bounds`: both inequalities together.
4. `sigPos_codimension_one`: a codimension-one restriction changes the positive index by at most one.
5. `signature_comp_bounds`: the same rank bounds under any injective finite-dimensional linear map.

These are **algebraic signature bounds**. They do **not** yet prove:

- the concrete actual ζ-weight pencil's eigenvalue-count interlacing at all real spectral thresholds;
- identification of its principal rational Hankel minors with the quadratic-form restrictions;
- strict interlacing/nonbreakdown or fixed finite-root cardinality when the slope is singular;
- the **false literal 3.4** claim that every (r\times r) principal determinant has exactly (r) finite real zeros (a counterexample is already Lean-verified in `LeanPaper.SingularPrincipalMinorExample`).

## Single-target branch build and merge gates

This branch changes exactly **one new theorem source** and three infrastructure files, plus this freeze receipt. The 220 preexisting mathematical source files and frozen lean/Mathlib pins remain unchanged.

The initial receiving PR CI must compile **221** modules and emit `AXIOM_AUDIT_ACCEPTED=ALL_PROJECT_DECLARATIONS` under only `propext`, `Quot.sound`, `Classical.choice`. No `sorryAx`, hidden/custom research axiom or proof-field admission.

This target is queued **behind** ongoing distinct source targets [PR #3 (6.16)](https://github.com/randogelist/zetahyperbolic-axiom/pull/3), [PR #4 (4.2)](https://github.com/randogelist/zetahyperbolic-axiom/pull/4), [PR #5 (6.10)](https://github.com/randogelist/zetahyperbolic-axiom/pull/5), [PR #6 (6.9)](https://github.com/randogelist/zetahyperbolic-axiom/pull/6), and [PR #7 (5.1)](https://github.com/randogelist/zetahyperbolic-axiom/pull/7); [PR #8](https://github.com/randogelist/zetahyperbolic-axiom/pull/8) is a repair to #5, not an independent paper target. Do not claim every queued PR will pass.

After accepted predecessors merge, reconcile this target against the **then-current main** while retaining all independently audited earlier sources and checking source/manifest/audit consistency. A successful baseline PR build alone is insufficient after any preceding merge. Re-run a full combined Lean and independent transitive axiom gate (expected **226** modules *only if* all five earlier independent queued modules have been admitted unchanged); require that exact CI receipt **before** merging this target into main.

**Freeze:** No other theorem, source family, research assertion or numerical witness may enter this PR. No promotion of the original 3.4 printed item or the 7/45 complete-item count follows from this isolated source.
