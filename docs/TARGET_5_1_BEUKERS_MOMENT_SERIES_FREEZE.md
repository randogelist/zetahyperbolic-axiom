# FROZEN TARGET 5.1 — actual Beukers double-integral moment series

**Anchor:** `ZETA_HYPERBOLIC_TARGET_5_1_BEUKERS_MOMENT_SERIES_1`  
**Status:** `_construction` — compile and transitive-axiom-audit required, no full 5.1 claim, no proof status promotion.  
**Receiving source:** `src/LeanPaper/BeukersMomentSeries.lean`; Git blob SHA-1 `5eff67223443f63e2447a6409ed33cf13458b038`.  
**Receiving branch baseline:** `zetahyperbolic-axiom/main@cb1abbe85bb277c823f31468142f7fdae8d0e9ba`, retaining the previously accepted 6.17 proof, Lean 4.33.0, Mathlib `db584cd6d46c92f209a44c0f1c829460d327499d`.

## External donor and exact changes

Immutable donor: [snditeration — BeukersMomentSeries.lean@0cee4ea](https://github.com/randogelist/snditeration/blob/0cee4ea2e32b1f476488f92b476c4eb224285160/Zetahyperbolic/Section5/BeukersMomentSeries.lean), Git blob SHA-1 `1ee8dd32e132768a80667f151364bca2d085b68f`.

The [donor's original CI run 40188938699](https://github.com/randogelist/snditeration/actions/runs/40188938699) **FAILED** to build this module, so no axiom-audited donor result is inherited. Its [failed workflow job 121155588555](https://github.com/randogelist/snditeration/actions/runs/40188938699) identifies three concrete diagnostics: positivity failure at line 47, norm-product mismatch at line 80 and an unresolved rational normalization at line 75/91.

Only these portability/proof repairs have been staged:

1. Replace two donor imports with existing recipient `LeanPaper.UnitLogMoments` and `Theorem_3_1_Zeta_Tail` and qualify the two Mellin-log-moment references.
2. Prove `logMonomial_nonneg` using explicit positive base and nonnegative negative-log power.
3. Prove the product-norm bound by rewriting the real norm to absolute value and using strict positivity.
4. Prove the geometric denominator normalization using explicit nonzero `1-xy`, `720(1-xy)` denominators before `field_simp; ring`.
5. Add `#print axioms` on the two main integral/diagonal moment theorems.

The rest of the donor mathematics, quantified theorem signatures, double-integral/sum definitions and proof architecture are retained. **This is only a repair candidate**: no Lean compilation of this modified source has yet been demonstrated.

## Targeted formal claim; what it does and does not prove

Define the actual *open unit-square* `square=(0,1)×(0,1)` with Lebesgue product measure and density
```text
w(x,y) = (−log(xy))^5 / (720(1−xy)).
```
The candidate proves the exact geometric-series/Mellin term decomposition and integrability, followed by
```text
∫_(0,1)^2 x^r y^t w(x,y) dx dy
  = Σ_{n≥0} (1/6) Σ_{j=0}^5
      1 / ((r+n+1)^(j+1) (t+n+1)^(6−j)).
```
For the diagonal `r=t`, this specializes to the actual tail
```text
∫_(0,1)^2 x^r y^r w(x,y) dx dy = ζ(7) − H_r^(7).
```
These statements are **candidate theorems** until a passing receiving build; they are not yet granted `!!`. Even if they pass, **off-diagonal rational moment reduction, the exact integral identification with the paper's full rational matrix pencil and weight normalization, and all infinite signed/cone consequences** must be separately audited. In particular do **not** promote the *whole* printed 5.1 from partial to complete without an exact clause comparison.

## One target, strict serial merge gate

This branch adds exactly one new Lean module, the necessary `modules.txt` / `lakefile.toml` / `src/LeanPaper/KernelAudit.lean` registrations and this freeze receipt; **all 220 accepted source modules remain untouched**. Its initial standalone proof gate is **221 modules**, not 220.

Existing queued predecessors must be processed in accepted order:
[PR #3: 6.16](https://github.com/randogelist/zetahyperbolic-axiom/pull/3) →
[PR #4: 4.2](https://github.com/randogelist/zetahyperbolic-axiom/pull/4) →
[PR #5: 6.10](https://github.com/randogelist/zetahyperbolic-axiom/pull/5) →
[PR #6: 6.9 Hermite](https://github.com/randogelist/zetahyperbolic-axiom/pull/6) →
**this target 5.1**.

Do not merge from a stale initial standalone pass. After its predecessors merge, reconcile the one target against the new `main` and require the **225-module combined Lean 4.33.0 full build and full transitive axiom audit**, with `AXIOM_AUDIT_ACCEPTED=ALL_PROJECT_DECLARATIONS`, no proof holes or custom research axioms and only `propext`, `Classical.choice`, `Quot.sound`. Verify all donor-merge paths and their source hashes, source-level statement correspondence and CI SHA. Only then mark the draft ready and merge.

**Status now:** source/code review + consistent 221-module declaration/ownership inventories; recipient CI pending. The original whole-manuscript completion count is **7/45**, unchanged.
