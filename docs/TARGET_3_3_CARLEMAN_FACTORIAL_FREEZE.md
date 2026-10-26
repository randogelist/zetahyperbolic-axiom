# FROZEN TARGET 3.3 — abstract factorial-growth Carleman divergence

**Anchor:** `ZETA_HYPERBOLIC_TARGET_3_3_CARLEMAN_FACTORIAL_1`  
**Status:** `_construction` — one isolated **conditional** proof candidate, not manuscript 3.3 closure.  
**New Lean source:** `src/LeanPaper/CarlemanFactorialCriterion.lean`, Git blob `5460760348493a71d7fe471a3ec2d0c1ab881d33`.

## Evidence, donor and freeze

- Based on frozen accepted `zetahyperbolic-axiom/main@54136b39ec280b200c108ee48e80a5c247b1fa6b` (222 mathematical/source modules, with earlier 6.17/6.16/4.2 targets present), Lean 4.33.0, Mathlib `db584cd6d46c92f209a44c0f1c829460d327499d`.
- Source donor: [`snditeration/Section3/CarlemanDivergence.lean@0cee4ea`](https://github.com/randogelist/snditeration/blob/0cee4ea2e32b1f476488f92b476c4eb224285160/Zetahyperbolic/Section3/CarlemanDivergence.lean).
- The donor's `factorial_majorant_le_power` theorem body is retained *unchanged*. The donor's **actual-moment** rest depends on `Section3.MomentGrowth` and the failing `Section3.ShiftedMomentPositivity` from [failed CI 40188938699](https://github.com/randogelist/snditeration/actions/runs/40188938699); its Carleman source was **not compiled in that run**. No donor PASS is credited here.
- To make a true single target with no unverified dependencies, the new module expresses the non-summability conclusion for a **generic positive moment sequence** `M : ℕ → ℝ`. The explicit factorial-growth premise remains a premise and cannot be inferred from a name such as `moment`.

## What the new Lean statements say (if CI passes)

Given `M(r) > 0` and for every `r≥1`
```text
M(r) ≤ C · (2r + A)!     (C ≥ 0; A natural)
```
the donor factorial majorant provides a positive constant `B=C_*(C,A)` with
```text
M(r) ≤ (B r)^(2r),
M(r)^(-1/(2r)) ≥ 1/(B r).
```
Because the harmonic series diverges, the `carlemanTerm` series is not summable:
```text
¬ Summable (fun n : ℕ => (M (n+1))^(-1/(2*(n+1)))).
```
The module also contains `carleman_not_summable_of_power`, which starts directly from a supplied `(B r)^(2r)` bound, useful when the moment-growth estimate has already been normalized.

**Missing bridge (not claimed):** prove for **actual** manuscript moment measure `μ_{k,N,K}` the strict positivity and uniform factorial upper bound, transport these abstract quantities to the exact Carleman moment integrals, then apply the appropriate Stieltjes determinacy theorem. The original 3.3 mixed nonprincipal total-positivity endpoint remains separate (the donor 2×2 candidate has a failing upstream `ShiftedMomentPositivity`).

## Integration and merge gates

Exactly one new module is added to `src/` and registered in `modules.txt`, `lakefile.toml` and `src/LeanPaper/KernelAudit.lean`, with **all 222 previously accepted mathematical source modules unchanged**. A new CI run must validate:

1. exact pinned compiler/dependency and complete source/root/audit arrays, **223 modules**;
2. full sequential Lean compile and independent transitive proof-axiom walker printing `AXIOM_AUDIT_ACCEPTED=ALL_PROJECT_DECLARATIONS`;
3. allowed axioms exclusively `propext`, `Quot.sound`, `Classical.choice`; no `sorryAx`, research axioms or conditional proof-field shortcuts;
4. PR diff limited to this source module, its build/audit registrations and this one-target receipt.

**Merge ordering:** [PR #5 for 6.10](https://github.com/randogelist/zetahyperbolic-axiom/pull/5) is ahead in the serial admission queue, with CI pending at frozen branch source. This 3.3 target must remain draft until PR #5 (or any other intervening accepted merge) is resolved. Reconcile against the then-current `main`, recompile **all resulting modules** (at least 224 if #5 merges and there are no other changes), audit the combined result, and **only then** merge. Do not treat an old 223-module branch PASS as combined-state proof after `main` changes.

**Whole-paper tally:** unchanged at 7/45 completed literal printed items; no new unconditional ζ-result or Carleman claim about actual manuscript moments.
