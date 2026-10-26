# Audit convergence — YOU_ARE_GOODWORKFLOWFRONTIER

**Purpose:** Quantify how much additional information repeated *source-inspection* rounds found in the Zetahyperbolic Leaned Paper, **separately from** whether new manuscript theorems were actually proved. This is an evidence-index saturation diagnostic, not an RH, odd-zeta, or whole-paper proof-convergence claim.

**Tracking branch:** `persistent/zetahyperbolic-paper-gap-tracker`. **Baseline mathematical source:** [`zetahyperbolic-axiom/main@86ca99a`](https://github.com/randogelist/zetahyperbolic-axiom/commit/86ca99a23d65cde4880a9005a49076c43e7bc968), Lean 4.33.0, pinned Mathlib `db584cd6d46c92f209a44c0f1c829460d327499d`, successful [219-module CI+axiom gate](https://github.com/randogelist/zetahyperbolic-axiom/actions/runs/40188664869). Historical checkpoints were measured on 26 October 2026. No new Lean source was compiled for this analysis.

## 1. Established proof tiers (unchanged)

| Marker | Tier | Admission standard |
|:---:|:---|:---|
| `!` | B-Tier | An on-paper mathematical derivation, not yet Lean-verified |
| `!!` | A-Tier | Exact statement compiled in Lean and passed the independent transitive axiom audit; explicit hypotheses remain hypotheses |
| `!!!` | Formal closure | Verified conditional transfer from finite accepted-witness predicate to the target; concrete accepted witness outstanding |
| `!!!!` | S-Tier | Concrete finite raw-data witness accepted by its terminating checker, plus verified downstream theorem |

A *partially formalized manuscript item* may contain A-Tier subtheorems; that does not promote the whole printed item to A-Tier. Refuted original claims remain **blocked** even if their corrected variants are proved.

## 2. Operational definitions of convergence

Let `r` be the audit-round checkpoint.

- **`F(r)`**: number of complete *literal printed manuscript items* admitted by the source ledger as A-Tier. At each checkpoint: **7 of 45**.
- **`E(r)`**: number of the 45 item rows with at least one `✓` marking documented positive proof evidence. This measures *coverage of the audit inventory*, **not** theorem completion.
- **`S(r)`**: number of distinct `../src/**/*.lean` paths referenced inside the 45 table rows' proof-evidence cells **at that checkpoint**. This excludes narrative links outside those rows and excludes external `snditeration` links.
- **`U(r)`**: cumulative union of distinct accepted-source paths cited by the evidence cells over **all earlier checkpoints**. It does not decrease when an old README citation is rewritten away.
- **`ΔU`**: previously unseen source paths appearing since the preceding measured checkpoint; **`v = ΔU / Δr`** is marginal source-discovery rate, **not** a rate of new mathematical proofs.
- **`n = 100·ΔU/S(r)`**: share of current snapshot's cited modules not seen at earlier checkpoints. A decreasing `n` can indicate documentation/source-discovery saturation, not an absence of mathematical proof routes.

All six historical readings come from the versioned **45-item `docs/PERSISTENT_PAPER_GAPS.md` table** (the links in the first column), with citations deduplicated by exact repository-relative path. Earlier README formatting was not consistent enough to use as the sole baseline; the register is the stable comparison unit. `✓` is a *recording convention*, and may change with editing.

## 3. Measured checkpoints

| Round | Fully A-Tier printed `F` | Rows with proof evidence `E` | Distinct cited source files `S` | Cumulative `U` | Newly cited `ΔU` | New files / round `v` | Novel source share `n` |
|---:|---:|---:|---:|---:|---:|---:|---:|
| [6](https://github.com/randogelist/zetahyperbolic-axiom/blob/8f2283eeee349b09a67f4e55b107d95a7da9f681/docs/PERSISTENT_PAPER_GAPS.md) | 7 | 36 | 42 | 42 | — | — | — |
| [12](https://github.com/randogelist/zetahyperbolic-axiom/blob/c0f97deca6dff579debd10c2f7d75ac5cb1d5d65/docs/PERSISTENT_PAPER_GAPS.md) | 7 | 36 | 53 | 53 | 11 | 1.83 | 20.8% |
| [18](https://github.com/randogelist/zetahyperbolic-axiom/blob/90475706d7cc5859902f4339198aa6a76a372af4/docs/PERSISTENT_PAPER_GAPS.md) | 7 | 37 | 61 | 62 | 9 | 1.50 | 14.8% |
| [25](https://github.com/randogelist/zetahyperbolic-axiom/blob/2a92a46dcaa8f2385c210bb30ea8dc4d7416b26d/docs/PERSISTENT_PAPER_GAPS.md) | 7 | 37 | 68 | 71 | 9 | 1.29 | 13.2% |
| [32](https://github.com/randogelist/zetahyperbolic-axiom/blob/e52dc59163a5372a58088afbdbcdbf15826d5dc0/docs/PERSISTENT_PAPER_GAPS.md) | 7 | 37 | 70 | 75 | 4 | 0.57 | 5.7% |
| [40](https://github.com/randogelist/zetahyperbolic-axiom/blob/f54eb137af1a11535c7da761d43ed90517b41355/docs/PERSISTENT_PAPER_GAPS.md) | 7 | 37 | 74 | 79 | 4 | 0.50 | 5.4% |

The evidence-marking counts were **49, 55, 64, 69, 74, 81** at rounds **6, 12, 18, 25, 32, 40**, respectively. Their growth is *not* treated as 32 new theorems: entries can group or split mathematical lemmas, repeat sources, and change wording.

## 4. Interpretation: three different kinds of convergence

**A. Coverage / breadth saturation:** Rows with any marked proof evidence moved **36 → 37 of 45** by round 18, then stayed at **37** through round 40. This is *inventory saturation*: additional audits deepened rows already in view instead of identifying more items with proof-bearing clauses.

**B. Source discovery deceleration:** Marginal new source citations dropped through **1.83, 1.50, 1.29, 0.57, 0.50 newly discovered Lean source paths per round**. At the 40-round snapshot, **4 of 74** distinct proof-linked local source files were novel relative to the previous checkpoints (**5.4%**); the other **70** had been cited earlier. Cumulative distinct source files climbed from **42 to 79**. The direction is consistent with repeated inspection of a fixed finite repository gradually exhausting *the proofs we noticed*, but it is **not a fitted asymptotic law**, guarantee that all source files were audited, or an argument that new proofs are impossible.

**C. Mathematical closure plateau:** `F(r)=7` at every checkpoint, so the **38 remaining literal paper items have not been promoted to complete A-Tier** by any of these reviews. Their count is unchanged: **21 partially formalized, 10 not formalized, 7 blocked**. The latest accepted `main` proof commit remained the same. Every increase in audit evidence refers to **already existing** theorems, not newly constructed Lean proofs.

**Crucial conclusion:** The *output converged toward an increasingly saturated inventory of known, already-proved components*, **not** toward a proof of the remaining printed theorems. Increasing table size or source links is not a mathematical limit argument.

## 5. Ongoing telemetry and switching rules

On each subsequent checkpoint, append a row to §3 and record the exact README/register commit and accepted Lean/Mathlib receipts. Keep **three independent ledgers**:

1. **Proof ledger** — exact printed item or subclause, concrete mathematical data, hypotheses, fully qualified Lean name, source SHA, accepted CI and transitive axiom receipt, and original-statement equivalence. This alone changes whole-item A-Tier counts.
2. **Evidence-index ledger** — number of distinct already-audited source files newly discovered, percentage retained/reused, and new source-file discovery rate. This measures audit saturation only.
3. **Open-frontier ledger** — exact unproved analytic/arithmetic bridge and its smallest concrete Lean target, or a mathematical counterexample blocking the printed formula. Updating a description is not proof completion.

**Suggested saturation rule:** Once **two consecutive batches of at least six rounds** reveal *zero newly discharged mathematical proof obligations* and **at most 0.5 newly cited accepted source modules per round**, stop repeating the same frozen-source sweep. The user may choose to continue anyway. The present last pair gives **0.57** then **0.50**, so this specific mechanical trigger has **not quite been met**. Still, low source novelty already makes **A_TIER_PLANNING → A_TIER_EXECUTION** on an actual open endpoint more productive than further rephrasing of the same status inventory.

**Reset/refresh trigger:** The accepted source SHA, compiler/Mathlib dependencies, statement, or independent audit receipt changes, or a newly discovered *specific clause proof* is brought forward. Recompute counts against the changed proof base and distinguish newly **built** proofs from newly **found** old proofs. Do not guess progress between unmeasured checkpoints.

## 6. References

- [Tierlist first, then all 45 items](../README.md).
- [Detailed open-obligation register](PERSISTENT_PAPER_GAPS.md).
- [First 40 rounds of detailed cross-branch source audit](MULTIROUND_RESOLUTION_AUDIT.md).
- [Authoritative printed-item source ledger](formalization_status.json).
- [Accepted local Lean build receipt](../validation/linux/acceptance.json).

**Convergence status at round 40:** **documentary inventory trending toward saturation; whole-item proof frontier static**. No `!!!` formal closure or `!!!!` finite-witness certificate.
