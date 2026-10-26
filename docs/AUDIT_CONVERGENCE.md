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

All eight historical readings come from the versioned **45-item `docs/PERSISTENT_PAPER_GAPS.md` table** (the links in the first column), with citations deduplicated by exact repository-relative path. Earlier README formatting was not consistent enough to use as the sole baseline; the register is the stable comparison unit. `✓` is a *recording convention*, and may change with editing.

## 3. Measured checkpoints

| Round | Fully A-Tier printed `F` | Rows with proof evidence `E` | Distinct cited source files `S` | Cumulative `U` | Newly cited `ΔU` | New files / round `v` | Novel source share `n` |
|---:|---:|---:|---:|---:|---:|---:|---:|
| [6](https://github.com/randogelist/zetahyperbolic-axiom/blob/8f2283eeee349b09a67f4e55b107d95a7da9f681/docs/PERSISTENT_PAPER_GAPS.md) | 7 | 36 | 42 | 42 | — | — | — |
| [12](https://github.com/randogelist/zetahyperbolic-axiom/blob/c0f97deca6dff579debd10c2f7d75ac5cb1d5d65/docs/PERSISTENT_PAPER_GAPS.md) | 7 | 36 | 53 | 53 | 11 | 1.83 | 20.8% |
| [18](https://github.com/randogelist/zetahyperbolic-axiom/blob/90475706d7cc5859902f4339198aa6a76a372af4/docs/PERSISTENT_PAPER_GAPS.md) | 7 | 37 | 61 | 62 | 9 | 1.50 | 14.8% |
| [25](https://github.com/randogelist/zetahyperbolic-axiom/blob/2a92a46dcaa8f2385c210bb30ea8dc4d7416b26d/docs/PERSISTENT_PAPER_GAPS.md) | 7 | 37 | 68 | 71 | 9 | 1.29 | 13.2% |
| [32](https://github.com/randogelist/zetahyperbolic-axiom/blob/e52dc59163a5372a58088afbdbcdbf15826d5dc0/docs/PERSISTENT_PAPER_GAPS.md) | 7 | 37 | 70 | 75 | 4 | 0.57 | 5.7% |
| [40](https://github.com/randogelist/zetahyperbolic-axiom/blob/f54eb137af1a11535c7da761d43ed90517b41355/docs/PERSISTENT_PAPER_GAPS.md) | 7 | 37 | 74 | 79 | 4 | 0.50 | 5.4% |
| [48](https://github.com/randogelist/zetahyperbolic-axiom/blob/242c11f1abdabebd966195eff05f2e104360edf7/docs/PERSISTENT_PAPER_GAPS.md) | 7 | 37 | 83 | 88 | 9 | 1.125 | 10.8% |
| [56](https://github.com/randogelist/zetahyperbolic-axiom/blob/34e89581b4b19ef47d24f6e817387317b7aa531f/docs/PERSISTENT_PAPER_GAPS.md) | 7 | 37 | 91 | 96 | 8 | 1.000 | 8.8% |

The evidence-marking counts were **49, 55, 64, 69, 74, 81, 89, 98** at rounds **6, 12, 18, 25, 32, 40, 48, 56**, respectively. Their growth is *not* treated as new proof constructions: entries can group or split mathematical lemmas, repeat sources, and change wording.

## 4. Interpretation: three different kinds of convergence

**A. Coverage / breadth plateau:** Rows with any marked proof evidence moved **36 → 37 of 45** by round 18, then stayed at **37** through round 56. This is *inventory saturation*: additional audits deepened rows already in view instead of identifying more items with proof-bearing clauses.

**B. Nonmonotone source discovery:** Marginal accepted-source citations per round moved **1.83, 1.50, 1.29, 0.57, 0.50, 1.125, then 1.000**. Round 56 newly credited **8 previously unseen Lean source paths among 91 current citations (8.8%)**, including direct actual-family counterproofs and representation-independence modules; round 48 credited 9 among 83 (10.8%) after just 4 among 74 (5.4%) at round 40. Cumulative distinct source paths climbed **42 → 79 → 88 → 96**. This rebound falsifies the simple extrapolation of a monotone decline in source discovery. The underlying accepted proof base did not change. These are **discovery counts**, not an asymptotic law, new compiled proofs, or a guarantee that the repository is exhaustively understood.

**C. Mathematical closure plateau:** `F(r)=7` at every checkpoint, so the **38 remaining literal paper items have not been promoted to complete A-Tier** by any of these reviews. Their count is unchanged: **21 partially formalized, 10 not formalized, 7 blocked**. The latest accepted `main` proof commit remained the same. Every increase in audit evidence refers to **already existing** theorems, not newly constructed Lean proofs.

**Crucial conclusion:** The *breadth of the evidence inventory plateaued*, but the **depth of newly noticed accepted proof components rebounded at round 48 and remained nonzero at round 56**. It has **not** converged to a zero-novelty state and is **not** converging to a proof of the remaining printed theorems. Increasing table size or source links is not a mathematical limit argument.

## 5. Ongoing telemetry and switching rules

On each subsequent checkpoint, append a row to §3 and record the exact README/register commit and accepted Lean/Mathlib receipts. Keep **three independent ledgers**:

1. **Proof ledger** — exact printed item or subclause, concrete mathematical data, hypotheses, fully qualified Lean name, source SHA, accepted CI and transitive axiom receipt, and original-statement equivalence. This alone changes whole-item A-Tier counts.
2. **Evidence-index ledger** — number of distinct already-audited source files newly discovered, percentage retained/reused, and new source-file discovery rate. This measures audit saturation only.
3. **Open-frontier ledger** — exact unproved analytic/arithmetic bridge and its smallest concrete Lean target, or a mathematical counterexample blocking the printed formula. Updating a description is not proof completion.

**Explicit zero-novelty sign (per reinference batch):**

> **⛔ REINFERENCE SATURATED — Δ = 0**

After a defined audit pass over the available branches and accepted Lean sources, print this exact marker **only if all four independently checked deltas are zero**:

- `ΔP=0`: no previously uncredited exact mathematical theorem/subclause that is provably covered by a passing Lean/axiom receipt, whether or not a whole printed theorem closes;
- `ΔE=0`: no previously uncredited, relevant accepted source or evidence supporting a new material proof distinction;
- `ΔO=0`: no newly discovered, corrected, or resolved mathematical obligation/counterexample that materially changes the open frontier;
- `ΔF=0`: no new verified downstream implication, checker, or equivalence that changes the formal proof frontier.

Changes in wording, formatting, descriptions, citations to already-counted proof facts, or repeated import paths do **not** count as new evidence. **An unchanged 7/45 complete-item tally alone is insufficient** to display the signal. Label each decision with the source heads, CI receipts, branch scope and the current checkpoint, and distinguish **NO NEW RESULTS FOUND IN SCANNED SOURCES** from a claim of global mathematical impossibility. When the marker appears, stop repeating the same unchanged-source sweep and redirect to `A_TIER_PLANNING` / `A_TIER_EXECUTION`, or resume upon a changed source/dependency fingerprint or new claim.

**Current sign status at the round-56 checkpoint: NOT TRIGGERED.** The latest eight-round batch credited direct Lean negative theorems for the printed 3.5/3.6 formulas, actual nearest-root limit and rational second moment, full μ/τ representation/domain lemmas, and explicit β(1) transcendence dependency proofs. The scoped novelty vector is **ΔP>0, ΔE>0, ΔO=0, ΔF=0** (no newly closed parent theorem, altered open bridge, or final transfer). The strict all-zero signal is therefore unavailable, even though the whole-item tally stayed 7/45.

**Suggested saturation rule:** Once **two consecutive batches of at least six rounds** reveal *zero newly discharged mathematical proof obligations* and **at most 0.5 newly cited accepted source modules per round**, stop repeating the same frozen-source sweep. The user may choose to continue anyway. The last pair now gives **1.125** then **1.000**, and the current batch again added substantive previously uncredited source evidence. This mechanical trigger is **not met**. Even with remaining uncredited source evidence, **A_TIER_PLANNING → A_TIER_EXECUTION** on a genuine open endpoint would create mathematical progress rather than merely deepen the inventory.

**Reset/refresh trigger:** The accepted source SHA, compiler/Mathlib dependencies, statement, or independent audit receipt changes, or a newly discovered *specific clause proof* is brought forward. Recompute counts against the changed proof base and distinguish newly **built** proofs from newly **found** old proofs. Do not guess progress between unmeasured checkpoints.

## 6. References

- [Tierlist first, then all 45 items](../README.md).
- [Detailed open-obligation register](PERSISTENT_PAPER_GAPS.md).
- [First 56 rounds of detailed cross-branch source audit](MULTIROUND_RESOLUTION_AUDIT.md).
- [Authoritative printed-item source ledger](formalization_status.json).
- [Accepted local Lean build receipt](../validation/linux/acceptance.json).

**Convergence status at round 56:** **37/45 item evidence breadth stable; 8 newly cited existing accepted source files; whole-item proof frontier static at 7/45**. Do not emit the saturation sign. No `!!!` formal closure or `!!!!` finite-witness certificate.
