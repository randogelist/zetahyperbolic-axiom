# Zetahyperbolic — persistent missing-paper tracker

**Repository:** [`randogelist/zetahyperbolic-axiom`](https://github.com/randogelist/zetahyperbolic-axiom)  
**Branch:** `persistent/zetahyperbolic-paper-gap-tracker`  
**Purpose:** permanently track every unproved, partially completed or mathematically incorrect item in the original 52-page Zetahyperbolic manuscript, together with the exact Lean proof needed to close it. **`snditeration` is a cross-repository source of reusable proofs, not the repository being modified.**

**Full research inventory:** [45-item missing-pieces register and targeted proof agenda](docs/PERSISTENT_PAPER_GAPS.md).  
**Original proof repository:** [`main` README](https://github.com/randogelist/zetahyperbolic-axiom/blob/86ca99a23d65cde4880a9005a49076c43e7bc968/README.md). This tracking branch deliberately does not edit active Lean proof modules.

## 1. Established proof tiers

The **YOU_ARE_GOODWORKFLOWFRONTIER** tierlist (from [WORKFLOW.txt](WORKFLOW.txt)) is:

| Marker | Tier | Definition |
|:---:|:---|:---|
| `!` | **B-Tier** | On-paper mathematical derivation, conditional on reasoning; not yet Lean-verified. |
| `!!` | **A-Tier** | The exact statement parses, elaborates and compiles in Lean; its **transitive axiom audit** passes with no `sorryAx`, hidden axioms or unstated hypotheses. An A-Tier *conditional theorem* proves only the stated implication. |
| `!!!` | **Formal closure** | A-Tier conditional chain reduces the target to acceptance of **finite witness data** by a terminating checker; no actual accepted witness yet. |
| `!!!!` | **S-Tier** | Concrete finite witness data pass the checker, and the axiom-audited downstream Lean transfer to the final claim passes. |

**Partial proof:** `!!` may already apply to individual mathematical components, **not** to the whole printed theorem. `Partially formalized`, `Not formalized` and `Blocked` describe manuscript coverage, **not** extra proof tiers. A false literal claim remains blocked even if a corrected proposition is fully A-Tier. No manuscript-wide `!!!` or `!!!!` certificate is asserted.

## 2. Manuscript items, grouped by proof status

| Whole printed item | Item numbers | Count |
|:---|:---|---:|
| `!!` A-Tier — complete printed result | 2.2, 2.3, 2.4, 2.5, 3.1, 4.3, 5.4 | 7 |
| A-Tier components — whole printed result **open** | 3.3, 3.7, 3.8, 3.9, 4.1, 4.2, 4.4, 4.5, 4.6, 4.7, 4.8, 5.1, 5.2, 5.3, 6.2, 6.4, 6.6, 6.9, 6.10, 6.17, 6.18 | 21 |
| Not formally established at item level | 5.6, 5.7, 6.1, 6.5, 6.7, 6.8, 6.11, 6.12, 6.14, 6.16 | 10 |
| Literal printed statement **blocked** | 3.2, 3.4, 3.5, 3.6, 6.3, 6.13, 6.15 | 7 |

**All 45 items**, their names, exact outstanding mathematical bridges and individual whole-item tier ratings appear in the [full register](docs/PERSISTENT_PAPER_GAPS.md), **immediately after its tier definitions**. A completed component does not remove the remaining obligations of a partially proved theorem.

## 3. Verified mathematical baseline (25 October 2026)

**219 Lean modules passed compilation and independent transitive axiom auditing**, covering 3,135 declarations, including 2,489 kernel theorem declarations (private/generated included). [Passing build](https://github.com/randogelist/zetahyperbolic-axiom/actions/runs/40188664869). The corresponding Leaned Paper is substantially advanced mathematically, with real rational-moment identities, positive actual Gram pencils, unconditional hyperbolicity and zero-free disks, spectral and strict Newton/reciprocal-moment results, algebraic transfer, and independent odd-beta transcendence.

Printed manuscript classification: **7 complete**, **21 partial**, **10 not formalized**, **7 literally blocked**. The 7 fully proved numbered results are **2.2, 2.3, 2.4, 2.5, 3.1, 4.3 and 5.4**. These numbers count whole paper statements, **not** Lean declarations. Source: [audited 45-result manuscript status](docs/FORMALIZATION_STATUS.md).

## 4. Missing-work priorities

| Workstream | Necessary closure |
|:---|:---|
| **F2 — ζ(5) quantitative result** | Actual `K=30n,N=3n` denominator/integrality and `exp(-K²/2500)` decay, genuine spectral `11.411` exponent, effective transfer to the printed irrationality measure `25687`. Fauzan's cited `K=40n,N=3n` estimates cannot simply be reused. |
| **F1 — spectral/analytic** | 3.3 mixed-minor strict positivity + Carleman, 3.4 corrected rank-aware interlacing, 3.5–3.6 normalized finite-rank replacements, 3.8 genuine Christoffel–Darboux/Laplace bridge, 3.9 Hurwitz/Dirichlet integral pencil. |
| **F3 — ζ(7), Beukers, β(4)** | Actual double-integral moments and infinite Krein tails, 5.6 outer prime sum `453803/288000` and corrected local pole gain, 5.7 q-adic Hermite blocks. **6.3(2)'s printed cone is false at h=4** and requires a new tail-controlled construction. |
| **F4 — multiweight and prime arithmetic** | Actual combined zeta–beta density, q-/2-adic local nonvanishing and height estimates, 6.13 secant-series sign correction, 6.15 exterior asymptotic repair, 6.17 harmonic pole-class repair. |

**Key diagnostic:** the paper's 4.6 lower height bound uses an upper bound in the wrong direction; 4.8's claimed global rational-root exclusion similarly applies a lower root-gap as an upper bound. These are *unproved paper inferences*, not reasons to discard the certified structural mathematics.

## 5. Persistent tracking procedure

- Work from the actual manuscript and the existing [machine-readable item ledger](docs/formalization_status.json), preserve all 45 item IDs, and freeze unchanged certified Lean modules.
- For each improvement record **the literal paper claim, exact constructed function/matrix, fully qualified Lean theorem, audited commit/runner receipt, retained hypotheses, and next open endpoint**.
- Keep **corrected theorem**, **failed printed claim**, **conditional implication**, and **unconditional proof** distinct. No guessed compiler PASS or imported assertions as axioms.
- Pull useful statements from [`snditeration`](https://github.com/randogelist/snditeration) only with pinned source and a proved translation bridge. Its main checkpoint reports **846 audited theorem declarations**; its wider continuation branch currently has failed CI, so these extra files are candidates only.
- The standard workflow remains `YOU_ARE_GOODWORKFLOWFRONTIER`, `LEAN_ANCHORINGS`, Lean 4.33.0 with cached pinned Mathlib. A documentation commit to this branch is **not** a new Lean build or native Windows audit.

**Status: full manuscript remains open.** No unproved claim of ζ(5)/ζ(7) irrationality from the paper's explicit family, finite-witness admission or whole-paper completion is made.
