# Cross-project proof intake — manuscript gap closures
**Branch:** YOU_ARE_GOODWORKFLOWFRONTIER  
**Date:** 26 October 2026  
**Status:** SOURCE COLLECTED / MERGE NOT YET ADMITTED (`_construction`)

The goal is to **collect exact mathematics from the user's other Lean projects and repository branches**, then merge only clauses whose actual objects and assumptions match the original 52-page Zetahyperbolic manuscript. No theorem status is promoted by this intake itself.

**Canonical receiving source**: [zetahyperbolic-axiom/main@86ca99a](https://github.com/randogelist/zetahyperbolic-axiom/commit/86ca99a23d65cde4880a9005a49076c43e7bc968), [219-module Lean 4.33.0 CI and independent axiom audit PASS](https://github.com/randogelist/zetahyperbolic-axiom/actions/runs/40188664869), Mathlib `db584cd6d46c92f209a44c0f1c829460d327499d`. Preserve `LEAN_ANCHORINGS`, the named `ZETA_HYPERBOLIC_ANCHOR_1` through `ZETA_HYPERBOLIC_ANCHOR_7`, and PASS-ONCE source/`.olean` reuse. Current 45-item tally remains **7 complete, 21 partial, 10 not formalized, 7 blocked**.

## 0. Frozen-target merge queue and first accepted merger (26 October 2026)

| Order | Target | PR / branch | Verified stage |
|---:|---|---|---|
| **1** | **6.17** corrected q-prime harmonic-index windows | [PR #2](https://github.com/randogelist/zetahyperbolic-axiom/pull/2), `feat/gwf-target-617-corrected-q-window-v0_1_0` | **MERGED** at [`cb1abbe85bb277c823f31468142f7fdae8d0e9ba`](https://github.com/randogelist/zetahyperbolic-axiom/commit/cb1abbe85bb277c823f31468142f7fdae8d0e9ba); [CI #40260089735](https://github.com/randogelist/zetahyperbolic-axiom/actions/runs/40260089735) **PASS**, 220-module plan, independent full transitive axiom audit `AXIOM_AUDIT_ACCEPTED=ALL_PROJECT_DECLARATIONS`, only `propext`, `Classical.choice`, `Quot.sound` |
| 2 | **6.16** compact positive-ratio finite comparison | [draft PR #3](https://github.com/randogelist/zetahyperbolic-axiom/pull/3), `feat/gwf-target-616-compact-ratio-v0_1_0` | Branch reconciled **after #2 merge** at `9814065ae1cba0098f873fea4fc0782dcba23187`; combined 221-module [CI #40262637451](https://github.com/randogelist/zetahyperbolic-axiom/actions/runs/40262637451) pending, merge **NOT admitted** |
| 3 | **4.2** algebraic approximation lattice `d₀` | [draft PR #4](https://github.com/randogelist/zetahyperbolic-axiom/pull/4), `feat/gwf-target-42-algebraic-lattice-v0_1_0` | Independent 220-module diagnostic CI pending; after #3 merge requires 222-module combined verification |
| 4 | **6.10** coefficient-Gram log growth for polynomially bounded integer matrices | [draft PR #5](https://github.com/randogelist/zetahyperbolic-axiom/pull/5), `feat/gwf-target-610-coefficient-gram-growth-v0_1_0` | One terminal proof-tactic repair to failed `snditeration` donor; independent [CI #40262349310](https://github.com/randogelist/zetahyperbolic-axiom/actions/runs/40262349310) pending; after #4 merge requires 223-module combined verification |

**Admission distinction:** The verified **finite q-index-window** theorem in #2 is newly merged A-Tier *source mathematics*, **not the original whole printed 6.17 theorem** (whose q-adic valuation and actual dual-basis identification remain open). The manuscript-wide full-item tally stays **7/45**. No claim is made that pending diagnostic or combined CI has passed. Do not merge #3–#5 simultaneously: each subsequent merge must contain earlier admitted mathematical sources and pass a fresh complete axiom gate.

## 1. Two distinct donor evidence classes

**A — Historically passing donors, collect now for isolated receiving-repo replay.**

- Uploaded `zeta5-spectral-lean (1).zip` contains 28 selected source compile receipts **inside the ZIP** (`verification/MERGE_BUILD.json`) for Lean 4.33.0 including `Zeta5Merge/Theorem6_10.lean`, `Theorem6_16.lean`, `Theorem6_17.lean`, `Theorem6_18.lean`, `OddZeta/ResidueMoments.lean`, `OddZeta/DecompositionBridge.lean`. Each selected `PASS` receipt's SHA-256 was compared to the ZIP source.
- Uploaded `ODD_ZETA_3X3_MERGED_v0_3_0.zip` has a **127-module Linux Lean 4.33 source-hash/cached-compilation manifest**, including `Zeta5/HermiteBasisCore.lean`, `Zeta5/HermiteBasis.lean`, `Merge/ImpactGEtaZeta.lean` and `Merge/LinearFormLimit.lean`. All four extracted sources match that manifest's SHA-256. Full `Zeta5` imported endpoint **is not certified** as an axiom-clean source by the selected 28-module merge; the original `Zeta5/Axioms.lean` contains a PNT axiom and must not be used as an allowed proof dependency.

**B — Failed/unfinished GitHub continuation: useful source mathematics, not admitted A-Tier.**

Donor [snditeration/continuation@0cee4ea](https://github.com/randogelist/snditeration/tree/0cee4ea2e32b1f476488f92b476c4eb224285160) introduced many gap-specific modules. [CI 40188938699 FAILED](https://github.com/randogelist/snditeration/actions/runs/40188938699) with ten specific failing Lean modules; the subsequent transitive-axiom gate **was skipped**. Some files such as `Section4/AlgebraicLattice` and `Section6/PotentialGap` **compiled in that failed build**; this does not establish accepted, independently axiom-audited proof status for their declarations. For source-level comparison, keep them quarantined until an isolated successful CI/axiom audit.

The independent [snditeration/main@c521749](https://github.com/randogelist/snditeration/commit/c521749190cce9981b0f108a8edc8034420f6420) **passes CI** and already provides exact weight-five sign/root-side components useful to 3.3. Deduplicate against `LeanPaper.SlopeSignature`, `PoleWeightSigns`, and the current local 3.3 bridge before importing.

## 2. Ranked merge candidates and explicit missing bridges

| Priority | Original item | Donor / actual candidate theorem | Verified limit / next merge gate |
|---|---|---|---|
| **P0** | **6.16** Zeta–Beta multiweight comparison | `Zeta5Merge.Theorem6_16.weight_comparison_of_compact_ratio` — historic Lean 4.33 PASS; proves uniform bounds from a compact, continuous, **positive** ratio including both endpoints | New receiving-repo import and axiom audit. Then prove the actual beta/zeta mixed-density *ratio identity*, compactification, and positivity **at 0 and 1**. Until then only a conditional comparison, not 6.16 |
| **P0** | **6.17** q-local Zeta–Beta arithmetic | `Zeta5Merge.Theorem6_17.harmonic_windows`, `low_no_multiple`, `high_unique_multiple`, `row_support_disjoint`, with `q41_regression`; historic Lean 4.33 PASS | Pair with accepted `LeanPaper.BetaHarmonicIndexObstruction` (q=11,41 counterdiagnostics). Prove actual basis rows' congruence and valuations. Repaired index windows **alone** do not prove 6.17 |
| **P0** | **4.2** degree-d algebraic approximation | [snditeration Section4/AlgebraicLattice.lean](https://github.com/randogelist/snditeration/blob/0cee4ea2e32b1f476488f92b476c4eb224285160/Zetahyperbolic/Section4/AlgebraicLattice.lean), `proposition_4_2` on the exact positive `d0` lattice | **Built in failed CI**, independent axiom audit skipped. Isolate and recompile, then connect to accepted `LeanPaper.Section4AlgebraicLimsup`; verify the exact original minimal-polynomial and height hypotheses. Could upgrade 4.2 conditional statement only after literal match |
| **P1** | **3.3(1)** nonprincipal mixed minors | [ShiftedMomentPositivity](https://github.com/randogelist/snditeration/blob/0cee4ea2e32b1f476488f92b476c4eb224285160/Zetahyperbolic/Section3/ShiftedMomentPositivity.lean) → [MixedMomentTwo](https://github.com/randogelist/snditeration/blob/0cee4ea2e32b1f476488f92b476c4eb224285160/Zetahyperbolic/Section3/MixedMomentTwo.lean), targeting `GRAM_MIXED_TWO_MINOR_POSITIVE` | Parent fails Lean at lines **86,128**; downstream mixed 2×2 theorem unverified. Need an actual Stieltjes measure and determinant identification. **All sizes** of mixed minors remain open beyond a proven 2×2 step |
| **P1** | **3.3(1)** Carleman determinacy | [MomentGrowth](https://github.com/randogelist/snditeration/blob/0cee4ea2e32b1f476488f92b476c4eb224285160/Zetahyperbolic/Section3/MomentGrowth.lean) → [CarlemanDivergence](https://github.com/randogelist/snditeration/blob/0cee4ea2e32b1f476488f92b476c4eb224285160/Zetahyperbolic/Section3/CarlemanDivergence.lean) | Blocked by above dependency; target is `carlemanSeries_not_summable` for *actual* moments. Add Stieltjes Carleman-uniqueness transfer. A divergent Carleman series alone is not yet all mixed total positivity |
| **P1** | **3.4** corrected singular-rank interlacing | [CauchyInterlacing](https://github.com/randogelist/snditeration/blob/0cee4ea2e32b1f476488f92b476c4eb224285160/Zetahyperbolic/Section3/CauchyInterlacing.lean), `actual_eigenvalue_count_interlacing` | Fails CI near lines **33,140**. Transport the valid **threshold-count** interlacing of positive-base pencil eigenvalues; do **not** restore the false printed `r` finite roots for singular slopes |
| **P1** | **5.1** true ζ(7) two-variable measure | [BeukersMomentSeries](https://github.com/randogelist/snditeration/blob/0cee4ea2e32b1f476488f92b476c4eb224285160/Zetahyperbolic/Section5/BeukersMomentSeries.lean), `integral_density_moment_series`, `diagonal_moment` | Failed lines **47,75,80**. Repair convergence/Fubini/positive integrability, then separately prove **off-diagonal rational harmonic difference** in manuscript (5.2); connect to accepted `LeanPaper.ImportedSection56.DualMoments`. No 5.1 closure yet |
| **P1** | **3.8** actual orthogonal polynomial/CD kernel | [ChristoffelDarboux](https://github.com/randogelist/snditeration/blob/0cee4ea2e32b1f476488f92b476c4eb224285160/Zetahyperbolic/Section3/ChristoffelDarboux.lean), `kernel_eq_inverseGram` and `actualPolynomial` | Multiple errors (including unknown `Matrix.diagonal_mulVec` at **118**). Align LDL/orthogonal polynomial definitions with `LeanPaper.SymmetricPoleSpectrum`; then prove actual measure pairing. Root multiset equality in main does not prove CD identity |
| **P1** | **6.10** coefficient Gram asymptotic | [CoefficientGramGrowth](https://github.com/randogelist/snditeration/blob/0cee4ea2e32b1f476488f92b476c4eb224285160/Zetahyperbolic/Section6/CoefficientGramGrowth.lean), `normalized_log_det_tendsto_zero` | One reported `field_simp` failure at **126**. Even after repair, theorem assumes **actual coefficient entries grow at most polynomially**; prove that bound and canonical-row independence or cannot conclude anything about manuscript Gram |
| **P1** | **6.9 / 6.17** Hermite/q-local block | `Zeta5.HermiteBasisCore.det_coeffMatrix_unimodular'`, `Zeta5.HermiteBasis.det_coeffMatrix_unimodular` in 127-module historically passing ZIP | Isolate dependencies and audit in receiving base. Show the *actual* manuscript triple-pole or beta local table has distinct nodes modulo q and matches donor coefficient map; no actual family determinant valuation follows automatically |
| **P2** | **6.10** corrected height/decay-rate direction | `Zeta5Merge.Theorem6_10.height_decay_ratio_gt_581_of_le_one_2500` and `lower_decay_bound_counterexample`; historically PASS | Import only if missing from existing `PotentialGap` and `Section4ManuscriptBridge`. The donor explicitly refutes an invalid implication from a **lower** bound on decay; energy constants still need original-family proof |
| **P2** | **6.18** finite dyadic quotient | `Zeta5Merge.Theorem6_18.shifted_quotient_zero`; historically PASS | Current main `LeanPaper.DyadicQuotientThreshold` already proves the actual 6n quotient disappearance; **compare, don't duplicate**. 2-adic integrality and odd-prime multiplier remain open |
| **P3** | **odd ζ and 4.5 research** | Independently compiled 127-module `ODD_ZETA_3X3` finite eta-to-zeta readouts; verified 28-module `OddZeta.ResidueMoments` gives strictly log-convex **residue correction** series | Neither is the manuscript Bose Hankel moment family or its `bζ(5)+aζ(3)` positive density. A new **data-identification theorem** would be required before transferring any inequality |

**Particular near-term leverage:** P0 6.16 and 6.17 are *already verified donor math* with simple Mathlib-only imports; 4.2's candidate `d0` wrapper actually compiled in the failed CI. The highest mathematical-impact but unverified donor is 5.1's actual double-integral construction. This is a **conditional ranking by source/code-repair size and gap alignment, not a promise of full theorem completion**.

## 3. CI failure triage: what actually broke

The [snditeration failed workflow job 121155588555](https://github.com/randogelist/snditeration/actions/runs/40188938699) reports **ten failed modules**, **not** ten disproved mathematical claims:

| Failing module | Specific first blockers in CI |
|---|---|
| `Section3.MatrixCurveJacobi` | Type mismatch near line 145 |
| `Section6.CoefficientGramGrowth` | `field_simp` made no progress, line 126 |
| `Section5.BeukersMomentSeries` | Positivity failure and type mismatch/unsolved goals, lines 47, 75, 80 |
| `Section3.LaplaceWeightDerivative` | Multiple tactic/type errors and unexpected `λ` tokens (37–108) |
| `Section3.ContinuousPencil` | Type mismatch near 130 |
| `Section3.ShiftedMomentPositivity` | Incorrect `ext` and simplification mismatch, lines 86 and 128 |
| `Section3.PrincipalCondensation` | Multiple rewrite/type mismatch and unsolved goals |
| `Section3.ChristoffelDarboux` | Multiple errors 103–350, including missing `Matrix.diagonal_mulVec` |
| `Section5.RationalIndependence` | Unknown `Matrix.isUnit_iff_isUnit_det.mp`, line 28; rewrite near 41 |
| `Section3.CauchyInterlacing` | Rewrite mismatch near 33 and type mismatch near 140 |

Compiled-in-failed-workflow modules `Section4.AlgebraicLattice` and `Section6.PotentialGap` are **not accepted** until their full closed dependency/axiom audit is rerun. In the default receiving repo, existing `LeanPaper.Section4AlgebraicLimsup`, `Section5DualSpectrum`, `PrincipalMinorRank`, `OddBetaValues` and finite-energy identities must be reused first.

## 4. Why some attractive donor families cannot be merged as closure

- **Different ζ(5) determinant families:** reviewed manuscript `(K,N,h)=(30n,3n,27n)`; Fauzan-type upstream `(40n,3n,37n)`; native search package `(7n,n,6n)`. Uploaded `zeta5-spectral-lean` contains `Merge.ParameterBoundary.no_positive_common_reindex` for the first two. A theorem about one family **does not** supply the other family's multiplier, Gram rate or spectral norm.
- **External headline axiom:** imported full `Zeta5` endpoint relies on original PNT axiom and lacks full 4.33 kernel replay. Only its **explicit historical passing, axiom-free donor subset** is eligible for isolated intake. No unconditional ζ(5) irrationality is credited from the imported headline.
- **Odd ζ 3×3 IMPACTG**: finite exact rational matrices and eta/zeta readout convergence are real Lean results; the required reduced-denominator-weighted error `q_n(ζ(s)-p_n/q_n)→0` remains unproved. No determinant identity with the manuscript Hankel family has been supplied.
- **Chebyshev weight-seven:** `CHEBYSHEV_MASTERTIER_LEAN_v0_1_56_NATIVE_ZETA7_FAST_FRONTIER` reports a native-pass lock and eta readout but leaves four native ζ(7) endpoint modules **pending**; it is research/control, not the Beukers two-variable measure.
- **GP7:** eight frozen representative modules have prior native user-pass evidence, but the native `riemannZeta 7` identity, infinite resolvent and derivative ladder are open. Do not infer 5.1/5.2.
- **Witness frontier / RH / Chebyshev / ζ(3):** finite witness calibration or proof reductions do not assert a concrete witness passing a terminating checker and do not close manuscript equations unless a verified exact transport is constructed.
- **Older GOODWORKFLOWFRONTIER ZIPs** often correspond to mathematical ancestors of the 219-module accepted `main`, while some latest source patches say `PENDING_NATIVE_VERIFICATION`. Deduplicate by **source SHA and exact theorem statement** before adding or replacing code.

## 5. Collection and safe merge sequence

**Companion conversation artifact:** `GOODWORKFLOWFRONTIER_CROSS_PROJECT_INTAKE_v0_1_0_construction.zip`. It contains **10 unchanged Lean files from uploaded donor archives**, a machine-readable source-SHA/proof-receipt manifest, source-specific historical PASS evidence, and a single Windows `run.cmd` that performs **static SHA-256 checks only**. It deliberately does not compile Lean, import the failing GitHub branch or modify the receiving project.

1. **Stage 0 — independent donor replay:** add a **new source-only GitHub feature branch** based on the frozen receiving `main`; import first the standalone verified 6.16/6.17/6.10 helpers in their donor namespaces, with no changes to previously accepted files. Verify actual source SHA and Lean 4.33 cached Mathlib imports. Print axioms on each exported theorem and conduct an independent transitive dependency audit. Maintain `PASS-ONCE`.
2. **Stage 1 — direct manuscript bridges:** implement `6.17` corrected q-window on actual beta polynomial rows; identify the actual `6.16` compact ratio at both endpoints; isolate the compiled-only `4.2` lattice wrapper for receiving CI. Separate `StatementExists` from `ProofComplete`.
3. **Stage 2 — analytic dependency repair:** fix `ShiftedMomentPositivity` once, compile its Carleman/mixed-two descendants; independently repair Cauchy interlacing and the Beukers moment series. These can promote exact subclauses but do not yet prove all mixed minors or an infinite Krein decomposition.
4. **Stage 3 — quantitative frontier:** repair coefficient Gram growth's lone failure; establish the **actual** coefficient bound before comparing to `6.10`. Construct actual-family uniform quadratic decay and spectral rates for `4.4`; **no imported alternate-family estimate** is accepted here without exact determinant equivalence.
5. **Stage 4 — accepted merge:** only after successful pinned-compiler CI, full transitive axiom gate (no `sorryAx`, `admit`, custom mathematical axioms or circular proof field), checked original-PDF quantifiers and actual-data identity, deduplication and branch review, merge the qualified modules into `main`. Re-evaluate the 45-item ledger at the **whole printed statement** level.

## 6. Quantitative success criteria

Record separately: **(a)** historical source PASS, **(b)** receiving branch COMPILED, **(c)** full independent AXIOM CLEAN, **(d)** source mathematically connected to the original data, and **(e)** full literal manuscript clause discharged. A paper item moves to `!!` only when every exact printed subclaim is formally proved (or the published claim is explicitly corrected and separately labeled, leaving the literal blocked).

**No newly merged proof / no 45-item promotion is claimed in this source-intake report.** The reinference is *not* saturated: credible previously uncollected donor modules and exact code-repair targets have been identified.

## 7. Accepted intake merge ledger — 26 October 2026

**Historical note:** Sections 1–6 above preserve the original pre-merge collection assessment. The following is a later verified GitHub state, not a retroactive claim that these sources were merged when the intake began.

| Target | PR | Main merge SHA | Proof evidence | Exact scope |
|---|---|---|---|---|
| **6.17** corrected q-index windows | [#2](https://github.com/randogelist/zetahyperbolic-axiom/pull/2) | [cb1abbe85](https://github.com/randogelist/zetahyperbolic-axiom/commit/cb1abbe85bb277c823f31468142f7fdae8d0e9ba) | [220-module PR CI PASS](https://github.com/randogelist/zetahyperbolic-axiom/actions/runs/40260089735), `AUDITED_AXIOMS=[Quot.sound, Classical.choice, propext]` | Finite prime denominator windows only; not q-adic determinant valuation |
| **6.16** compact positive-ratio comparison | [#3](https://github.com/randogelist/zetahyperbolic-axiom/pull/3) | [c390e38c](https://github.com/randogelist/zetahyperbolic-axiom/commit/c390e38cc9b8f56c7c4446882984f19a5a90e550) | [221-module combined PR CI PASS](https://github.com/randogelist/zetahyperbolic-axiom/actions/runs/40262637451) | Abstract continuous positive ratio on compactified [0,1]; actual Zeta–Beta ratio not identified |
| **4.2** arbitrary `d0` algebraic lattice | [#4](https://github.com/randogelist/zetahyperbolic-axiom/pull/4) | [54136b39](https://github.com/randogelist/zetahyperbolic-axiom/commit/54136b39ec280b200c108ee48e80a5c247b1fa6b) | [222-module source-identical preflight PASS](https://github.com/randogelist/zetahyperbolic-axiom/actions/runs/40264760621) and full independent axiom audit; the preflight and merged PR had byte-identical 222 `.lean` sources and exact build manifests | Conditional algebraic-height/degree/decay/root-separation transfer only |
| **6.10** coefficient-Gram growth | [#5 (draft)](https://github.com/randogelist/zetahyperbolic-axiom/pull/5) | **NOT MERGED** | Reconciled PR head `262dda91157c8b3cf650a5917068a0b11ed21df6`; [fresh combined 223-module CI](https://github.com/randogelist/zetahyperbolic-axiom/actions/runs/40267337819) **in progress at this checkpoint** | Candidate `log det(CCᵀ)/K² → 0` under explicit rank and entry-growth hypotheses; not yet compiler accepted |

**Verified current `main`:** `54136b39ec280b200c108ee48e80a5c247b1fa6b`, registered module count **222**. Sources from #2, #3 and #4 are each present once. The manuscript literal full-item count is unchanged at **7/45**, despite these additional accepted narrow conditional or finite arithmetic lemmas.

**Next single target:** #5 only. The repair source in its branch is the exact byte-verified Git blob `b58764606ad898f27236c293245bfb54365192cf`, taken from the isolated [repair branch #8](https://github.com/randogelist/zetahyperbolic-axiom/pull/8). The auxiliary repair PR must **not** merge to main; PR #5 has the repaired source already. The 223-module axiom-audited CI must finish successfully on its reconciled head before #5 can merge.

**Additional future target drafts** remain independent in GitHub and receive no theorem credit or queue-jump merely by existing.

## Queued 3.3 Carleman factorial criterion (frozen new target)

- **One target/one source:** [draft PR #16](https://github.com/randogelist/zetahyperbolic-axiom/pull/16), branch `feat/gwf-target-33-carleman-factorial-criterion-v0_1_0`, frozen name `ZETA_HYPERBOLIC_TARGET_3_3_CARLEMAN_FACTORIAL_1`; source [`LeanPaper.CarlemanFactorialCriterion`](https://github.com/randogelist/zetahyperbolic-axiom/blob/feat/gwf-target-33-carleman-factorial-criterion-v0_1_0/src/LeanPaper/CarlemanFactorialCriterion.lean), Git blob `5460760348493a71d7fe471a3ec2d0c1ab881d33`.
- **Donor:** `snditeration/Section3/CarlemanDivergence.lean@0cee4ea`. Its factorial majorant theorem body is preserved. Because the original donor's actual-measure dependency was not compiled, this PR creates an **abstract conditional criterion** for a positive moment sequence with factorial upper growth; it **does not** claim the moment bound or Stieltjes determinacy for the actual manuscript data.
- **Baseline/verification:** added one source and registered the exact **223-module** receiving project against accepted `main@54136b39ec280b200c108ee48e80a5c247b1fa6b`. CI run [40268735312](https://github.com/randogelist/zetahyperbolic-axiom/actions/runs/40268735312) was triggered and **must** pass the full transitive axiom gate before any local A-Tier result. The 222 accepted mathematical module sources are frozen.
- **Queue rule:** prior [PR #5](https://github.com/randogelist/zetahyperbolic-axiom/pull/5) is still ahead and awaiting its combined verification; #16 must remain draft pending its own 223-module CI and any subsequent **fresh combined** build after #5 or other accepted main changes. Do not silently promote original 3.3, 6.10, RH or any odd-zeta irrationality result. **7/45** complete literal paper results remains the status.
