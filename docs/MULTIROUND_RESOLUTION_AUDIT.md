# Multi-round cross-branch proof audit — 25 October 2026

**Scope:** original 52-page Zetahyperbolic manuscript; exact formalized claims in `randogelist/zetahyperbolic-axiom`, compared with `randogelist/snditeration` and archived staging sources. This is a **read-only proof-scope audit** of existing code and available receipts; **no newly compiled theorem** is claimed by the documentation update.

## 1. Established tierlist (governing all entries below)

| Marker | Established tier | Evidence gate |
|:--:|:--|:--|
| `!` | **B-Tier** | Derived on paper; reasoning has not passed the Lean kernel/axiom gate. |
| `!!` | **A-Tier** | The **exact Lean proposition** has compiled and its transitive axioms are audited, with no `sorryAx`, custom axioms, or silently added premises. A proved conditional implication does not prove its assumptions. |
| `!!!` | **Formal closure** | A-Tier conditional derivation reduces the **target** to finite terminating-checker witness admission, with an accepted witness not yet present. |
| `!!!!` | **S-Tier** | Finite raw witness data actually pass a terminating checker, with verified A-Tier transfer to the claimed conclusion. |

Partial/blocked/unformalized are **manuscript coverage labels**, not extra tiers. An item with A-Tier **subtheorems** may remain partial. A corrected A-Tier statement does not make a refuted literal printed statement A-Tier.

## 2. Complete numbered paper items already crossed off

`!!` complete, with original-paper statement checked: **2.2, 2.3, 2.4, 2.5, 3.1, 4.3, 5.4** — **7/45**. These are already accounted for in the latest [45-result ledger](formalization_status.json); that link is also available as [the active ledger](formalization_status.json).

**Additional separate foundation outside the 45-row metric:** **Definition 2.1** — actual order-s monomial/pole moment and Hankel pencil definitions, canonical rational-function realization and basic ζ evaluation are constructed, with certified [source](../src/Definition_2_1_Order_s_Rational_Moment_Functional.lean) and [rational-function extension](../src/LeanPaper/Section2MuLinear.lean). Do **not** count it as an eighth completed member of the frozen 45-result ledger.

## 3. Round 1 — baseline integrity, current main

| Evidence | Verified boundary |
|:--|:--|
| [`zetahyperbolic-axiom/main` commit 86ca99a](https://github.com/randogelist/zetahyperbolic-axiom/commit/86ca99a23d65cde4880a9005a49076c43e7bc968) | 219 active modules. |
| [GitHub Actions run 40188664869](https://github.com/randogelist/zetahyperbolic-axiom/actions/runs/40188664869) | Successful sequential build **and** transitive axiom gate. |
| [Acceptance receipt](../validation/linux/acceptance.json) | 3,135 project declarations, including 2,489 theorem declarations (generated/private included), and 83,815 visited dependency declarations. Only `propext`, `Quot.sound`, `Classical.choice` are allowed. |
| [Proof-integrity receipt](../validation/linux/proof_integrity.json) | Zero active placeholders or project-specific axioms. Conditional mathematical hypotheses still matter. Native Windows validation of this revision is not established. |

**Conclusion:** full-paper literal closure still open; the seven A-Tier completions and all other exact imported helpers are real certified mathematics, not just theorem-name placeholders.

## 4. Round 2 — Section 3 structural/spectral clause audit

| Paper item | Crossed-off proof component, **not** whole item unless stated | Status of remaining paper claim |
|:--|:--|:--|
| **3.2** | [`ContinuousGram.printed_pencil_degree_and_real_roots`](../src/LeanPaper/ContinuousGram.lean) and corrected all-s weight/odd-specialization are A-Tier. | Literal odd-weight normalization is false by factor π/2; **corrected-only A-Tier**, original **blocked**. |
| **3.3** | [`PoleWeightSigns.determinant_leading_sign`](../src/LeanPaper/PoleWeightSigns.lean); [`SlopeSignature.actual_normalized_signature_counts`](../src/LeanPaper/SlopeSignature.lean) are A-Tier. The exact weight-five primitive leading sign and root-side `⌊27n/2⌋`/`⌈27n/2⌉` counts passed independently in [`snditeration` PoleSigns](https://github.com/randogelist/snditeration/blob/c521749190cce9981b0f108a8edc8034420f6420/Zetahyperbolic/Section3/PoleSigns.lean) and [SpectralInertia](https://github.com/randogelist/snditeration/blob/c521749190cce9981b0f108a8edc8034420f6420/Zetahyperbolic/Section3/SpectralInertia.lean). | Mixed **nonprincipal** total positivity and Carleman uniqueness open; final primitive count bridge not recorded as complete in receiving repo. |
| **3.4** | [`PrincipalMinorRank.original_principal_degree_eq_rank`](../src/LeanPaper/PrincipalMinorRank.lean), [`DodgsonCondensation.manuscript_condensation`](../src/LeanPaper/DodgsonCondensation.lean), [real-rootedness](../src/LeanPaper/PrincipalMinorRealRoots.lean) are locally A-Tier. | Rank-aware compatible Cauchy interlacing remains open. Printed all-`r` enumeration is false when slope rank drops. |
| **3.5** | [`JFractionActualObstruction`](../src/LeanPaper/JFractionActualObstruction.lean) proves the rank-one normalization error and a valid correction. Earlier normalized 2-3-step Schur identities are also [present](../src/LeanPaper/ImportedSection3/NormalizedContinuedFraction.lean). | Universal corrected cyclic Lanczos fraction, determinants' scale factor and exponential spectral edge still open; **literal original blocked**. |
| **3.6** | [`CorrectedReciprocalCorollary.corrected_corollary_3_6`](../src/LeanPaper/CorrectedReciprocalCorollary.lean), [all-order log jets](../src/LeanPaper/ReciprocalAllOrders.lean), [finite-support rank](../src/LeanPaper/ReciprocalRootMoments.lean), and [nearest-root limit](../src/LeanPaper/ReciprocalNearestRootLimit.lean) locally A-Tier. | **Complete corrected finite-family** item, but original all-order strict Hankel positivity and its erroneous inequality/sign conventions remain blocked; uniform cross-`K` edge estimates separate. |
| **3.7** | [`ActualStrictNewton.actual_centered_newton_strict`](../src/LeanPaper/ActualStrictNewton.lean) proves all normalized centered strict inequalities (assuming the actual admissible parameters and h≥2). [`HigherDerivativeTuran.actual_primitive_all_derivative_turan`](../src/LeanPaper/HigherDerivativeTuran.lean) proves actual all-derivative Turán. **`HasDistinctRoots` in the imported file means existence of at least two *different* roots; it does not assert pairwise simplicity.** | Paper's additional assertion of **individual coefficient nonvanishing** remains unproved; cannot cross off that statement merely from strict normalized inequalities. |
| **3.8** | [finite signed pole characteristic polynomial](../src/LeanPaper/ImportedSection3/ActualPoleKernel.lean) and [finite Jacobi determinant identity](../src/LeanPaper/ImportedSection3/Jacobi.lean) are A-Tier. | Actual orthogonal-polynomial Christoffel–Darboux expansion and derivative-under-integral Laplace bridge open. |
| **3.9** | [positive Fekete kernels](../src/LeanPaper/ImportedCharacter/CharacterPositive.lean) and [shifted-pole finite spectrum](../src/LeanPaper/ImportedCharacter/ShiftedPole.lean) are A-Tier. | Actual Hurwitz/Dirichlet analytic moment and pole-integral functionals remain unidentified. |

**Round 2 result:** substantial previously completed subclauses can be struck through; **no new complete original item** can be promoted.

## 5. Round 3 — arithmetic/Diophantine scope and exact rate audit

| Paper item | Certified already | Still open |
|:--|:--|:--|
| **4.1** | [`Section4TransferComplete.spectral_transfer_lattice`](../src/LeanPaper/Section4TransferComplete.lean): arbitrary-grid **eventual** real-exponent criterion. [`Section4EffectiveBudget.effective_spectral_measure`](../src/LeanPaper/Section4EffectiveBudget.lean): explicit integer threshold **if effective input onset/rates are supplied**. | The printed bare “sufficiently large `K`” premises do not yield a computable onset. Actual ζ(5) family rates do not follow. |
| **4.2** | [`Section4Resultant.integer_resultant_product`](../src/LeanPaper/Section4Resultant.lean); [`Section4AlgebraicLimsup.algebraic_transfer_limsup`](../src/LeanPaper/Section4AlgebraicLimsup.lean) gives a genuine degree-`d` algebraic-root approximation bound with its **finite upper limsup height** hypothesis (all-natural-index family). This is **stronger source coverage than a generic resultant lemma**. | The literal Proposition 4.2 is formulated for `K∈d₀ℕ`, not an all-natural-index sequence. An exact lattice reindexing/height and algebraic-minimal-polynomial equivalence should be compiled/audited before promoting the **whole printed** item. |
| **4.4** | [`Section4EffectiveBudget.manuscript_effective_rate_margins`](../src/LeanPaper/Section4EffectiveBudget.lean) proves the **specific rational comparisons** among `9/10`, `1/2500`, `11.411`, `2251`, `25687`. [exact disk](../src/LeanPaper/OperatorNormDisk.lean) is A-Tier. | No verification of `Q_K` actual p-adic multiplier, `exp(-K²/2500)` determinant decay or `‖B_K‖≤exp(11.411K)` for manuscript `K=30n`. Numerical comparison by itself is not ζ(5) irrationality. |
| **4.5–4.6** | Finite coupled shift and leading-coefficient/determinant-barrier algebra in [bridge](../src/LeanPaper/Section4ManuscriptBridge.lean). | Uniform actual-family multiplier, rates, heights; 4.6 proof uses an unjustified reversed inequality for `A_M`. |
| **4.7–4.8** | [finite cluster fraction implication](../src/LeanPaper/Section4ManuscriptBridge.lean), [conditional factor distance inequality](../src/LeanPaper/ImportedSection4/Proposition_4_8_Factor_Distance_Bounds.lean). | Specific norm/average/height bounds and unconditional rational-root exclusion; the printed 4.8 argument reverses a root-distance inequality. |

**Round 3 result:** **4.2's limsup component** and **4.4's numerical-rate margin** are newly explicit crossed-off steps. No numerical rate for the actual paper family has been certified.

## 6. Round 4 — ζ(7), β and multiweight proof boundaries

| Item | Certified (subclaim only) | Boundary |
|:--|:--|:--|
| **5.2** | [`Section5DualSpectrum.actual_dual_zeros_real`](../src/LeanPaper/Section5DualSpectrum.lean): actual finite rational coefficient pencil has real complex zeros under row-separation. [`KreinDimensionObstruction.fixed_K_two_h_two_impossible`](../src/LeanPaper/KreinDimensionObstruction.lean) proves the fixed-`K` dimension obstruction. | Infinite Beukers Krein/tail-controlled cones still open. |
| **5.6** | [`PaperChain.stage09_weight7_rational_signs`](../src/PaperChain/Stage09.lean) merely proves positivity of `453803/288000` and a second **rational sign**. | **Not** a proof that the manuscript's floor-function integral equals this fraction. Full outer-integral computation, corrected inner valuation and tail bounds remain open. |
| **6.2** | [`BeukersDenominator.dualConstant_seven_denominator`](../src/LeanPaper/BeukersDenominator.lean) proves exact finite arithmetic denominator clearance; adjacent rational moments also proved. | Real double-integral representation not established. |
| **6.4** | [`Section6BetaFinite.PAPER10_BETA_VANDERMONDE_RESIDUAL_SIGN`](../src/LeanPaper/Section6BetaFinite.lean) and oriented finite positive models are A-Tier. | Actual analytic β measure and q-adic determinant nonvanishing need proof; raw orientation is `(-1)^N`. |
| **6.6** | [anchored finite multiweight cone](../src/LeanPaper/ImportedMultiweight/AnchoredSemidefiniteCone.lean) and [finite spectral hyperbolicity](../src/LeanPaper/ImportedMultiweight/FiniteMultiweightCone.lean) proven. | No actual infinite multiweight density/arithmetic asymptotics. |
| **6.9** | [`TriplePoleHermite.hermite_congruence`](../src/LeanPaper/ImportedSection56/TriplePoleHermite.lean) and corrected finite Hermite block algebra. | Uses a **corrected kernel**; actual manuscript's local Laurent coefficients, invertibility and q-adic valuations not thereby established. |
| **6.10** | [finite determinant spectral identity](../src/LeanPaper/ImportedSection56/FiniteDeterminant.lean). | Infinite-family potential growth/gap and limiting equilibrium not yet proved. |
| **6.11** | [`DyadicQuotientThreshold.odd_square_scaling`](../src/LeanPaper/DyadicQuotientThreshold.lean) and [`consecutive_product_even`](../src/LeanPaper/DyadicQuotientThreshold.lean) are A-Tier **finite arithmetic identities**. | Euler distributions, prime sums/limits and 2-adic family growth still open. This is *not* a full-formalization promotion. |
| **6.13** | [`CentralFactorialSecant.central_secant_positive`](../src/LeanPaper/CentralFactorialSecant.lean) and [finite reversed-sign correction](../src/LeanPaper/CentralFactorialSecant.lean), plus [explicit exponential envelope](../src/LeanPaper/CentralFactorialDecay.lean). | Corrected infinite differentiated secant-series convergence and actual beta-pencil transfer absent; literal printed series formula has a sign error. |
| **6.15** | [`OddBetaValues.betaOdd_transcendental`](../src/LeanPaper/OddBetaValues.lean) and [`betaOdd_linearIndependent`](../src/LeanPaper/OddBetaValues.lean) are **unconditional A-Tier** for actual ordered odd β series. | These are *independent complete subresults*, not printed 6.15's effective fixed-degree measure or incorrect exterior asymptotic. |
| **6.17** | [`BetaHarmonicIndexObstruction`](../src/LeanPaper/BetaHarmonicIndexObstruction.lean) gives exact rational counterexamples to printed local valuation proof steps (including the permitted q=11 and 41 cases). | Recompute pole residues/local block; diagnosis alone does not disprove a separately conditional main statement. |
| **6.18** | [`DyadicQuotientThreshold.weight_five_six_n_quotient_zero`](../src/LeanPaper/DyadicQuotientThreshold.lean) and degree thresholds A-Tier. | Full dyadic residue integrality, odd-prime multiplier and irrationality exponent remain open. |

**Round 4 result:** added explicit crossed-off minor components for **5.6 (rational sign only)** and **6.11 (two elementary identities)**; all quantitative and infinite-dimensional endpoints retain their unproved status.

## 7. Round 5 — branch/receipt comparison and rejected promotions

- [`zetahyperbolic-axiom/main`](https://github.com/randogelist/zetahyperbolic-axiom/tree/main): [successful CI](https://github.com/randogelist/zetahyperbolic-axiom/actions/runs/40188664869); authoritative current proof.
- [`leaned-paper`](https://github.com/randogelist/zetahyperbolic-axiom/tree/leaned-paper): predecessor 166-module revision, [successful CI](https://github.com/randogelist/zetahyperbolic-axiom/actions/runs/40181021829); absorbed by newer main.
- [`feat/leaned-paper-source-assembly-v0_1_0`](https://github.com/randogelist/zetahyperbolic-axiom/tree/feat/leaned-paper-source-assembly-v0_1_0): old passing source base, not a new mathematical extension over main.
- [`continuation-in-progress`](https://github.com/randogelist/zetahyperbolic-axiom/tree/continuation-in-progress): `CONTINUATION_CHECKPOINT.json` explicitly says **IN_PROGRESS_NOT_VERIFIED_BUILD**. Its extra `Section2LagrangeFormula.lean` provides a plausible finite polynomial spelling, but it has **no accepted new CI receipt**; not crossed off.
- [`snditeration/main`](https://github.com/randogelist/snditeration/tree/main): [CI success](https://github.com/randogelist/snditeration/actions/runs/40186793090), 846 audited theorem declarations. Its actual weight-five primitive leading sign and root-side multiplicity counts legitimately close those **external subclauses**. They are *not silently imported into the receiving project*.
- [`snditeration/feat/zetahyperbolic-continuation-20261025`](https://github.com/randogelist/snditeration/tree/feat/zetahyperbolic-continuation-20261025): [CI failed](https://github.com/randogelist/snditeration/actions/runs/40188938699); expanded files named `CauchyInterlacing`, `CarlemanDivergence`, `ChristoffelDarboux`, `BeukersMomentSeries` and others are **candidate construction only**. This failure forbids A-Tier promotion regardless of names.
- Historical manuscript ZIPs and stage files (e.g., finite rational checks such as `PaperChain.stage09_weight7_rational_signs`) are not proof of missing analytic/valuation assertions. Freeze PASS-ONCE modules and cite exact source hashes, not archive names.

## 8. Round 6 — stop rule and next crossing threshold

**Stop:** After full-item review, current main theorem-signature audit, external-branch CI review, and manuscript-error analysis, **no further whole printed theorem beyond the seven qualifies as newly resolved under the established A-Tier gate**. Do not falsely “cross out” original 3.2/3.4/3.5/3.6/6.3/6.13/6.15; they require correction of the mathematical specification, not more Lean tactics against the false printed text.

The most efficient *genuinely new* theorem completions to target are:
1. Complete **3.3(1)** mixed-minor positivity + Carleman. Combine with already proved sign/inertia and exact external weight-five counts.
2. Build **rank-aware 3.4 Cauchy interlacing**, transporting all-rank existing Dodgson and singular-slope root counts.
3. Complete **3.8** actual orthogonal polynomial / dominated-derivative identity and **3.9** true character/Hurwitz measures.
4. For **4.1/4.2**, compile the exact effective-onset and `d0`-lattice equivalences (rather than declaring full printed scope from a stronger, differently indexed source).
5. For **4.4**, prove the missing actual-family rate estimates; comparison inequalities have already been discharged.
6. For **5–6**, prove true infinite two-variable moments/tail estimates and local p/q-adic valuations; replace false positive-cone claims and erroneous pole classifications.

Each new crossing requires **the exact theorem**, **same mathematical data**, **passing Lean build**, **independent full transitive axiom audit**, **source/Mathlib SHA**, and **proof dependencies from the claimed hypotheses to the original paper clause**. Work on this tracker is documentation; `main` was not modified.
