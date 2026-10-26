# Multi-round cross-branch proof audit — 25–26 October 2026

**Audit chronology:** Rounds 1–6 completed on 25 October 2026; additional source/PDF/branch rounds 7–12 completed on 26 October 2026. This review uses the same frozen successful compiler receipts and **does not claim a new Lean build**.

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


## 9. Round 7 — literal PDF clauses versus exact source signatures

This pass compared the supplied **52-page manuscript** directly against the checked theorem signatures, not just file titles:

- **3.4(2) fully resolved as its own clause:** [`LeanPaper.DodgsonCondensation.manuscript_at_minor_root`](../src/LeanPaper/DodgsonCondensation.lean) proves the exact signed-square Jacobi evaluation and `≤ 0`, for the actual manuscript pencil and arbitrary embedded principal blocks. The general determinant condensation formula is also proved. Original **3.4(1)** is still blocked by the universal rank-`r` root enumeration and missing rank-compatible interlacing.
- **3.7(1) is resolved:** [`actual_primitive_all_derivative_turan`](../src/LeanPaper/HigherDerivativeTuran.lean) and [`actual_primitive_all_derivative_turan_strict`](../src/LeanPaper/HigherDerivativeTuran.lean) prove every derivative Turán inequality and strictness off derivative zeros. [`theorem_3_7_strict_center`](../src/LeanPaper/ActualStrictCenter.lean) proves the precise strict center bound. **3.7(2) is resolved** by [`actual_coefficient_strict_criterion`](../src/LeanPaper/ActualStrictNewton.lean), with the actual coefficient zero/nonzero equality cases. For **3.7(3)**, [`actual_centered_newton_strict`](../src/LeanPaper/ActualStrictNewton.lean) proves the full centered strict normalized inequality; the manuscript additionally asserts **every individual** centered coefficient is nonzero, which the source does not prove. The symbol `HasDistinctRoots` in these source modules means at least two *different* roots, not pairwise simple roots. Do not credit that missing nonvanishing clause.
- **5.2(1) is resolved as a finite clause:** [`Section5DualSpectrum.actual_dual_degree`](../src/LeanPaper/Section5DualSpectrum.lean) and [`actual_dual_zeros_real`](../src/LeanPaper/Section5DualSpectrum.lean) work on the paper's exact **rational** `Real.dualDelta`, with `coefficientRowsSeparate` equivalent to the stated independent coefficient rows. The infinite signed-integral decomposition **5.2(2)** and tail-controlled polynomial cones **5.2(3)** are still missing.
- **6.15(1), two independent subclaims resolved:** [`OddBetaValues.betaOdd_transcendental`](../src/LeanPaper/OddBetaValues.lean) and [`betaOdd_linearIndependent`](../src/LeanPaper/OddBetaValues.lean) prove the actual ordered beta series are transcendental and each finite family, together with 1, is rationally linearly independent. The printed **effective irrationality-measure** clause of 6.15(1) remains open; 6.15(2)'s positive measure and exterior asymptotic remain open/incorrect respectively.

**Round 7 receipt:** crossed **3.4(2), 3.7(1)–(2) and centered strict inequality, 5.2(1), and the first two arithmetic claims of 6.15(1)**. None of these promotes an entire additional item to complete; each parent's remaining clause is real.

## 10. Round 8 — exact `K=30n` primitive ζ(5) family, degree, positivity

The original Theorem 4.4 uses `K=30n,N=3n,h=27n,m=3,k=2` and a primitive integer polynomial. [`MAIN_CHAIN_IRRATIONALITY.lean`](../src/MAIN_CHAIN_IRRATIONALITY.lean) contains the **exactly matched** family

```lean
def affineFamily (k n : ℕ) : Real.Parameters :=
  ⟨k, 3, 3 * (n + 1), 30 * (n + 1)⟩
```

so `affineFamily 2 n` runs through the manuscript's positive-index weight-five family, merely reindexed by `n+1`. The source proves:

1. **Fully crossed off:** [`primitivePolynomial_isPrimitive`](../src/MAIN_CHAIN_IRRATIONALITY.lean), [`primitivePolynomial_eval`](../src/MAIN_CHAIN_IRRATIONALITY.lean), [`primitivePolynomial_natDegree`](../src/MAIN_CHAIN_IRRATIONALITY.lean), [`primitivePolynomial_eval_pos`](../src/MAIN_CHAIN_IRRATIONALITY.lean) and `affineFamily_admissible`, `affineFamily_h`, `affineFamily_unbounded`. Thus integer primitiveness, exact `h=27(n+1)` degree, actual zeta(5) center positivity/nonvanishing and unbounded admissible indices are already Lean-proved. Calling the *existence of a primitive integer normalization* an open obstacle is too broad; only the **effective arithmetic multiplier/height growth** and **decay** remain open.
2. [`PaperChain.Stage05RateGapBridge.stage05_original_primitive_gap_identity`](../src/PaperChain/Stage05RateGapBridge.lean) proves the **exact finite leading-size × determinant-ratio identity**, while `stage05_original_determinant_ratio_pos` proves positivity. [`stage05_zeta5_irrational_if_leading_ratio_gap`](../src/PaperChain/Stage05RateGapBridge.lean) proves **a conditional** `Irrational (Real.zeta 5)` from explicit uniform leading and determinant log-rate hypotheses. It does **not** discharge either hypothesis.
3. [`Section4EffectiveBudget.manuscript_effective_rate_margins`](../src/LeanPaper/Section4EffectiveBudget.lean) settles the *arithmetic comparisons of constants*, not the analytic rates.

**Still open:** actual prime/determinant multiplier size, the required `exp(-K²/2500)` bound, `‖B_K‖ ≤ exp(11.411K)` and effective onset; without them **Theorem 4.4 remains partial**. A conditional `irrational_zeta...` theorem in the repo is a valid A-Tier implication, **never** an unconditional zeta result.

## 11. Round 9 — a genuine ζ(7) inequality and negative dual direction

[`ImportedSection56/ZetaSevenBound.lean`](../src/LeanPaper/ImportedSection56/ZetaSevenBound.lean) contains the following **unconditional, kernel-audited** actual-value results:

- `zetaSeven_tail_le_one_div_64`: an explicitly proved tail bound for `Σ_{n≥2}n⁻⁷`.
- `zetaSeven_lt_38_div_37`: `Real.zeta 7 < 38/37`.
- `weightSeven_rankOne_negative_unconditional`: an **actual weight-seven rational dual determinant** is strictly negative at the true `Real.zeta 7`.

These are more than generic finite matrix algebra, and should be marked crossed off as actual analytic/finite-sign components of **5.2**. They do **not** prove the *arbitrary-`h` infinite positive and negative Krein subspaces* or the two-variable Beukers integral identity, and therefore do not make 5.2 a complete printed theorem.

## 12. Round 10 — actual finite energy, content/Gram identity and adjacent drift

Already audited and now explicitly crossed off as **actual manuscript-family** finite identities:

- [`FiniteEnergy.finite_potential_conservation`](../src/Theorem_4_1_Determinant_Log_Energy.lean): `leadingLog + valueDecayLog = determinantEnergy` **for every admissible parameter tuple**, and `finite_potential_conservation_per_K_sq`: exact equality after division by `K²` for each finite `K`.
- [`Stage08FinitePotentialBridge.stage08_original_finite_potential_conservation_per_K_sq`](../src/PaperChain/Stage08FinitePotentialBridge.lean) explicitly transports the normalized identity to the original manuscript parameter wrapper.
- [`ContentGramCancellation.primitive_eval_log_eq_content_add_gram`](../src/Theorem_4_1_Content_Gram_Cancellation.lean) and [`Stage05ContentGramBridge.stage08_original_content_gram_energy_identity`](../src/PaperChain/Stage05ContentGramBridge.lean) give the exact content + Gram decomposition.
- [`AdjacentLogIncrement.affineEnergy_increment_eq_log_ratio`](../src/Theorem_4_1_Adjacent_Log_Increment.lean) and [`Stage05AdjacentDriftBridge.stage05_affine_original_adjacent_log_ratio`](../src/PaperChain/Stage05AdjacentDriftBridge.lean) give the **exact adjacent step** for the actual affine family.
- All four bridge families have separate conditional theorems `..._irrational_if_...`; these are genuine A-Tier **conditional implications**, not the yet-unproved uniform decay/gap premise.

Mark these finite **4.4/4.6/6.10** identities as resolved. **Theorem 6.10's quadratic limiting potential gap/derivative-growth asymptotics remain open**; an identity valid at each finite `K` cannot supply the sign of a `K→∞` limit.

## 13. Round 11 — finite arithmetic vs global claim, and counterexample scope

Reviewing actual source rather than module names:

- **5.6:** [`PaperChain.Stage09.stage09_weight7_rational_signs`](../src/PaperChain/Stage09.lean) proves numerical **signs of given rational numbers**, **not** the table's floor-piece integral `453803/288000`. Cross off the rational sign only.
- **6.2:** [`BeukersDenominator.dualConstant_seven_denominator`](../src/LeanPaper/BeukersDenominator.lean) proves the finite `6d_K^7` denominator. The two-variable integral to those rational moments remains open.
- **6.11/6.18:** [`DyadicQuotientThreshold`](../src/LeanPaper/DyadicQuotientThreshold.lean) settles the exact polynomial quotient cutoff and odd-square/parity identities, **not** the Euler distribution, 2-adic local residue valuation and effective dyadic multiplier.
- **6.3(2):** [the signed Beukers negative-cone counterexample](BEUKERS_POSITIVITY_COUNTEREXAMPLE.md) has exact rational arithmetic and a justified elementary analytic enclosure, but the **full counterexample certificate has not been compiled in Lean**. Thus the literal paper claim is blocked on mathematical grounds, without inventing a Lean theorem.
- **6.13:** [finite secant differential and sign-correction proof](../src/LeanPaper/CentralFactorialSecant.lean) is A-Tier; original infinite-series sign is wrong, and the corrected termwise differentiation/β-pencil transfer remains unproved.
- **6.15(2):** the published fixed-exterior `h^(-2k)` asymptotic factor conflicts with the Szegő regime for `k≥1`; the necessary analytic replacement itself is not a Lean-verified asymptotic.
- **6.17:** [`BetaHarmonicIndexObstruction`](../src/LeanPaper/BetaHarmonicIndexObstruction.lean) proves the **specific** `q=11` denominator and `q=41` leading-diagonal diagnostics; do not infer a general refutation of the separately conditional whole theorem.

## 14. Round 12 — branch acceptance and terminal reconciliation

Checked the following source heads against their actual build receipts:

| Branch / proof source | Exact status | Consequence for crossings |
|:--|:--|:--|
| [`zetahyperbolic-axiom/main@86ca99a`](https://github.com/randogelist/zetahyperbolic-axiom/commit/86ca99a23d65cde4880a9005a49076c43e7bc968) | [CI PASS 40188664869](https://github.com/randogelist/zetahyperbolic-axiom/actions/runs/40188664869): sequential Lean 4.33 build and independent transitive axiom check, 219 modules | A-Tier for exact compiled source signatures, not hypothetical printed scope |
| `zetahyperbolic-axiom/leaned-paper`, `feat/leaned-paper-source-assembly-v0_1_0` | Historical PASS, ancestor/reusable sources | No upgrade over the more complete current `main` |
| [`zetahyperbolic-axiom/continuation-in-progress`](https://github.com/randogelist/zetahyperbolic-axiom/tree/continuation-in-progress) | `CONTINUATION_CHECKPOINT.json` explicitly labels **IN_PROGRESS_NOT_VERIFIED_BUILD** | Its `Section2LagrangeFormula` and other candidates are **not** accepted new crossings |
| [`snditeration/main@c521749`](https://github.com/randogelist/snditeration/commit/c521749190cce9981b0f108a8edc8034420f6420) | [CI PASS 40186793090](https://github.com/randogelist/snditeration/actions/runs/40186793090), 846 audited theorem declarations (including generated ones) | Exact `3.3(2)` weight-five primitive sign and `3.3(3)` root-side count can be independently considered proved **externally**; receiving-project bridge still separate |
| [`snditeration` broad continuation](https://github.com/randogelist/snditeration/tree/feat/zetahyperbolic-continuation-20261025) | [CI FAILED 40188938699](https://github.com/randogelist/snditeration/actions/runs/40188938699) | No crossing from unaccepted `CarlemanDivergence`, `CauchyInterlacing`, `ChristoffelDarboux` etc. |

**This extended 12-round audit does not find an eighth manuscript item with a proven **complete literal** Lean statement.** Seven remain `!!` A-Tier complete. Numerous important *exact* subtheorems have been crossed off (including the real manuscript `K=30n` primitive integer family), while the remaining proof bridges, failed printed clauses and analytic/asymptotic endpoints are retained without inflation. No `!!!` / `!!!!` certificate is claimed.

**Subsequent audit policy:** New status promotions require a *new* successful proof receipt plus exact original-statement matching, not repeated reviews of the same unchanged accepted source.


## 15. Round 13 — source-membership, SHA and acceptance verification (26 October 2026)

The latest inspected repository heads remain frozen: [`zetahyperbolic-axiom/main@86ca99a`](https://github.com/randogelist/zetahyperbolic-axiom/commit/86ca99a23d65cde4880a9005a49076c43e7bc968) and [`snditeration/main@c521749`](https://github.com/randogelist/snditeration/commit/c521749190cce9981b0f108a8edc8034420f6420). The relevant GitHub Actions runs still show **PASS** for those exact heads; `snditeration/feat/zetahyperbolic-continuation-20261025` still reports **FAILED**, and `zetahyperbolic-axiom/continuation-in-progress` has no accepted new head receipt.

Rather than assuming a file's presence implies verification, I checked **all nine newly noticed proof modules** below against both [`modules.txt`](../modules.txt) and [`provenance/active_module_hashes.json`](../provenance/active_module_hashes.json). **All nine belong to the accepted 219-module source inventory and are covered by the same [successful CI compilation/transitive axiom gate](https://github.com/randogelist/zetahyperbolic-axiom/actions/runs/40188664869)**. Accepted modules:

- `LeanPaper.ImportedSection56.KreinIdentity`
- `LeanPaper.ImportedSection56.RankOneWitness`
- `LeanPaper.ImportedSection56.DualWeightInvariance`
- `LeanPaper.ImportedSection56.SelectedMonomial`
- `LeanPaper.ImportedSection56.UnimodularMonomial`
- `LeanPaper.BetaOneMoments`
- `LeanPaper.UnitLogMoments`
- `LeanPaper.SymmetricPoleSpectrum`
- `LeanPaper.ImportedCharacter.PositiveSlope`

This is **A-Tier evidence for exact theorem statements** and not evidence of new compiler runs or whole-paper closure. The receipt permits only `propext`, `Quot.sound` and `Classical.choice` as transitive axioms.

## 16. Round 14 — weight-independent and monic dual pencils (5.1–5.2)

The **actual rational** dual pencil is stronger than the previously noted finite `CCᵀ` identity:

- [`PaperOrder.CoreAlgebra.dualEntry_derivative_weight_independent`](../src/LeanPaper/ImportedSection56/DualWeightInvariance.lean) proves its entrywise `X`-derivative **does not depend on the weight `s`**. [`dualDelta_top_coefficient_weight_independent`](../src/LeanPaper/ImportedSection56/DualWeightInvariance.lean) proves the determinant's degree-`h` coefficient is weight-independent, **even for dependent coefficient rows** (when it may be zero). Both are crossed off.
- [`dualSelectedMonomialSlope_one`](../src/LeanPaper/ImportedSection56/SelectedMonomial.lean), [`dualSelectedMonomialDelta_monic`](../src/LeanPaper/ImportedSection56/SelectedMonomial.lean), and [`dualSelectedMonomialDelta_degree`](../src/LeanPaper/ImportedSection56/SelectedMonomial.lean) prove **exact leading coefficient 1 and degree `h`** when `h` distinct monomials are selected from `ℚ[x]≤K`, in any order.
- [`dualUnimodularSelectedMonomial_top_coeff`](../src/LeanPaper/ImportedSection56/UnimodularMonomial.lean) retains monicity under a rational row basis transform satisfying `det(A)^2=1`; [`dualUnimodularSelectedMonomial_degree`](../src/LeanPaper/ImportedSection56/UnimodularMonomial.lean) preserves full degree. The full-monomial family likewise has a monic determinant of degree `K+1`: [`dualFullMonomialDelta_degree`](../src/LeanPaper/ImportedSection56/FullMonomial.lean).

**Crossed:** actual derivative independence, actual selected-monomial monicity, exact full degree and unimodular stability. **Still missing:** identification with the genuine double-integral Beukers measure in 5.1, and infinite Krein cones in 5.2.

## 17. Round 15 — finite and summable infinite Krein polarization (5.2(2))

[`PaperOrder.PrincipalTheorems.weightSeven_Krein_bilinear`](../src/LeanPaper/ImportedSection56/KreinIdentity.lean) proves the **full six-channel bilinear identity** by pairing complementary logarithmic powers with exact factor `1/1440`. The source also proves:

- `weightSeven_Krein_quadratic`: exact positive-square-minus-negative-square polarization.
- `weightSeven_Krein_finite_modes`: summed identity for **every finite mode cutoff `M`**.
- `weightSeven_Krein_infinite_modes`: equality of the two infinite mode sums **when `Summable (fun m => weightSevenPairing (a m) (b m))` is provided**.

The infinite-sum theorem is valid A-Tier mathematics; its **summability hypothesis is a real hypothesis**, and the mode channels `a,b : ℕ→ℕ→ℝ` are abstract real sequences. It does **not** establish Fubini/Tonelli for `ψ_{m,ν}^{±}` built from an arbitrary `f∈L²(0,1)`, nor identify the left side with the true **`dΩ₇` double integral of paper equation (5.4)**.

**Crossed:** exact finite algebra, quadratic/bilinear polarization, and *conditional summable-series equality*. **Not crossed:** original analytic 5.2(2) whole clause or its all-`f` domain.

## 18. Round 16 — unconditional positive **and** negative rank-one ζ(7) witnesses (5.2(3))

The accepted files include **both signs**, not just the negative instance previously highlighted:

- [`negativeWeightSeven_actual_pencil`](../src/LeanPaper/ImportedSection56/RankOneWitness.lean): the exact polynomial for rational row `A(x)=1−6x` is **`37X−38`**, with exact rational root `38/37`.
- [`zetaSeven_lt_38_div_37`](../src/LeanPaper/ImportedSection56/ZetaSevenBound.lean) and [`weightSeven_rankOne_negative_unconditional`](../src/LeanPaper/ImportedSection56/ZetaSevenBound.lean): **`G_A(ζ(7))<0`**, no supplied ζ bound.
- [`positiveWeightSeven_actual_pencil`](../src/LeanPaper/ImportedSection56/RankOneWitness.lean): the rational constant row `A(x)=1` gives **`Δ_A(X)=X`**; [`positiveWeightSeven_at_zeta`](../src/LeanPaper/ImportedSection56/RankOneWitness.lean) proves **`G_A(ζ(7))>0`**.

For **`h=1, K≥1`**, these are explicit rational positive/negative **one-dimensional finite pencil instances**. They genuinely resolve that restricted case of the sign-choice construction in 5.2(3). They do **not** prove positive/negative rational subspaces of **arbitrary dimension `h`**, nor the untruncated infinite analytic Krein tail needed in the paper's general statement. The printed quantifier `K≥h` and its `M≥h` construction still require a rank/dimension repair at large `h`.

## 19. Round 17 — true Mellin integral and the special `k=0` β measure (5.1, 6.1–6.2, 6.15)

- [`LeanPaper.UnitLogMoments.integral_exp_neg_substitution`](../src/LeanPaper/UnitLogMoments.lean) proves the actual one-variable exponential change of variables, and [`integral_pow_log`](../src/LeanPaper/UnitLogMoments.lean) proves, with endpoints, `∫₀¹ u^a (−log u)^m du = m!/(a+1)^(m+1)`. [`integrable_pow_log`](../src/LeanPaper/UnitLogMoments.lean) proves integrability. These are important already completed **analytic primitives** for Sections 5–6, but not the paper's two-variable `dΩ₇` or its q-adic factorization.
- [`LeanPaper.BetaOneMoments.zeroth_moment`](../src/LeanPaper/BetaOneMoments.lean): **`∫₀¹ du/(1+u²)=π/4`**. [`first_moment`](../src/LeanPaper/BetaOneMoments.lean): **`∫₀¹ u du/(1+u²)=log(2)/2`**. Positivity of the actual density and first moment is proved.
- [`eta_at_one_needs_removable_value`](../src/LeanPaper/BetaOneMoments.lean) proves that replacing `η(1)=log 2` with the **totalized** product `(1−2^(1−1))ζ(1)` incorrectly gives zero, not the above positive first moment. This is a verified diagnostic of the manuscript's **`k=0` endpoint notation**, *not* a full refutation of all higher-`k` moments.

**Crossed:** exact one-variable Mellin/Gamma moments and the `k=0` density's first two integrals. **Still missing:** the fully identified `k≥0`, all-`r` β moments, strictly totally positive Hankel matrix and correct rank-one asymptotic in printed 6.15(2).

## 20. Round 18 — symmetric spectral equality and positive-character slope (3.8–3.9, 6.4)

- [`LeanPaper.SymmetricPoleSpectrum.actual_symmetric_charpoly_eq_pole`](../src/LeanPaper/SymmetricPoleSpectrum.lean) proves that the **actual symmetric whitened matrix** `B=G^(−1/2) M G^(−1/2)` has **the exact same characteristic polynomial** as the signed pole-kernel matrix; [`actual_symmetric_roots_eq_pole`](../src/LeanPaper/SymmetricPoleSpectrum.lean) transfers the entire root **multiset**, including algebraic multiplicities. This is a genuine completed component of **3.8(1)** beyond a mere abstract `G^-1 M` identity. Still missing: constructing the *monic orthogonal polynomials* and Christoffel–Darboux kernel from the actual measure, and 3.8(2)'s differentiated Laplace integral.
- [`LeanPaper.ImportedCharacter.PositiveSlope.poleM_posDef`](../src/LeanPaper/ImportedCharacter/PositiveSlope.lean) proves positive definiteness of `V diag(γ) Vᵀ` for **injective nodes and positive residues**, at **all finite dimensions**. [`shiftedSlope_posDef`](../src/LeanPaper/ImportedCharacter/PositiveSlope.lean) instantiates it at the positive shifted pole lattice. [`CharacterPositive.all_fekete_laplace_numerators_pos`](../src/LeanPaper/ImportedCharacter/CharacterPositive.lean) supplies positivity of the manuscript's five rational character numerators. These are already proved subcomponents of **3.9/6.4**. They do not construct the Hurwitz/Dirichlet **analytic moment functional**, hence do not close either whole theorem.
- Final provenance gate: the inspected new subproofs exist in the **accepted** 219-module manifest. The [`snditeration` broad continuation](https://github.com/randogelist/snditeration/tree/feat/zetahyperbolic-continuation-20261025) still has no passing CI for its novel files. No claim is upgraded by filename or by an unverified helper.

**Round 18 verdict:** **7/45 complete printed results remain the only entire-item `!!` claims**. Additional A-Tier subproofs crossed include **actual 5.2 weight-independent monicity, mode polarization under an explicit summability condition, h=1 genuine two-sign ζ(7) witnesses; actual `k=0` β integrals; the exact symmetric 3.8 pole-kernel spectrum and positive shifted-node slopes**. The substantial remaining Beukers infinite-tail, mixed-minor, arithmetic-rate, q-adic and corrected-claim obligations have not vanished.

A new complete-item status requires **fresh exact-proposition equivalence + a passing Lean/axiom audit**, not further reading of unchanged sources.


## 21. Round 19 — frozen source and transitive proof receipt reconciliation (26 October 2026)

Rechecked all branches and GitHub Actions. The accepted [`zetahyperbolic-axiom/main@86ca99a`](https://github.com/randogelist/zetahyperbolic-axiom/commit/86ca99a23d65cde4880a9005a49076c43e7bc968) and [`snditeration/main@c521749`](https://github.com/randogelist/snditeration/commit/c521749190cce9981b0f108a8edc8034420f6420) remain unchanged and have passing CI receipts. The 219 active modules were compiled in [Actions 40188664869](https://github.com/randogelist/zetahyperbolic-axiom/actions/runs/40188664869) using Lean 4.33.0 and pinned Mathlib `db584cd6d46c92f209a44c0f1c829460d327499d`. The full independent axiom gate passed with exactly the allowed foundations. No newly compiled code is claimed in this round.

The ten newly inspected modules listed below were all individually checked against the *exact* [219-line build plan](../modules.txt) and [accepted source hash inventory](../provenance/active_module_hashes.json): `ImportedSection56.DualNullspace`, `ImportedSection56.DualBasisCongruence`, `ImportedSection56.DualStrictDiscriminant`, `ImportedSection56.DualQuadraticRoot`, `ImportedSection3.NormalizedContinuedFraction`, `ImportedSection3.PowerSumExtrema`, `ProofAdvances.Corollary_3_6_ExactFiniteRank`, `ProofAdvances.Corollary_3_6_AllPrincipalMinors`, `Theorem_2_5_Weight_Change`, and `PaperChain.Stage07WeightShiftBridge`. Each module is therefore in the already accepted A-Tier import closure; the *meaning and premises* of its exact theorem still control the marking.

## 22. Round 20 — complete finite dual-Gram nullspace and change-of-basis laws (5.1–5.2)

- [`dualSlopeQuadraticForm_zero_iff`](../src/LeanPaper/ImportedSection56/DualNullspace.lean) proves **the exact nullspace equivalence** for a finite rational coefficient matrix `C`: `vᵀ(CCᵀ)v=0` iff every column sum `Σ_i v_i C_{ir}=0`. [`dualSlopeQuadraticForm_pos_iff_rowsSeparate`](../src/LeanPaper/ImportedSection56/DualNullspace.lean) proves strict positivity on all nonzero coefficient vectors **if and only if** rational row separation. This closes both directions of a genuine finite `5.2(1)` slope criterion, rather than assuming positivity.
- [`dualCoefficientMatrix_rowChange`](../src/LeanPaper/ImportedSection56/DualBasisCongruence.lean) proves the actual coefficient transform `C↦AC`. [`dualSlopeMatrix_rowChange`](../src/LeanPaper/ImportedSection56/DualBasisCongruence.lean) proves `CCᵀ↦A(CCᵀ)Aᵀ` for *every* rational square `A`. [`dualDelta_top_coeff_rowChange`](../src/LeanPaper/ImportedSection56/DualBasisCongruence.lean) proves top coefficient `c_h↦det(A)^2 c_h`; invertibility plus nonzero top coefficient preserves full degree.
- These laws improve the earlier proof map for **5.1/5.2** beyond the special monomial basis and its unimodular case. They do **not** establish the original *full polynomial determinant* basis-congruence at every `X` if not stated, nor any integral-defined Beukers identity.

**Crossed:** all-size exact finite Gram nullspace/row separation, slope congruence and top-coefficient transport. **Open:** two-variable analytic measure, summable *actual* infinite Krein modes, arbitrary-dimensional positive/negative cones.

## 23. Round 21 — normalized rank-two/rank-three continued fractions (3.5)

[The corrected normalization source](../src/LeanPaper/ImportedSection3/NormalizedContinuedFraction.lean) contains exact algebraic results at **two and three** successive Schur levels, not merely a scalar counterexample:

- `corollary_3_5_normalized_two_det` proves the determinant of `[[1+ta,tb],[tb,1+tc]]` equals its normalized continuant.
- `corollary_3_5_two_level_schur_identity` proves `(1+ta)(1+tc−(tb)^2/(1+ta))` equals the normalized determinant **provided `1+ta ≠ 0`**.
- `normalized_three_continuant_recurrence`, `normalized_three_continuant_eq_det` and `normalized_three_schur_identity` give the exact `3×3` tridiagonal determinant and its nested Schur fraction, with **both relevant intermediate denominators nonzero**.

These are A-Tier *generic finite identities* that discharge the low-rank normalized fraction algebra needed for the **corrected** Corollary 3.5. The paper's literal `a_j+t` / missing determinant-scale formula is **still false**. A general actual-family Lanczos tridiagonalization, cyclicity/no-breakdown theorem, complete `h`-step fraction and spectral-edge estimate remain open.

## 24. Round 22 — exact finite-support Hankel rank/positivity dichotomy (3.6)

Several A-Tier results resolve the sharp, **mathematically valid** replacement of the impossible printed all-orders strict Hankel assertion:

- [`weighted_hankel_posSemidef`](../src/ProofAdvances/Corollary_3_6_WeightedCorrected.lean): every finite order, nonnegative weights, arbitrary real atoms.
- [`weighted_det_pos_iff_order_le_support`](../src/ProofAdvances/Corollary_3_6_ExactFiniteRank.lean): **if the listed `h` atoms are pairwise distinct and the masses positive**, then **`det H_n > 0 ↔ n≤h`**. For `n>h` the determinant vanishes; these are exact Lean theorems, not numerical examples.
- [`weighted_all_principal_minors_nonnegative`](../src/ProofAdvances/Corollary_3_6_AllPrincipalMinors.lean): all principal subdeterminants are nonnegative **at any truncation order**, even under repeated selected indices.
- [`weighted_all_principal_minors_positive`](../src/ProofAdvances/Corollary_3_6_AllPrincipalMinors.lean): injectively chosen principal submatrices are strictly positive for `n≤h` under the **distinct-atom/positive-mass** conditions.
- [`actual_reciprocal_moment_bounds`](../src/LeanPaper/ImportedSection3/RootMomentBounds.lean) applies finite extremal power-sum bounds to the actual manuscript root vector, with multiplicities allowed.

**Crucial separation:** This is **3.6's finite atomic reciprocal-root moment family**, not **3.3(1)'s continuous positive density and *mixed nonprincipal* Hankel minors**. Roots symmetric around a rational center can have **coincident reciprocal-square atoms**; without proving distinctness, do not assert strict lower-order determinants for every actual shift. The corrected 3.6 proof remains complete at its own scope, but the false printed statement remains blocked.

## 25. Round 23 — all-weight rational pole-reweight laws (4.5, 4.6, Section 2)

For a **fixed** `m,N,K` and increased odd-zeta index `k→k+d`, [`Theorem_2_5_Weight_Change.lean`](../src/Theorem_2_5_Weight_Change.lean) proves

```text
w_a(k+d) = w_a(k) · a^(2d),
det M(k+d) = det M(k) · ∏_a a^(2d),
LC(Δ_{k+d}) = LC(Δ_k) · ∏_a a^(2d),
∏_a a^(2d) > 0.
```

The source also proves the **exact positive ratio of slope determinants**, and a cross-multiplication identity for arbitrary weights `k,l`. [`PaperChain.Stage07WeightShiftBridge.stage07_original_derivative_det_reweight`](../src/PaperChain/Stage07WeightShiftBridge.lean) transports this to the **original manuscript parameters**, with [positive weight factor](../src/PaperChain/Stage07WeightShiftBridge.lean) proved.

**Crossed:** rational finite pole-weight reweight, determinant and leading-coefficient transfer, positive factor, for every admissible finite family. **Still open:** the independent analytic positivity of the coupled `bζ(5)+aζ(3)` density, Loewner comparison, prime cancellation, uniform multiplier/height rates. A positive finite **determinant reweighting** is not positivity of an arbitrary coupled affine form.

## 26. Round 24 — two-dimensional strict dual spectrum and finite multiweight Turán (5.2, 6.6)

- [`dualTwoByTwo_discriminant_nonneg`](../src/LeanPaper/ImportedSection56/DualDiscriminant.lean) supplies a **sum-of-squares proof** of a nonnegative real discriminant for symmetric `2×2` pencils with positive-definite direction. [`dualTwoByTwo_det_has_real_zero`](../src/LeanPaper/ImportedSection56/DualQuadraticRoot.lean) constructs a real zero using that discriminant.
- [`dualTwoByTwo_discriminant_pos_of_nonproportional`](../src/LeanPaper/ImportedSection56/DualStrictDiscriminant.lean) proves **strict** positive discriminant if, in addition, `bu−av≠0`. This is a legitimate sufficient condition for distinct roots of this *two-dimensional matrix*, not a proof of universal simplicity for all actual dual determinants.
- [`FINITE_MULTIWEIGHT_SPECTRAL_HYPERBOLICITY`](../src/LeanPaper/ImportedMultiweight/FiniteMultiweightCone.lean) proves exact degree, real spectrum and Turán nonnegativity for **finite positive combinations of positive-definite real slope matrices** (with explicit positive weights and equality to the chosen pencil direction).
- [`FINITE_MULTIWEIGHT_STRICT_TURAN`](../src/LeanPaper/ImportedMultiweight/FiniteMultiweightCone.lean) adds strict Turán away from roots, under `n>0`, for the **same finite model**.

**Crossed:** rank-two real-root/conditional simplicity and all-dimensional finite multiweight hyperbolicity/strict Turán under exact stated assumptions. **Open:** the actual infinite multiweight `ζ/β` density, signed measures, q-adic multiplier and uniform asymptotic claims from Sections 6.6–6.18.

## 27. Round 25 — manuscript-wide scope check and promotion threshold

- Inspected both repositories' **current** head SHAs, recent Actions conclusions, the full accepted module plan, source hash inventory, and the actual signatures and proof bodies above. No new accepted `main` Lean commit was found; the broad `snditeration` continuation remains CI-failing.
- The newly identified **exact proofs** above are all already present in the previously passing **219-module, axiom-audited main**. These may be crossed from *remaining subproof work*, but their successful compilation is **reused historical evidence**, not a new compilation.
- No additional literal printed item joins the seven fully proved results: `2.2, 2.3, 2.4, 2.5, 3.1, 4.3, 5.4`. Section 3's total positivity/Carleman, interlacing and full continued fraction, Sections 4's concrete rate/prime bounds, and Sections 5–6's true two-variable measures, infinite Krein cones and valuation estimates **remain mathematically open** (or require a corrected printed specification).
- A subsequent crossing to **whole-item `!!`** requires a checked original-clause identity, correct data/quantifiers, and a *new successful* compiler/axiom receipt for any newly introduced imports. `!!!` and `!!!!` remain unavailable without the stipulated finite-witness architecture and checker admission.

**25-round status: seven complete numbered manuscript items, substantial additional verified subresults, no unproved quantitative claim promoted.**


## 28. Round 26 — head, manifest, frozen cache and source-hash gate (26 October 2026)

Re-fetched **all visible branches and current GitHub Actions runs** for both `zetahyperbolic-axiom` and `snditeration`. There is **no newly accepted mathematical commit** beyond `zetahyperbolic-axiom/main@86ca99a` ([CI PASS 40188664869](https://github.com/randogelist/zetahyperbolic-axiom/actions/runs/40188664869)) or `snditeration/main@c521749` ([CI PASS 40186793090](https://github.com/randogelist/snditeration/actions/runs/40186793090)). The broad `snditeration/feat/zetahyperbolic-continuation-20261025` has failed CI at `0cee4ea` and **is not a crossing source**.

Eight exact modules in this round were checked against [`modules.txt`](../modules.txt), their retained [source-hash inventory](../provenance/active_module_hashes.json) and the accepted [219-module axiom-audited receipt](../validation/linux/acceptance.json): `PaperChain.Stage04PrincipalMinorCenter`, `PaperChain.Stage08PoleProductBridge`, `LeanPaper.ImportedSection56.DualNonsingularDegree`, `LeanPaper.ImportedSection56.TriplePoleHermite`, `LeanPaper.Section6BetaFinite`, `PaperChain.Stage10`, `LeanPaper.Section4ManuscriptBridge`, `PaperChain.Stage05PrimitiveBridge`. **All eight are active and fingerprinted**. No fresh Lean run is inferred from this documentary audit. Despite some stale in-file comments saying “candidate”, this exact source set is covered by the subsequent passing full-project receipt; however, each theorem's mathematical hypotheses remain obligatory.

## 29. Round 27 — actual original 3.3 principal center and strict two-index inequality

[`ManuscriptChain.PrincipalMinors.gram_posDef`](../src/PaperChain/Stage04PrincipalMinorCenter.lean) proves strict **positive definiteness of the actual odd-zeta center Gram for every injectively selected principal index family**, including nonconsecutive indices. [`determinant_center_pos`](../src/PaperChain/Stage04PrincipalMinorCenter.lean) proves strict positivity for its actual **rational-polynomial principal determinant** evaluated at the genuine ζ center; [`determinant_ne_zero`](../src/PaperChain/Stage04PrincipalMinorCenter.lean) excludes the zero polynomial. These are not conditional on a *supplied* abstract positive matrix: they use the existing analytic Gram construction and admissibility.

The further [`two_index_strict`](../src/PaperChain/Stage04PrincipalMinorCenter.lean) proves, for every pair of distinct indices `i≠j`, the **actual strict** inequality
```text
G(i,j) * G(j,i) < G(i,i) * G(j,j)
```
at `ζ(2k+1)`, by positivity of the 2×2 selected principal determinant. Thus **all principal minors and every 2×2 principal gap at the center** can be crossed off for 3.3(1), and the center nonvanishing needed by corrected 3.4 is already proved. **Do not infer strict positivity of mixed minors with different row/column indices** from the principal proof. Andréief/generalized-Vandermonde mixed signs and Carleman uniqueness remain the genuinely open 3.3(1) endpoints.

## 30. Round 28 — arbitrary invertible rational dual-basis degree, beyond monicity (5.2)

[`dualDelta_degree_of_nonsingular_slope`](../src/LeanPaper/ImportedSection56/DualNonsingularDegree.lean) proves the **actual** rational dual determinant has degree `h` under just `det(dualSlopeMatrix c) ≠ 0`, without requiring monomial or identity slopes.

[`dualDelta_topCoeff_nonzero_rowChange_iff`](../src/LeanPaper/ImportedSection56/DualNonsingularDegree.lean) proves an **if-and-only-if nonvanishing criterion** under *any invertible rational row change* `det A≠0`; [`dualDelta_degree_rowChange_of_nonsingular_slope`](../src/LeanPaper/ImportedSection56/DualNonsingularDegree.lean) proves resulting full degree. These generalize the already crossed selected-monomial and unimodular cases from rounds 14/20.

**Crossed:** exact finite full-degree criterion, invertible-change invariance of degree and nonzero leading coefficient for actual dual polynomial data. **Not crossed:** the genuine infinite Beukers moment realization, positive/negative infinite Krein cone, or an unconditional proof of coefficient independence for every manuscript-prescribed polynomial family.

## 31. Round 29 — corrected triple-pole local determinant and 9m-dimensional Hermite count (6.9)

The accepted [`Zetahyperbolic.TriplePoleRepair`](../src/LeanPaper/ImportedSection56/TriplePoleHermite.lean) proves exact arithmetic rather than just naming an interpolation architecture:

- `dimension_9m`: three Taylor jets at each of `3m` nodes have dimension **`9m`**.
- `localBlock_det`: the symmetric local triple-pole block has exact determinant **`-(w₂)^3`**; `localBlock_det_ne_zero` when `w₂≠0`.
- `poleFunctional_eq_jetFunctional` and `local_congruence`: the explicit triple-pole functional equals its Hermite-jet representation and its bilinear local block.
- `hermite_congruence` and `momentMatrix_det`: the arbitrary finite Hermite table gives the exact global determinant **`det(HermiteTable)^2 * ∏_a -(c_{a,2}u_{a,0})^3`**.
- `momentMatrix_det_ne_zero`: nonzero determinant *conditional on* an invertible jet table, nonzero top Laurent coefficients, and nonzero leading pole factors.

**Crossed:** the entire displayed **generic/corrected finite Hermite determinant algebra** and conditional nonvanishing implication, with no asserted unverified local determinant formula. **Still missing:** identity with *the originally printed triple-pole kernel*, invertibility of the *specific actual* Hermite table, nonzero *actual* Laurent coefficients, q-adic valuations/prime domination and the final 6.9 arithmetic claims. The module's corrected kernel must not silently replace the original.

## 32. Round 30 — actual original finite pole-energy decomposition and four-rate ζ(5) transfer

[`PaperChain.stage08_original_finite_pole_energy`](../src/PaperChain/Stage08PoleProductBridge.lean) proves, **without an asymptotic hypothesis and using the original manuscript parameters**, the exact relation
```text
leadingLog + valueDecayLog
  = 2*log(vandermondeSize) + log(poleProductSize) - gramLog.
```
This is a sharper **finite pole-product expansion** of the already certified K²-normalized energy identities from round 10.

[`stage05_zeta5_irrational_if_pole_log_rates`](../src/PaperChain/Stage08PoleProductBridge.lean) then proves a true A-Tier **conditional** endpoint `Irrational (Real.zeta 5)` from four actual-family eventual quadratic rate estimates and their strict gap `A+B < 2*C+D`. The theorem's explicit `hleading`, `hgram`, `hvandermonde` and `hpoles` premises are **not discharged**. It neither proves the manuscript's specific `11.411` spectral constant nor its fixed `1/2500` decay.

**Crossed for 4.4/4.6/6.10:** all-finite original-data Vandermonde/Gram/pole energy equality and the conditional four-rate transfer. **Open:** actual asymptotic evaluation of those four rates, the strict positive gap, the numerical constants and all consequent unconditional odd-zeta claims.

## 33. Round 31 — β finite tensor-grid Gram and exact orientation (5.3, 6.4)

The accepted [`LeanPaper.Section6BetaFinite`](../src/LeanPaper/Section6BetaFinite.lean) proves **strictly positive weighted two-node and three-node polynomial Gram forms**, and also a true `2×2` **tensor interpolation grid** for the four monomials `1,x,y,xy`: `PAPER10_BILINEAR_TENSOR_GRID_ZERO` proves that all four evaluations vanish only when all four polynomial coefficients vanish; `PAPER10_BILINEAR_TENSOR_GRID_GRAM_STRICT` proves the resulting four-node quadratic energy is strictly positive for any nonzero bilinear vector **when all four masses are positive**.

[`PAPER10_BETA_FULL_CHARACTER_VANDERMONDE_CANCELLATION`](../src/LeanPaper/Section6BetaFinite.lean) includes a *global* `(-1)^N` orientation that makes the **normalized** finite residue sign positive. The independent [`PaperChain.stage10_character_vandermonde_sign`](../src/PaperChain/Stage10.lean) confirms the **raw** parity is `(-1)^N`; [`stage10_even_start_positive`](../src/PaperChain/Stage10.lean) proves the special case `Even N` has raw positive sign.

**Crossed:** exact finite positive two/three-node and four-node tensor-grid algebra and corrected parity bookkeeping. These are genuinely proved useful **finite submodels** of 5.3 and 6.4, but **do not identify any actual β(4) Beukers analytic density, its signed residues, or a q-adic valuation**. The raw-sign condition for odd `N` must remain explicit in the paper repair.

## 34. Round 32 — exclude false promotions after proof-body audit

Explicitly tested the remaining tempting shortcut claims against their **declaration types**:

- `PaperChain.Stage04.ExactMinorRankLaw` and `InterlacesFiniteRootLists` are **defined `Prop`s**, not proofs of rank-sensitive interlacing. The valid rank law is separately proved in [`PrincipalMinorRank`](../src/LeanPaper/PrincipalMinorRank.lean); compatible eigenvalue interlacing remains open.
- `PaperChain.Stage07.WeightSandwich` and `Zeta3Zeta5PositivityCone` are **only definitions**, not a proof of the coupled ζ(5),ζ(3) analytic positive cone.
- `PaperChain.Stage09.StrictTailCertificate` is **only a declared certificate predicate**, not an accepted actual pole-ordered prime valuation or a concrete passing witness. Its rational-sign theorem does not calculate the printed floor integral.
- All generic [`Section6BetaFinite`](../src/LeanPaper/Section6BetaFinite.lean) strictly positive finite sums display **positive-amplitude/injective-evaluation hypotheses**, not established positivity of the original character-weight Beukers function.
- The [`LeanPaper.Section4ManuscriptBridge.manuscript_primitive_complex_padic_disk`](../src/LeanPaper/Section4ManuscriptBridge.lean) is an *actual-primitive-polynomial* specialization of the already **completed 4.3** nonarchimedean disk under explicit nonzero-center and small-radius premises. It **does not establish** 4.4–4.8's missing q-adic multiplier or its archimedean irrationality exponent.

No eighth **whole original printed** item is admitted. The manuscript-wide tally remains **7 full `!!`, 21 partial, 10 not formalized and 7 blocked**, with many individually A-Tier completed clauses. The new tracker changes only documentary evidence; no Lean source was changed, no new Linux or native Windows compilation was performed, and no S-Tier finite witness admission was observed.


## 35. Round 33 — accepted-build provenance and branch gates (26 October 2026)

Rechecked current GitHub heads and CI. The accepted [zetahyperbolic-axiom/main@86ca99a](https://github.com/randogelist/zetahyperbolic-axiom/commit/86ca99a23d65cde4880a9005a49076c43e7bc968) still has [passing Lean 4.33.0 compilation and transitive axiom audit](https://github.com/randogelist/zetahyperbolic-axiom/actions/runs/40188664869). Independent [snditeration/main@c521749](https://github.com/randogelist/snditeration/commit/c521749190cce9981b0f108a8edc8034420f6420) passed its own CI; the broader continuation [failed CI](https://github.com/randogelist/snditeration/actions/runs/40188938699). All eleven source modules inspected in these new rounds occur in the accepted [build plan](../modules.txt) and [hashed provenance inventory](../provenance/active_module_hashes.json). No new Lean build or new theorem acceptance is claimed by this review.

## 36. Round 34 — complete corrected all-real-s Proposition 3.2

The source [ContinuousWeightMoments](../src/LeanPaper/ContinuousWeightMoments.lean) proves moment integrability, the geometric-series interchange and each monomial integral for the corrected continuous density when s>1. [ContinuousGram](../src/LeanPaper/ContinuousGram.lean) proves the actual integral-defined Gram is positive definite, the determinant has exact degree h, and every complex zero is real; at the odd integer weights its corrected pencil agrees with the genuine odd-zeta pencil. Even the *printed* scaled pencil has real spectrum. However [ContinuousDensityNormalization](../src/LeanPaper/ContinuousDensityNormalization.lean) and ContinuousGram prove the printed density differs from the intended one by the factor pi/2. Cross off the entire corrected analytical construction only; **the literal 3.2 coincidence remains false**.

## 37. Round 35 — exact logarithmic lattice and cluster-fraction arithmetic (4.1, 4.7)

[Section4IndexSelection](../src/LeanPaper/Section4IndexSelection.lean) constructs d0*floor(c*log(b)/d0), proves its divisibility, quantitative bounds, divergence, and eventual index/radius budgets. [Section4EffectiveBudget](../src/LeanPaper/Section4EffectiveBudget.lean) yields a computable denominator threshold **when actual rational rate data and an effective input onset are supplied**. [Section4ManuscriptBridge](../src/LeanPaper/Section4ManuscriptBridge.lean) proves a finite cluster-fraction lower bound for the actual spectral list under explicitly supplied cap/mean bounds, and proves that a large actual spectral exponent gives a genuine root within exp(-tau) of the odd-zeta center. [Theorem_4_7_Finite_Root_Cluster_Count](../src/LeanPaper/ImportedSection4/Theorem_4_7_Finite_Root_Cluster_Count.lean) proves the exact numerical 0.014 / 0.2589 / 0.1 / 11.411 comparison. These are A-Tier **conditional finite implications**; the spectral caps and means for the actual K-family are unproved.

## 38. Round 36 — factor-distance direction and actual p-adic primitive specialization (4.8, 4.3)

[Proposition_4_8_Factor_Distance_Bounds](../src/LeanPaper/ImportedSection4/Proposition_4_8_Factor_Distance_Bounds.lean) proves a lower product estimate from **lower** bounds on every root distance and an upper product estimate from **upper** bounds. The hypotheses differ: the first cannot establish the second. [Section4ManuscriptBridge.manuscript_primitive_complex_padic_disk](../src/LeanPaper/Section4ManuscriptBridge.lean) specializes the already-complete p-adic 4.3 disk to the actual primitive polynomial, with explicit nonzero-center and radius hypotheses. Cross off these precise mathematical implications. The printed 4.8 blanket rational-root exclusion still reverses a distance inequality; its family-wide height and root-exclusion estimates remain unproved.

## 39. Round 37 — central-factorial secant identities and true pointwise density tail (6.13)

[CentralFactorialSecant](../src/LeanPaper/CentralFactorialSecant.lean) proves the closed all-k secant differential identity, its positive derivative, the exact exponential-mode multiplier, annihilation of all modes indexed l<k, and the reversed-product sign. Its explicit first surviving case has multiplier **-8** where the omitted sign gives **+8**. [CentralFactorialDecay](../src/LeanPaper/CentralFactorialDecay.lean) proves the corrected density positive and the **pointwise** bound density(k,u) <= 2*pi*u^(2*k+1)*exp(-(2*k+1)*pi*u) for u>=0. These settle substantial finite/operator and analytical estimates. They do not justify the printed false-sign infinite series, termwise differentiated convergence, or its claimed beta-pencil transfer.

## 40. Round 38 — exact weight-five polynomial quotient thresholds (6.18, 6.11)

[DyadicQuotientThreshold](../src/LeanPaper/DyadicQuotientThreshold.lean) proves the general polynomial-division disappearance threshold. For the **actual** K=30n,N=3n,M=3,k=2 specialization its quotient vanishes for every i,j<6n. For the full i,j<27n block the numerator has degree **at most 72n-1** and quotient degree **at most 42n-1** (upper bounds, not equality assertions). The file also proves the odd-square scaling and consecutive-product parity identities used in 6.11. Cross off the exact polynomial-degree algebra. No 2-adic residue integrality, odd-prime denominator multiplier, Euler distribution law or irrationality measure follows.

## 41. Round 39 — two exact local prime-arithmetic diagnostics (6.17)

[BetaHarmonicIndexObstruction](../src/LeanPaper/BetaHarmonicIndexObstruction.lean) proves that a permitted q=11, rho=3 choice contains the odd denominator 11. The actual reduced rational harmonic sum is **10956424/12006225**, with 11 dividing its denominator but not its numerator. A separate q=41 calculation certifies loss of the proposed leading diagonal pole by local cancellation. The general odd-denominator-membership lemma specifies when any odd q appears in the first M odd denominators. This refutes the two **printed proof steps**, not the universal substantive conclusion of 6.17; any replacement must rebuild the local valuation and basis argument.

## 42. Round 40 — original-manuscript and cross-branch promotion gate

All newly checked declarations belong to the previously accepted 219-module proof base, not a fresh build. The exact original-paper inventory remains **7 complete A-Tier, 21 partially formalized, 10 not formalized, 7 blocked**. Crossed subclauses include corrected all-real-s analytic moments, 4.7 finite spectral counting, 6.13 secant density decay, 6.18 exact quotient threshold and 6.17 arithmetic diagnostics. No eighth literal printed theorem is fully proved, no actual-family quadratic decay or exponential norm estimate is newly established, and no finite-witness checker has admitted a concrete witness. Future whole-item promotion requires an exact original-claim equivalence, a successful Lean+Mathlib build and transitive axiom audit. The tracker is documentation only; existing Lean sources remain unchanged.


## 43. Round 41 — accepted source and branch gate

Receiving repo main@86ca99a still has [PASS CI 40188664869](https://github.com/randogelist/zetahyperbolic-axiom/actions/runs/40188664869) including the independent Lean 4.33 transitive axiom gate; snditeration main@c521749 also has [PASS CI](https://github.com/randogelist/snditeration/actions/runs/40186793090), but [its broad continuation FAILED](https://github.com/randogelist/snditeration/actions/runs/40188938699). The sources newly credited below already appear in the accepted [build plan](../modules.txt) and [fingerprinted source inventory](../provenance/active_module_hashes.json). These are newly found old proofs, not new compilations.

## 44. Round 42 — exact finite Jacobi Taylor formula (3.8)

[ExactTaylor.affine_det_exact_second_order](../src/LeanPaper/ImportedSection3/ExactTaylor.lean) proves for any nonsingular real matrix G and any real matrix H an exact polynomial formula det(G+tH)=det(G)*(1+trace(G^-1 H)*t+R(t)*t^2), where R is explicitly the double divX of the determinant polynomial. This is a second-order finite algebraic remainder, not a bound. The actual Gram is nonsingular, so this result is applicable to the finite pencil. The true differentiated Laplace integral and orthogonal-polynomial Christoffel-Darboux identification remain open.

## 45. Round 43 — algebraic resultant and all-degree budget (4.2)

[Section4ConjugateBounds.algebraic_approximation_barrier](../src/LeanPaper/Section4ConjugateBounds.lean) derives an explicit product lower bound from a nonzero *integer* resultant, using the actual polynomial degrees and heights. [Section4AlgebraicBudget.eventually_conjugate_budget](../src/LeanPaper/Section4AlgebraicBudget.lean) proves the dangerous upper expression is eventually <1 uniformly over all minimal-polynomial degrees m<=d given explicit eventual degree/height bounds and the strict rate gap (d-1)L+lambda/c<epsilon. These are genuinely proved conditional uniform estimates. The printed arbitrary d0-lattice wrapper and actual-family rates remain unproved.

## 46. Round 44 — no consecutive centered Taylor zeros (3.7)

[ConsecutiveDerivativeZeros.actual_centered_consecutive_nonvanishing](../src/LeanPaper/ConsecutiveDerivativeZeros.lean) proves that for every admissible actual odd-zeta polynomial, any two consecutive Taylor coefficients at the true zeta center cannot both vanish (for k<h). The same file has an explicit split real-root polynomial with a vanishing *individual* coefficient despite two distinct roots, so no false inference is made to nonvanishing of every actual coefficient. [StrictTuranRolle.THEOREM_3_7_ACTUAL_CRITICAL_POINT_SEPARATION](../src/LeanPaper/ImportedSection3/StrictTuranRolle.lean) proves derivative-root separation between two zeros of the actual determinant, not interlacing of successive principal minors.

## 47. Round 45 — actual mixed spectral signs and real-exponent determinant sign (3.3)

[SlopeIndefinite.actual_factorization_has_both_signs](../src/LeanPaper/SlopeIndefinite.lean) constructs strictly positive and strictly negative actual spectral factors when h>=2, and its slope_indefinite theorem proves the real-parameter slope is neither semidefinite sign. [ImportedSection3.SlopeSign.slope_det_pos_iff](../src/LeanPaper/ImportedSection3/SlopeSign.lean) and slope_det_neg_iff identify the real-exponent determinant sign with its entire pole-residue product, using the squared Vandermonde factor. This strengthens the exact finite sign record, not the unproved nonprincipal mixed-minor total positivity or Carleman uniqueness.

## 48. Round 46 — actual coalesced reciprocal moment rank (3.6)

[ReciprocalRootMoments.finiteHankel_eq_coalesced](../src/LeanPaper/ReciprocalRootMoments.lean) constructs the distinct inverse-square atoms with aggregated positive masses and proves equality with the true atomic Hankel matrix. Its reciprocalHankel_det_pos_iff gives the *sharp* strict positivity criterion n<=number of distinct inverse-square atoms, and the actual manuscript_reciprocal_moments theorem transports positivity, shifted semidefiniteness and sharp rank to the actual determinant roots at a rational nonroot shift. Opposite root gaps can coalesce as square atoms. This confirms the corrected endpoint; the printed all-order strict claim remains false.

## 49. Round 47 — explicit real manuscript singular principal minor (3.4)

[SingularPrincipalMinorExample](../src/LeanPaper/SingularPrincipalMinorExample.lean) contains a source-audited original-paper admissible counterexample k=2,m=1,N=1,K=6. The first principal slope is exactly zero; its principal determinant is a strictly positive constant polynomial of degree zero and has no finite real roots. This is an explicit verification that the printed universal r-finite-root enumeration cannot hold. Rank-aware real-root count is already proved separately, but compatible Cauchy eigenvalue interlacing remains open. Inspection of accepted snditeration principal/reciprocal modules yielded no new whole-item completion.

## 50. Round 48 — zero-novelty signal decision

This eight-round re-inference added material *previously uncredited* accepted theorem evidence for 3.3, 3.6, 3.7, 3.8 and 4.2, and newly credited a direct original-data counterexample source for 3.4. Therefore the all-zero-novelty marker is NOT triggered. The whole manuscript remains 7/45 fully A-Tier, with 21 partial, 10 not formalized and 7 blocked. No new mathematical theorem was compiled: this is progress in discovering existing source coverage only. Remaining mixed-minor/Carleman, interlacing, integral, rate, height, beta, and prime-valuation gaps remain open.
