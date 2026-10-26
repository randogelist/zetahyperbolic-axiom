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
