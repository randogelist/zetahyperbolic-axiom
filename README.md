# Leaned Paper

This repository formalizes the supplied manuscript, *Spectral Theory and Diophantine Bounds for Hankel Determinants of Odd Zeta Values*, with Lean 4.33.0 and pinned Mathlib.

**The paper is not fully formalized.** Some printed statements are false, and ordinary analytic and arithmetic proof obligations remain. The repository retains verified continuation checkpoints alongside later source integrations; it is not a claim that only fatal blockers remain.

The recorded `v0_1_5_construction` Linux checkpoint contains **219 modules**, all compiled and independently audited in that historical environment. The 53 new modules preserve all 165 prior mathematical/helper sources byte for byte. The audit traverses **3,135 project declarations** and their dependencies, including private declarations; the only axioms are `propext`, `Quot.sound` and `Classical.choice`. See [acceptance](validation/linux/acceptance.json) and [proof integrity](validation/linux/proof_integrity.json). These declaration counts are not counts of manuscript theorems.

## Paper chapters and theorem tiers

This index covers **all 45 numbered results** in the [52-page manuscript](Zetahyperbolic%20(3)%20(1)%20(1).pdf): **35 theorems, 5 propositions, 3 corollaries and 2 lemmas**. Numbering and chapter order follow the paper. Definition 2.1, Remarks 4.9, 4.10 and 5.5, and Conjecture 4.11 are listed separately below.

### Tier key and evidence boundary

| Marker | Tier | Required evidence |
| --- | --- | --- |
| `!` | B-Tier derivation | A reasoned derivation of the exact stated result, with all remaining premises explicit; not a Lean certificate. |
| `!!` | A-Tier | Exact Lean statement compiled and transitively axiom-audited, with its hypotheses and execution environment recorded. |
| `!!!` | Certified conditional closure | A certified downstream chain reducing the target to a finite, terminating checker; an accepted witness may remain outstanding. |
| `!!!!` | S-Tier | An actual accepted finite raw-data witness plus the certified transfer to the exact target. |
| `—` | No whole-result tier assigned | **Partial:** components exist; **Open:** full construction/proof outstanding; **Blocked:** the literal statement requires correction. These are work states, not extra proof tiers. |

A paper proof, a source filename, an imported candidate, or an audited helper does not automatically give the full printed result a tier. A generic conditional analytic theorem is not automatically `!!!`: the finite-checker reduction must itself be established. No whole-result `!`, `!!!` or `!!!!` is assigned by this inventory.

**Recorded baseline:** seven full printed results have `!!` A-Tier evidence in the **historical Linux Lean 4.33.0** checkpoint: **2.2, 2.3, 2.4, 2.5, 3.1, 4.3 and 5.4**. The baseline ledger records another **21 partial, 10 open and 7 blocked** results. See [the semantic status report](docs/FORMALIZATION_STATUS.md), [structured evidence](docs/formalization_status.json), [all 45 ledger entries](docs/manuscript_45_ledger.csv), [Linux acceptance](validation/linux/acceptance.json) and [transitive axiom audit](validation/linux/proof_integrity.json). The row tier applies to the **whole original statement**; corrected variants and proved subclauses are distinguished in the last column.

**Receiving-tree checkpoint — 2026-10-26:** inspected `main@211b362c16ff6ef73e9a5f2f70c5cbb9a444cf80` registers **238 modules**, whereas the retained Linux receipt covers **219 modules**. Its [Actions run 40281351796](https://github.com/randogelist/zetahyperbolic-axiom/actions/runs/40281351796) failed at the compile/audit step. The seven historical tiers are preserved; this is **not** a successful 238-module audit or a native Windows PASS. Source integrations for [3.3 / 5.1 / finite 5.2](docs/GWF_MANUSCRIPT_234_CLEAN_MAIN_INTAKE_20261026.md), [4.2](docs/GWF_SECTION4_ALGEBRAIC_HEIGHT_SOURCE_INTAKE_20261026.md), [5.2 rational independence](docs/GWF_SECTION52_RATIONAL_POLYNOMIAL_INDEPENDENCE_INTAKE_20261026.md) and [weight-five signature counts](docs/GWF_WEIGHTFIVE_SIGNATURE_COUNTS_AFTER237_20261026.md) do not promote a whole manuscript result without matching receiving-build and semantic evidence. The repository edit does not change the locked execution target.

### Chapter list

| Chapter | Title | Starts on page | Numbered results |
| --- | --- | ---: | ---: |
| 1 | Introduction | [1](Zetahyperbolic%20(3)%20(1)%20(1).pdf#page=1) | 0 |
| 2 | Algebraic Structure and Canonical Basis Invariance | [3](Zetahyperbolic%20(3)%20(1)%20(1).pdf#page=3) | 4 |
| 3 | Hyperbolicity, Total Positivity, and Spectral Structure | [7](Zetahyperbolic%20(3)%20(1)%20(1).pdf#page=7) | 9 |
| 4 | Diophantine Approximation, Heights, and Root Collapse for ζ(5) | [14](Zetahyperbolic%20(3)%20(1)%20(1).pdf#page=14) | 8 |
| 5 | Weight-Seven Integral Identities, Dual Pencils, and Double-Pole Systems | [22](Zetahyperbolic%20(3)%20(1)%20(1).pdf#page=22) | 6 |
| 6 | Structural Barriers, Multi-Weight Couplings, and Further Diophantine Advances | [29](Zetahyperbolic%20(3)%20(1)%20(1).pdf#page=29) | 18 |
| 7 | Discussion and Open Problems | [51](Zetahyperbolic%20(3)%20(1)%20(1).pdf#page=51) | 0 |

### Chapter 2 — Algebraic Structure and Canonical Basis Invariance

| Result | Printed title | Recorded whole-result tier / state | Proved scope, correction or open endpoint |
| --- | --- | --- | --- |
| [Lemma 2.2](Zetahyperbolic%20(3)%20(1)%20(1).pdf#page=4) | Pullback identity | **!! A — Linux baseline** | Complete actual rational-functional pullback and representation independence. |
| [Lemma 2.3](Zetahyperbolic%20(3)%20(1)%20(1).pdf#page=5) | Reflection and difference identities for τ_X | **!! A — Linux baseline** | Complete statement; retain the documented Bernoulli B₁ correction to its proof prose. |
| [Theorem 2.4](Zetahyperbolic%20(3)%20(1)%20(1).pdf#page=6) | Canonical basis invariance | **!! A — Linux baseline** | Complete functional/basis congruence and primitive normalization up to sign. |
| [Theorem 2.5](Zetahyperbolic%20(3)%20(1)%20(1).pdf#page=6) | Lagrange pole diagonalization | **!! A — Linux baseline** | Complete diagonalization; alternative product spelling is tracked separately. |

### Chapter 3 — Hyperbolicity, Total Positivity, and Spectral Structure

| Result | Printed title | Recorded whole-result tier / state | Proved scope, correction or open endpoint |
| --- | --- | --- | --- |
| [Theorem 3.1](Zetahyperbolic%20(3)%20(1)%20(1).pdf#page=7) | Universal hyperbolicity and zero-free disk | **!! A — Linux baseline** | Complete actual primitive-polynomial statement and operator-norm disk; later exponential estimates are separate. |
| [Proposition 3.2](Zetahyperbolic%20(3)%20(1)%20(1).pdf#page=8) | Continuous hyperbolic pencil for all real s > 1 | **— Blocked** | Blocked literal odd-weight coincidence: density normalization is wrong. Corrected real-s pencil is proved. |
| [Theorem 3.3](Zetahyperbolic%20(3)%20(1)%20(1).pdf#page=8) | Total positivity, leading sign, and universal signature | **— Partial** | Mixed-minor strict positivity and determinacy remain. Shifted-solid-minor and exact weight-five count candidates are integrated; receiving verification remains open. |
| [Theorem 3.4](Zetahyperbolic%20(3)%20(1)%20(1).pdf#page=9) | Root interlacing and Dodgson condensation for principal minors | **— Blocked** | Printed r-root enumeration fails for singular slopes. Rank-sensitive components and Dodgson identity are proved; full corrected interlacing remains. |
| [Corollary 3.5](Zetahyperbolic%20(3)%20(1)%20(1).pdf#page=10) | Stieltjes J-fraction from interlacing roots | **— Blocked** | Printed fraction normalization has an actual-family counterexample. Full corrected Jacobi/Lanczos construction and spectral-edge bounds remain. |
| [Corollary 3.6](Zetahyperbolic%20(3)%20(1)%20(1).pdf#page=11) | Stieltjes reciprocal-root power sums | **— Blocked** | Printed all-order strictness, bound orientation and odd-order sign need correction. Corrected fixed-family result is proved; it is not the original statement. |
| [Theorem 3.7](Zetahyperbolic%20(3)%20(1)%20(1).pdf#page=11) | Turánian non-negativity and Newton log-concavity | **— Partial** | Strict normalized Newton components are proved. Individual centered-coefficient nonvanishing still needs an actual-family argument. |
| [Theorem 3.8](Zetahyperbolic%20(3)%20(1)%20(1).pdf#page=12) | Christoffel–Darboux pole representation and Jacobi derivative identity | **— Partial** | Finite spectral/Jacobi components exist; actual orthogonal-polynomial identification and Laplace-deformation integral assembly remain. |
| [Theorem 3.9](Zetahyperbolic%20(3)%20(1)%20(1).pdf#page=13) | Hyperbolicity for Hurwitz and Dirichlet Hankel determinants | **— Partial** | Finite Fekete positivity and pole algebra exist; actual Hurwitz/character analytic measures and pencil identification remain. |

### Chapter 4 — Diophantine Approximation, Heights, and Root Collapse for ζ(5)

| Result | Printed title | Recorded whole-result tier / state | Proved scope, correction or open endpoint |
| --- | --- | --- | --- |
| [Theorem 4.1](Zetahyperbolic%20(3)%20(1)%20(1).pdf#page=14) | Spectral irrationality measure criterion | **— Partial** | Transfer and effective-data variants exist. The printed computability claim needs effective onset/rate inputs, beyond existential eventual bounds. |
| [Proposition 4.2](Zetahyperbolic%20(3)%20(1)%20(1).pdf#page=15) | Transfer criterion for algebraic approximations of degree d ≥ 1 | **— Partial** | Lattice/resultant components and actual minimal-polynomial-height source are integrated; final receiving audit and exact whole-statement reconciliation remain. |
| [Proposition 4.3](Zetahyperbolic%20(3)%20(1)%20(1).pdf#page=15) | Ultrametric zero-free disk over Q_p | **!! A — Linux baseline** | Complete abstract ultrametric disk statement; concrete zeta valuations and irrationality are separate. |
| [Theorem 4.4](Zetahyperbolic%20(3)%20(1)%20(1).pdf#page=16) | Sharpened spectral bound and effective irrationality measure for ζ(5) | **— Partial** | Actual normalization, arithmetic multiplier, determinant decay and spectral rate 11.411 remain; measure 25687 is not certified. |
| [Theorem 4.5](Zetahyperbolic%20(3)%20(1)%20(1).pdf#page=18) | Irrationality and effective measure for bζ(5) + aζ(3) | **— Partial** | Actual positive-density cone, p-adic cancellation and uniform quantitative measure inputs remain. |
| [Theorem 4.6](Zetahyperbolic%20(3)%20(1)%20(1).pdf#page=19) | Two-sided determinant bounds and coefficient heights | **— Partial** | Uniform height/decay estimates and printed constants 0.23310 and 3.73980 remain open. |
| [Theorem 4.7](Zetahyperbolic%20(3)%20(1)%20(1).pdf#page=21) | Macroscopic exponential root collapse and root separation | **— Partial** | Uniform spectral caps, average lower bounds and actual asymptotic constants remain. |
| [Proposition 4.8](Zetahyperbolic%20(3)%20(1)%20(1).pdf#page=21) | Rational root exclusion and degree bounds for cluster factors | **— Partial** | Effective family-wide height budgets, nonvanishing and root-exclusion/cluster-degree estimates remain. |

### Chapter 5 — Weight-Seven Integral Identities, Dual Pencils, and Double-Pole Systems

| Result | Printed title | Recorded whole-result tier / state | Proved scope, correction or open endpoint |
| --- | --- | --- | --- |
| [Theorem 5.1](Zetahyperbolic%20(3)%20(1)%20(1).pdf#page=22) | Two-variable Beukers measure for ζ(7) | **— Partial** | Moment-series, actual off-diagonal integral, density and rationality sources are integrated from audited donors; combined receiving certification is still required. |
| [Theorem 5.2](Zetahyperbolic%20(3)%20(1)%20(1).pdf#page=23) | Dual hyperbolicity and Krein-space decomposition of the two-variable ζ(7) pencil | **— Partial** | Finite signed Krein and rational-independence candidates are integrated. Infinite-space/tail-controlled cones remain; correct K dependence on h. |
| [Proposition 5.3](Zetahyperbolic%20(3)%20(1)%20(1).pdf#page=24) | Two-variable Beukers measure and dual pencil for β(4) = L(4, χ₋₄) | **— Partial** | Continuous beta measure, actual dual moment/pencil identification and full spectrum remain. |
| [Theorem 5.4](Zetahyperbolic%20(3)%20(1)%20(1).pdf#page=25) | Cancellation of higher zeta values on even pole pairs | **!! A — Linux baseline** | Complete final statement; preserve the three documented sign/B₁/pole-sum proof corrections. |
| [Theorem 5.6](Zetahyperbolic%20(3)%20(1)%20(1).pdf#page=26) | Weight-seven prime-sum evaluation and pole-ordered refinement | **— Open** | Exact floor-function prime sums, outer integral 453803/288000, inner-tail bounds and pole refinement remain. |
| [Theorem 5.7](Zetahyperbolic%20(3)%20(1)%20(1).pdf#page=28) | Simultaneous double-pole Hankel determinant for {1, ζ(5), ζ(6)} | **— Open** | Actual double-pole functional and q-adic valuation/minor estimates remain. |

### Chapter 6 — Structural Barriers, Multi-Weight Couplings, and Further Diophantine Advances

| Result | Printed title | Recorded whole-result tier / state | Proved scope, correction or open endpoint |
| --- | --- | --- | --- |
| [Theorem 6.1](Zetahyperbolic%20(3)%20(1)%20(1).pdf#page=29) | Divided-difference p-adic valuation law and intrinsic p⁻⁶ barrier | **— Open** | Actual Mellin change of variables, divided-difference valuation and invertible local obstruction block remain. |
| [Theorem 6.2](Zetahyperbolic%20(3)%20(1)%20(1).pdf#page=31) | Simultaneous weight-(6, 7) Beukers functional with zero denominator overhead | **— Partial** | Arithmetic denominator component exists; continuous measure/moment realization and polynomial-integral assembly remain. |
| [Theorem 6.3](Zetahyperbolic%20(3)%20(1)%20(1).pdf#page=32) | Unconditional q-adic non-vanishing and explicit positive-cone approximations for G_A⁽⁷⁾(X) | **— Blocked** | Part (2) has an exact rational/analytic h=4 counterexample, explicitly not a Lean proof. New cone/tail construction is needed; part (1) q-adic proof remains. |
| [Theorem 6.4](Zetahyperbolic%20(3)%20(1)%20(1).pdf#page=33) | Character–Vandermonde sign cancellation and unconditional hyperbolicity for β(4) | **— Partial** | Finite sign algebra exists; actual character measure/pencil, q-adic nonvanishing and full hyperbolicity remain. |
| [Theorem 6.5](Zetahyperbolic%20(3)%20(1)%20(1).pdf#page=34) | Unconditional q-adic non-vanishing for Δ_K(0) | **— Open** | Exact stated local residue/minor arithmetic and v_q(Δ_K(0)) = −(3m_q − 2) remain. |
| [Theorem 6.6](Zetahyperbolic%20(3)%20(1)%20(1).pdf#page=35) | Generalized multi-weight positive-definite pencil | **— Partial** | Actual infinite density, uniform two-sided comparison, arithmetic multiplier and signature/asymptotics remain. |
| [Theorem 6.7](Zetahyperbolic%20(3)%20(1)%20(1).pdf#page=37) | Universal multi-weight two-variable Beukers Krein decomposition | **— Open** | Actual signed multiweight measure, infinite Krein subspaces and arithmetic nonvanishing remain. |
| [Corollary 6.8](Zetahyperbolic%20(3)%20(1)%20(1).pdf#page=38) | Unconditional three-term linear independence cone for {1, ζ(3), ζ(5)} | **— Open** | Actual cone/approximants and nonvanishing, height and decay estimates remain. |
| [Theorem 6.9](Zetahyperbolic%20(3)%20(1)%20(1).pdf#page=38) | Triple-pole and multi-weight Hankel determinants | **— Partial** | Finite Hermite/jet components exist; global pole order, actual-node invertibility/nonzero factors and q-adic transfer remain. |
| [Theorem 6.10](Zetahyperbolic%20(3)%20(1)%20(1).pdf#page=39) | Universal potential-gap identity and vanishing of quadratic derivative growth in two variables | **— Partial** | Finite determinant and conditional coefficient-Gram components exist; actual asymptotic potential gap and family growth limits remain. |
| [Theorem 6.11](Zetahyperbolic%20(3)%20(1)%20(1).pdf#page=40) | The p⁻⁽²ᵏ⁻¹⁾ distribution growth law and 2-adic polynomial-quotient obstruction for β(2k) | **— Open** | Euler distribution, local-prime growth, archimedean rate independence and exact dyadic quotient obstruction remain. |
| [Theorem 6.12](Zetahyperbolic%20(3)%20(1)%20(1).pdf#page=42) | Full-dimension sign-flip restoration of positive definiteness and q-adic non-vanishing for pure β(4) | **— Open** | Actual sign-flipped pencil, rational cutoffs, full Gram positivity and exact q-adic nonvanishing remain. |
| [Theorem 6.13](Zetahyperbolic%20(3)%20(1)%20(1).pdf#page=43) | Central-factorial secant differential identity, Laplace mode annihilation, and unilateral (h, 0) root signature for all k ≥ 1 | **— Blocked** | Printed series sign is wrong. Corrected finite differential identity/envelope is proved; infinite-series and actual-pencil clauses remain. |
| [Theorem 6.14](Zetahyperbolic%20(3)%20(1)%20(1).pdf#page=45) | Even-pole scaling via cosh(2πv) and coupled positive-definite pencils for bζ(5) + aβ(4) and bζ(5) − aβ(2) | **— Open** | Actual even-pole/cosh moments, comparison constants, coupled pencil and exponential disk estimates remain. |
| [Theorem 6.15](Zetahyperbolic%20(3)%20(1)%20(1).pdf#page=46) | Arithmetic transcendence, strictly positive one-variable measure, and rank-one Padé pencil for β(2k + 1) across all k ≥ 0 | **— Blocked** | Odd-beta transcendence/independence components are proved. Printed exterior h⁻²ᵏ asymptotic needs correction; effective measures and full rank-one construction remain. |
| [Theorem 6.16](Zetahyperbolic%20(3)%20(1)%20(1).pdf#page=47) | Generalized multi-weight Zeta–Beta positive-definite pencil | **— Open** | Compact-ratio helper is integrated; actual combined density, moment identity, cone/signature and quantitative arithmetic theorem remain. |
| [Theorem 6.17](Zetahyperbolic%20(3)%20(1)%20(1).pdf#page=48) | Universal two-variable Beukers Zeta–Beta pencil, Krein decomposition, and q-adic non-vanishing | **— Partial** | Corrected prime-window components exist; repair local-block inferences and construct coupled measures/infinite Krein spaces. Full theorem is not refuted by those diagnostics alone. |
| [Theorem 6.18](Zetahyperbolic%20(3)%20(1)%20(1).pdf#page=49) | Principal-minor 2-adic integrality law, dyadic height bounds for Zeta–Beta pencils, and multi-weight effective measures | **— Partial** | Quotient disappearance and exact degree components are proved; dyadic residues, determinant height loss, odd-prime multipliers and measure remain. |

### Definitions, remarks and conjecture

| Item | Topic | Status |
| --- | --- | --- |
| [Definition 2.1](Zetahyperbolic%20(3)%20(1)%20(1).pdf#page=3) | Order-s rational moment functional | Definition/construction; not one of the 45 proof-bearing results. |
| [Remark 4.9](Zetahyperbolic%20(3)%20(1)%20(1).pdf#page=22) | Spectral bounds and variational conjecture for ρ₅* | Explanatory discussion; no theorem tier assigned. |
| [Remark 4.10](Zetahyperbolic%20(3)%20(1)%20(1).pdf#page=22) | Lee–Yang phase transition at ζ(5) | Explanatory discussion; no theorem tier assigned. |
| [Conjecture 4.11](Zetahyperbolic%20(3)%20(1)%20(1).pdf#page=22) | Existence of the asymptotic spectral-growth limit and equality to the variational value | Open conjecture; no proof tier assigned. |
| [Remark 5.5](Zetahyperbolic%20(3)%20(1)%20(1).pdf#page=25) | Simple-pole scope of the even-pole cancellation formula | Scope restriction; higher-order poles require additional work. |

Chapters 1 and 7 contain the introduction and open-problem discussion, respectively, with no additional numbered theorem statements. The chapter tables preserve the manuscript's gap at 5.5 because that item is a remark.

## Verified mathematics at the recorded baseline

| Development | Exact contribution |
| --- | --- |
| [Rational functionals](docs/SECTION2_FUNCTIONAL_COMPLETION.md) | Actual linear maps on the exact rational-function domains, literal pullback/reflection/difference and even-pole cancellation, including real iterated derivatives. |
| [Basis transport](src/LeanPaper/Section2FunctionalBasis.lean) and [Lagrange functional](src/LeanPaper/Section2LagrangeFunctional.lean) | Arbitrary functional and polynomial-basis invariance; original-denominator functional identification and complete pole diagonalization. |
| [Continuous Gram pencil](src/LeanPaper/ContinuousGram.lean) | Real-s convergence, all moments, positive Gram and hyperbolicity; corrected odd-weight coincidence. The original normalization mismatch is separately proved. |
| [Strict Newton hierarchy](src/LeanPaper/ActualStrictNewton.lean) | Actual-family strict normalized coefficient/centered inequalities, using proved distinct roots from alternating residue signs. Individual centered-coefficient nonvanishing remains separate. |
| [Corrected reciprocal corollary](docs/COROLLARY_3_6_REPAIR.md) | All-order rationality/logarithmic identities, exact finite-support Hankel laws, corrected bounds and nearest-root limit. |
| [Spectral reconstruction](docs/SPECTRAL_CONTINUATION_REVIEW.md) | Actual residue signs, mixed spectrum and intrinsic inertia, all-rank Dodgson identity, and an actual-family counterexample to the printed fraction. |
| [Arithmetic transfer](docs/SECTION4_CONTINUATION_REVIEW.md) | Constructed resultants and conjugate bounds, asymptotic index budgets, rational transfer and an explicit computable threshold from effective input data. |
| [Odd beta values](src/LeanPaper/OddBetaValues.lean) | Actual ordered beta series, nonzero rational pi-power values, transcendence and finite rational linear independence, using a pinned fully audited Lindemann proof. |
| [Section 5–6 components](docs/SECTION56_CONTINUATION_REVIEW.md) | Central-factorial differential identity and exponential envelope, Mellin/log moments, common denominators, exact quotient thresholds and arithmetic obstruction diagnostics. |

The new [Beukers counterexample](docs/BEUKERS_POSITIVITY_COUNTEREXAMPLE.md) disproves Theorem 6.3(2) for its actual `h=4` polynomial subspace. Its exact rational certificate and elementary analytic enclosure have been independently reviewed; this certificate is explicitly distinguished from a Lean kernel proof.

## Build and verify

The pinned toolchain is **Lean 4.33.0**, and Mathlib is **`db584cd6d46c92f209a44c0f1c829460d327499d`**. All transitive dependencies are locked in `lake-manifest.json`. See [BUILD.md](docs/BUILD.md) for the sequential Lake build and [LOCAL_TESTING.md](docs/LOCAL_TESTING.md) for the fingerprinted local runner.

`modules.txt` is the complete dependency-ordered active build plan, ending with `LeanPaper.KernelAudit`. The GitHub workflow validates its source inventory, compiles every module and runs the independent transitive axiom gate. A workflow configuration or previous successful run does not certify a new commit; consult that commit's actual Actions results.

The original offline Windows `run.cmd` remains unchanged; [NATIVE_RUNNER.md](docs/NATIVE_RUNNER.md) documents it. Native Windows execution has not been performed here. Deliberate negative audit fixtures under `tests/axiom_walk` are not imported into the proof development.

## Provenance and open work

[Increment provenance](provenance/completion_increment.json) records the accepted source hashes and audit receipt. The [external pi intake](provenance/external_pi_intake.json) records the exact source commit, license, port adjustments and dependency closure. Earlier source and build evidence is retained.

The remaining work includes mixed-minor positivity and determinacy, orthogonal-polynomial/Laplace identities, actual Hurwitz/character and Beukers measures, corrected infinite Krein constructions, and substantial family-specific spectral, denominator, height and decay estimates. Several printed formulas and inferences need correction. No full-paper or odd-zeta irrationality claim is inferred from compilation.

The frozen workflow identifiers remain `YOU_ARE_GOODWORKFLOWFRONTIER`, `LEAN_ANCHORINGS`, and `ZETA_HYPERBOLIC_ANCHOR_1` through `ZETA_HYPERBOLIC_ANCHOR_7`.
