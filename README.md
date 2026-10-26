# Leaned Paper

This repository formalizes the supplied manuscript, *Spectral Theory and Diophantine Bounds for Hankel Determinants of Odd Zeta Values*, with Lean 4.33.0 and pinned Mathlib.

**The paper is not fully formalized.** Some printed statements are false, and ordinary analytic and arithmetic proof obligations remain. This is a verified continuation checkpoint, not a claim that only fatal blockers remain.

Version `v0_1_5_construction` contains **219 active modules**, all compiled and independently audited locally. The 53 new modules preserve all 165 prior mathematical/helper sources byte for byte. The audit traverses **3,135 project declarations** and their dependencies, including private declarations; the only axioms are `propext`, `Quot.sound` and `Classical.choice`. See [acceptance](validation/linux/acceptance.json) and [proof integrity](validation/linux/proof_integrity.json). These declaration counts are not counts of manuscript theorems.

## Manuscript correspondence

Seven complete printed results are verified: **2.2, 2.3, 2.4, 2.5, 3.1, 4.3 and 5.4**. The remaining results comprise 21 partial developments, 10 not yet formalized and 7 blocked literal statements. Every one of the 45 results is tracked in [the status report](docs/FORMALIZATION_STATUS.md), its [structured companion](docs/formalization_status.json), and [the ledger](docs/manuscript_45_ledger.csv).

A supporting lemma, conditional transfer, corrected statement or counterexample does not count as a proof of the original theorem. Detailed source correspondence and repairs are recorded in the section reviews.

## New verified mathematics

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
