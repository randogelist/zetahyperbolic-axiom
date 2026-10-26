> **Final receiving verification:** All registered Lean sources discussed here are included in the 260-module [GitHub CI PASS](https://github.com/randogelist/zetahyperbolic-axiom/actions/runs/40327942655) at proof commit `7250b47ba4d20ba934e890966a9b77a559689cfd`, with a fresh all-project transitive axiom audit and negative regressions. See the [matching receipt](../../validation/github/20261026/acceptance.json) and [current whole-result status](../FORMALIZATION_STATUS.md). References below to candidates, pending CI or failed runs describe historical investigation checkpoints; compilation does not extend the exact mathematical scope recorded here.

# Section 5.2 rational-independence repair

## Affected source and exact endpoints

`src/LeanPaper/Section5RationalIndependence.lean`:

- `real_rows_separate_of_rational_injective`
- `rational_independent_dual_hyperbolicity`
- `polynomialCoefficients_independent`
- `theorem_5_2_polynomial_hyperbolicity`

The statement, quantifiers and hypotheses of every existing declaration are preserved. The final endpoint remains the actual degree-`h` and real-complex-root assertion for the weight-seven dual determinant of a linearly independent rational polynomial family with degree cutoff `K`. It does not assert the infinite Krein claims of the entire printed 5.2.

## Original failure and cause

Baseline CI run `40281177876`, job `121434811096`, source HEAD `211b362c16ff6ef73e9a5f2f70c5cbb9a444cf80`, failed in this module:

1. A declaration documentation comment was placed before a `set_option ... in` command instead of immediately before its theorem, producing `unexpected token 'set_option'; expected 'lemma'`.
2. `Matrix.PosDef.mul_conjTranspose_self c hc` requires `StarOrderedRing ℚ`, which the pinned Mathlib does not provide.
3. `hqpd.det_pos` selected a positivity-of-determinant theorem unsuitable for rational matrices. Error rendering/elaboration then exhausted 3,000,000 heartbeats.
4. The failed elaboration left `sorryAx` in the diagnostic dependency list. This was a failed build, not a valid proof receipt; merely increasing the heartbeat option could not repair the typeclass issue.

## Correction

Removed the misplaced budget command. Proved rational Gram positivity directly: rational row injectivity gives a nonzero row combination; the Gram quadratic form is exactly the sum of its rational coefficient squares and hence strictly positive. This uses ordinary ordered-field arithmetic and the generic `Matrix.PosDef.of_dotProduct_mulVec_pos`, avoiding the unsupported `StarOrderedRing ℚ` requirement.

Obtained determinant nonvanishing through the generic field theorem `PosDef.isUnit` followed by `Matrix.isUnit_iff_isUnit_det`, instead of using the inapplicable determinant-positivity theorem. The existing cast-to-real Gram argument and polynomial-independence argument remain in place.

No placeholders, new axioms, weakened hypotheses or altered theorem conclusions were introduced. No local Lean, Lake, compiler, or package installation was run.

## Verification status

Source/API review completed against pinned Mathlib commit `db584cd6d46c92f209a44c0f1c829460d327499d`; Git diff confirms unchanged declaration statements. First receiving CI `40316513854` reached the new proof but exposed two rewrite details: eager simplification expanded `dotProduct` before applying its matrix associativity identity, and `map_det` was rewritten in the wrong direction. Replaced the first with ordered `rw` steps followed by square expansion, and reversed the determinant-map rewrite. All declaration statements remain unchanged. Receiving CI for these final two corrections and the transitive axiom audit are pending. Do not classify the repaired declarations as newly verified until the exact receiving SHA passes.

## Remaining scope

The finite polynomial spectral endpoint is fully implemented in source. The infinite Krein realization and quantitative tail control of whole Theorem 5.2 are separate mathematical obligations; this repair neither assumes nor proves them.

## Second receiving CI follow-up

CI `40318924083` confirmed the ordered sum-square rewrite and all subsequent proof steps except determinant transport. Its remaining error exposed the pinned API distinction between `RingHom.mapMatrix` and `Matrix.map`: direct rewriting by `map_det` did not unfold the bundled matrix homomorphism while matching. The proof now first instantiates `map_det` on the exact rational Gram matrix, explicitly simplifies `RingHom.mapMatrix_apply` in that equality, and then rewrites by the resulting exact matrix-map identity. This changes no mathematical statement. Final receiving verification remains pending.

Third receiving CI confirmed this determinant rewrite but showed that `exact_mod_cast` does not normalize the remaining bundled `Rat.castHom` application. Replaced that final tactic by explicit `Rat.coe_castHom` normalization and `(Rat.cast_ne_zero (α := ℝ)).2 hqdet`, using the exact characteristic-zero equivalence in pinned Mathlib `Data/Rat/Cast/CharZero.lean`. The remaining source-level proof contains no guessed coercion transport. Receiving verification is pending.

## Receiving verification update

CI4 compiled `Section5RationalIndependence.lean` successfully, including the exact rational-polynomial finite-hyperbolicity endpoint; the successful subset transitive axiom audit passed. Its dependent `BeukersPolynomialSpectrum` was reached for the first time and is being repaired separately as recorded in `beukers_polynomial_spectrum.md`. Whole-project completion is still pending.
