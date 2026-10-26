import LeanPaper.ReciprocalRootMoments
import LeanPaper.ImportedSection3.NormalizedContinuedFraction

/-!
# Obstructions to the literal statements of Corollaries 3.5 and 3.6

These results preserve the distinction between a corrected theorem and the
printed statement. The Hankel obstruction applies to the actual manuscript
root vector, at every shift. The two numerical identities are diagnostics
for the general normalized-matrix and logarithmic-derivative calculations;
they are not asserted to be instances of the manuscript parameter family.
-/

noncomputable section
open scoped BigOperators

namespace LeanPaper.ManuscriptObstructions

open LeanPaper.ReciprocalRootMoments
open LeanPaper.Section3ContinuedFractions

/-- The next Hankel determinant after the number of listed manuscript roots
vanishes. Repeated inverse-square gaps may force vanishing even earlier. -/
theorem manuscript_hankel_det_succ_eq_zero
    (p : ManuscriptChain.Real.Parameters)
    (hp : ManuscriptChain.Real.Admissible p) (q : ℝ) :
    (reciprocalHankel (manuscriptRoots p hp) q (p.h + 1)).det = 0 := by
  apply reciprocalHankel_det_zero_above_distinct_support
  have hcard : (atomSupport (reciprocalAtom (manuscriptRoots p hp) q)).card ≤ p.h := by
    classical
    unfold atomSupport
    simpa using Finset.card_image_le
      (s := (Finset.univ : Finset (Fin p.h)))
      (f := reciprocalAtom (manuscriptRoots p hp) q)
  omega

/-- Thus the printed all-orders strict-positivity assertion is impossible
for the actual finite root family, including rational non-root shifts. -/
theorem manuscript_hankel_not_positive_at_all_orders
    (p : ManuscriptChain.Real.Parameters)
    (hp : ManuscriptChain.Real.Admissible p) (q : ℝ) :
    ¬ ∀ n : ℕ, 0 < (reciprocalHankel (manuscriptRoots p hp) q n).det := by
  intro h
  have hnext := h (p.h + 1)
  rw [manuscript_hankel_det_succ_eq_zero] at hnext
  exact (lt_irrefl (0 : ℝ)) hnext

/-- At t = 0 the normalized pencil is the identity. The unscaled printed
two-level fraction with a₁ = 2, a₂ = 3, b₁ = 1 instead gives 3/5. -/
theorem normalized_fraction_printed_formula_fails :
    (1 + (0 : ℝ) * 3) / normalizedTwoDet 2 1 3 0 ≠
      1 / (2 + (0 : ℝ) - 1 ^ 2 / (3 + 0)) := by
  norm_num [normalizedTwoDet]

/-- For P = X - 1 at q = 0, P'/P = -1 whereas (1-q)⁻¹ = 1.
This isolates the odd-order sign error independently of any root theorem. -/
theorem first_logarithmic_ratio_sign_fails :
    (Polynomial.derivative (Polynomial.X - 1 : Polynomial ℝ)).eval 0 /
        (Polynomial.X - 1 : Polynomial ℝ).eval 0 ≠
      ((1 : ℝ) - 0)⁻¹ := by
  norm_num

end LeanPaper.ManuscriptObstructions
