import LeanPaper.ImportedSection3.SignStructure
import Mathlib.Tactic

/-!
# Theorem 3.3 — real-exponent determinant sign reduction

The manuscript's slope determinant is a nonzero squared Vandermonde determinant
multiplied by the complete product of the signed pole coefficients.  Thus the
slope determinant is positive if and only if the signed pole product is.

This is an exact statement for arbitrary matrix size and every real exponent.
It does NOT assert the printed explicit inertia counts, Sylvester congruence,
Carleman determinacy, or strict total positivity of all non-principal minors.
-/

noncomputable section
open scoped BigOperators

namespace PaperAdvances.Theorem3_3_Sign

open PaperAdvances.Proposition3_2

/-- The determinant sign is exactly the sign of the pole-weight product. -/
theorem slope_det_pos_iff (p : ManuscriptChain.Real.Parameters) (s : ℝ) :
    0 < (slope p s).det ↔ 0 < ∏ a : Fin p.h, gamma p s a := by
  rw [slope_det_formula]
  have hV : 0 < (vandermonde p).det ^ 2 :=
    sq_pos_of_ne_zero (vandermonde_det_ne_zero p)
  constructor
  · intro h
    by_contra hn
    have hp : (∏ a : Fin p.h, gamma p s a) ≤ 0 := le_of_not_gt hn
    have hle : (vandermonde p).det ^ 2 * (∏ a : Fin p.h, gamma p s a) ≤ 0 := by
      simpa only [mul_comm] using (mul_nonpos_of_nonpos_of_nonneg hp hV.le)
    exact (not_lt_of_ge hle) h
  · intro hp
    exact mul_pos hV hp

/-- Likewise, the negative determinant sign is exactly that of its pole product. -/
theorem slope_det_neg_iff (p : ManuscriptChain.Real.Parameters) (s : ℝ) :
    (slope p s).det < 0 ↔ (∏ a : Fin p.h, gamma p s a) < 0 := by
  rw [slope_det_formula]
  have hV : 0 < (vandermonde p).det ^ 2 :=
    sq_pos_of_ne_zero (vandermonde_det_ne_zero p)
  constructor
  · intro h
    by_contra hn
    have hp : (0 : ℝ) ≤ ∏ a : Fin p.h, gamma p s a := le_of_not_gt hn
    have hle : (0 : ℝ) ≤ (vandermonde p).det ^ 2 * (∏ a : Fin p.h, gamma p s a) :=
      mul_nonneg hV.le hp
    exact (not_lt_of_ge hle) h
  · intro hp
    simpa only [mul_comm] using (mul_neg_of_neg_of_pos hp hV)

end PaperAdvances.Theorem3_3_Sign

#print axioms PaperAdvances.Theorem3_3_Sign.slope_det_pos_iff
#print axioms PaperAdvances.Theorem3_3_Sign.slope_det_neg_iff
