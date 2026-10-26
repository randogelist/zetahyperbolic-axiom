import LeanPaper.ImportedSection56.DualPencilCCT
import Mathlib.Tactic.Ring

/-!
# Theorem 5.2 — complete 2x2 generalized-eigenvalue discriminant

For a real symmetric affine 2x2 pencil A + x M whose slope M is
positive definite, its discriminant is nonnegative. The result is
certified by an explicit polynomial sum-of-squares identity. It is a
fully algebraic low-dimensional subcase of the real-rooted dual pencil
and does not assert the still-open all-dimensional analytical bridge.
-/

noncomputable section
namespace PaperOrder.CoreAlgebra

/-- Discriminant of det(A + X M) for symmetric 2x2 A and M. -/
def dualTwoByTwoDiscriminant (a b c u v w : ℝ) : ℝ :=
  (a * w + c * u - 2 * b * v) ^ 2 -
    4 * (u * w - v ^ 2) * (a * c - b ^ 2)

/-- Exact determinant polynomial of the symmetric two-by-two pencil. -/
theorem dualTwoByTwo_det_expansion (a b c u v w x : ℝ) :
    ( !![a + x * u, b + x * v; b + x * v, c + x * w] :
      Matrix (Fin 2) (Fin 2) ℝ).det =
      (u * w - v ^ 2) * x ^ 2 +
        (a * w + c * u - 2 * b * v) * x + (a * c - b ^ 2) := by
  rw [Matrix.det_fin_two_of]
  ring

/-- Pure polynomial identity; on the right every term is nonnegative
when det M = uw-v^2 is positive. -/
theorem dualTwoByTwo_discriminant_sos (a b c u v w : ℝ) :
    u ^ 2 * dualTwoByTwoDiscriminant a b c u v w =
      (a * (u * w - v ^ 2) - c * u ^ 2 +
        2 * b * u * v - a * v ^ 2) ^ 2 +
      4 * (u * w - v ^ 2) * (b * u - a * v) ^ 2 := by
  unfold dualTwoByTwoDiscriminant
  ring

/-- A positive definite symmetric slope (u>0, uw-v²>0) forces the
quadratic discriminant to be nonnegative for EVERY symmetric base. -/
theorem dualTwoByTwo_discriminant_nonneg
    (a b c u v w : ℝ) (hu : 0 < u)
    (hM : 0 < u * w - v ^ 2) :
    0 ≤ dualTwoByTwoDiscriminant a b c u v w := by
  have hproduct : 0 ≤ u ^ 2 * dualTwoByTwoDiscriminant a b c u v w := by
    rw [dualTwoByTwo_discriminant_sos]
    have hfactor : 0 ≤ (4 : ℝ) * (u * w - v ^ 2) :=
      mul_nonneg (by norm_num) (le_of_lt hM)
    exact add_nonneg (sq_nonneg _) (mul_nonneg hfactor (sq_nonneg _))
  have hu2 : 0 < u ^ 2 := sq_pos_of_ne_zero (ne_of_gt hu)
  by_contra hbad
  have hneg : dualTwoByTwoDiscriminant a b c u v w < 0 :=
    lt_of_not_ge hbad
  have hcontr := mul_neg_of_pos_of_neg hu2 hneg
  exact (not_lt_of_ge hproduct) hcontr

end PaperOrder.CoreAlgebra

#print axioms PaperOrder.CoreAlgebra.dualTwoByTwo_det_expansion
#print axioms PaperOrder.CoreAlgebra.dualTwoByTwo_discriminant_sos
#print axioms PaperOrder.CoreAlgebra.dualTwoByTwo_discriminant_nonneg
