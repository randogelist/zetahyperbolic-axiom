import LeanPaper.ImportedSection56.DualDiscriminant
import Mathlib.Tactic

/-!
# Theorem 5.2: every symmetric positive-slope 2x2 pencil has a real zero

A constructive quadratic formula, using the nonnegative discriminant
proved for the actual two-by-two symmetric affine-pencil algebra. The
root theorem is finite and unconditional under the explicit positive
slope inequalities. No odd-zeta approximation hypothesis is used.
-/

noncomputable section
namespace PaperOrder.CoreAlgebra

/-- The elementary quadratic formula over the reals, expressed as an
existence theorem so it works at any nonzero leading coefficient. -/
theorem realQuadratic_has_root_of_discriminant_nonneg
    (A B C : ℝ) (hA : A ≠ 0)
    (hdisc : 0 ≤ B ^ 2 - 4 * A * C) :
    ∃ x : ℝ, A * x ^ 2 + B * x + C = 0 := by
  let D : ℝ := B ^ 2 - 4 * A * C
  have hD : 0 ≤ D := hdisc
  have hsqrt : (Real.sqrt D) ^ 2 = D := Real.sq_sqrt hD
  have hden : 2 * A ≠ 0 := mul_ne_zero (by norm_num) hA
  have hden4 : (4 : ℝ) * A ≠ 0 := mul_ne_zero (by norm_num) hA
  let x : ℝ := (-B + Real.sqrt D) / (2 * A)
  have hidentity :
      (4 * A) * (A * x ^ 2 + B * x + C) =
        (Real.sqrt D) ^ 2 - D := by
    dsimp [x, D]
    field_simp [hA]
    ring
  have hzero : (4 * A) * (A * x ^ 2 + B * x + C) = 0 := by
    rw [hidentity, hsqrt, sub_self]
  refine ⟨x, ?_⟩
  exact (mul_eq_zero.mp hzero).resolve_left hden4

/-- Every symmetric real 2x2 affine pencil with positive-definite
slope has an actual real zero of its determinant. -/
theorem dualTwoByTwo_det_has_real_zero
    (a b c u v w : ℝ) (hu : 0 < u)
    (hM : 0 < u * w - v ^ 2) :
    ∃ x : ℝ,
      ( !![a + x * u, b + x * v; b + x * v, c + x * w] :
        Matrix (Fin 2) (Fin 2) ℝ).det = 0 := by
  have hdisc := dualTwoByTwo_discriminant_nonneg a b c u v w hu hM
  change 0 ≤ (a * w + c * u - 2 * b * v) ^ 2 -
    4 * (u * w - v ^ 2) * (a * c - b ^ 2) at hdisc
  obtain ⟨x, hx⟩ := realQuadratic_has_root_of_discriminant_nonneg
    (u * w - v ^ 2) (a * w + c * u - 2 * b * v)
    (a * c - b ^ 2) (ne_of_gt hM) hdisc
  refine ⟨x, ?_⟩
  rw [dualTwoByTwo_det_expansion]
  exact hx

end PaperOrder.CoreAlgebra

#print axioms PaperOrder.CoreAlgebra.realQuadratic_has_root_of_discriminant_nonneg
#print axioms PaperOrder.CoreAlgebra.dualTwoByTwo_det_has_real_zero
