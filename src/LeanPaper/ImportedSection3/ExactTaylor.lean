import LeanPaper.ImportedSection3.Jacobi
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.Tactic

/-!
# Theorem 3.8 -- exact finite-dimensional Jacobi expansion

The coefficient identities here hold in every finite dimension, for every
real matrix and for every scalar perturbation t.  The quadratic remainder
is an *exact polynomial*, not asymptotic big-O notation.

The previous Jacobi theorem identifies its first-order coefficient as the
trace of the relative matrix.  This module retains the complete higher-order
remainder explicitly, which is useful when the manuscript's Section 4
requires quantitative control of perturbations.

This is **not** the analytic Laplace-weight differentiation-under-the-integral
statement in Theorem 3.8(2); that remains an independent frontier.
-/

noncomputable section
open Matrix Polynomial
namespace PaperAdvances.Theorem3_8_ExactTaylor

/-- The constant term of the identity-centered determinant is one. -/
theorem unit_det_constant {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    (Theorem3_8_Jacobi.unitDetPoly A).eval 0 = 1 := by
  rw [Theorem3_8_Jacobi.unitDetPoly_eval]
  simp

/-- The linear coefficient is exactly the matrix trace. -/
theorem unit_det_linear_coeff {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    (Theorem3_8_Jacobi.unitDetPoly A).coeff 1 = A.trace := by
  exact Matrix.coeff_det_one_add_X_smul_one A

/-- Full-dimensional exact quadratic remainder at the identity center. -/
theorem unit_det_exact_second_order {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (t : ℝ) :
    (1 + t • A).det =
      1 + A.trace * t +
      ((Theorem3_8_Jacobi.unitDetPoly A).divX.divX).eval t * t ^ 2 := by
  exact Matrix.det_one_add_smul t A

/-- Exact second-order perturbation formula at any nonsingular base. -/
theorem affine_det_exact_second_order {n : ℕ}
    (G H : Matrix (Fin n) (Fin n) ℝ) (hG : G.det ≠ 0) (t : ℝ) :
    (G + t • H).det =
      G.det *
        (1 + (G⁻¹ * H).trace * t +
          ((Theorem3_8_Jacobi.unitDetPoly (G⁻¹ * H)).divX.divX).eval t * t ^ 2) := by
  rw [Theorem3_8_Jacobi.affineDet_factor_pointwise G H hG t]
  rw [unit_det_exact_second_order]

end PaperAdvances.Theorem3_8_ExactTaylor

#print axioms PaperAdvances.Theorem3_8_ExactTaylor.unit_det_linear_coeff
#print axioms PaperAdvances.Theorem3_8_ExactTaylor.affine_det_exact_second_order
