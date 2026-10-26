import Mathlib.LinearAlgebra.Matrix.Polynomial
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Analysis.Matrix.Order
import Mathlib.Tactic

/-!
# Theorem 6.10: the exact finite determinant identity

For the actual affine determinant polynomial `Q`, its coefficient at the matrix
dimension is computed, then related to the determinant of the relative matrix.
The symmetric square-root version requires `S * S = A` and `det S ≠ 0`.
No limiting energy estimate or equilibrium-measure comparison is asserted.
-/

noncomputable section
open Polynomial Matrix
open scoped MatrixOrder

namespace Zetahyperbolic.Theorem6_10

variable {n : ℕ}

/-- Affine pencil centered at `xi`, with base matrix `A` and direction `M`. -/
def centeredPencil (A M : Matrix (Fin n) (Fin n) ℝ) (xi : ℝ) :
    Matrix (Fin n) (Fin n) ℝ[X] :=
  fun i j => C (A i j) + (X - C xi) * C (M i j)

/-- An arbitrary scalar normalization of the determinant of this pencil. -/
def normalizedDet (A M : Matrix (Fin n) (Fin n) ℝ) (xi scale : ℝ) : ℝ[X] :=
  C scale * (centeredPencil A M xi).det

theorem centeredPencil_eq (A M : Matrix (Fin n) (Fin n) ℝ) (xi : ℝ) :
    centeredPencil A M xi =
      (X : ℝ[X]) • M.map C + (A - xi • M).map C := by
  ext i j
  simp [centeredPencil, Matrix.map_apply, Matrix.smul_apply, Matrix.sub_apply,
    Matrix.add_apply]
  ring

/-- The coefficient at the matrix dimension, whether or not degree drops. -/
theorem normalizedDet_coeff (A M : Matrix (Fin n) (Fin n) ℝ) (xi scale : ℝ) :
    (normalizedDet A M xi scale).coeff n = scale * M.det := by
  rw [normalizedDet, Polynomial.coeff_C_mul, centeredPencil_eq]
  simpa only [Fintype.card_fin] using
    congrArg (fun x : ℝ => scale * x)
      (Polynomial.coeff_det_X_add_C_card M (A - xi • M))

/-- A nonzero normalization and nonsingular direction make the dimension
coefficient the actual leading coefficient. -/
theorem normalizedDet_natDegree
    (A M : Matrix (Fin n) (Fin n) ℝ) (xi scale : ℝ)
    (hscale : scale ≠ 0) (hM : M.det ≠ 0) :
    (normalizedDet A M xi scale).natDegree = n := by
  apply le_antisymm
  · unfold normalizedDet
    apply (Polynomial.natDegree_C_mul_le _ _).trans
    rw [centeredPencil_eq]
    simpa only [Fintype.card_fin] using
      Polynomial.natDegree_det_X_add_C_le M (A - xi • M)
  · apply Polynomial.le_natDegree_of_ne_zero
    rw [normalizedDet_coeff]
    exact mul_ne_zero hscale hM

theorem normalizedDet_eval_center (A M : Matrix (Fin n) (Fin n) ℝ)
    (xi scale : ℝ) :
    (normalizedDet A M xi scale).eval xi = scale * A.det := by
  unfold normalizedDet
  rw [Polynomial.eval_mul, Polynomial.eval_C]
  congr 1
  change (Polynomial.evalRingHom xi) (centeredPencil A M xi).det = A.det
  rw [(Polynomial.evalRingHom xi).map_det]
  congr 1
  ext i j
  simp [centeredPencil]

/-- The nonsymmetric relative matrix is sufficient for the determinant identity. -/
def relativeMatrix (A M : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n) (Fin n) ℝ := A⁻¹ * M

theorem base_det_mul_relative_det (A M : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.det ≠ 0) :
    A.det * (relativeMatrix A M).det = M.det := by
  rw [relativeMatrix, Matrix.det_mul, Matrix.det_nonsing_inv]
  simp only [Ring.inverse_eq_inv']
  field_simp

/-- Exact finite identity from Theorem 6.10, valid for every scalar normalization.
The index `n` is the matrix dimension, not an assumed polynomial degree. -/
theorem abs_top_coefficient_eq_eval_mul_relative_det
    (A M : Matrix (Fin n) (Fin n) ℝ) (xi scale : ℝ) (hA : A.det ≠ 0) :
    |(normalizedDet A M xi scale).coeff n| =
      |(normalizedDet A M xi scale).eval xi| * |(relativeMatrix A M).det| := by
  rw [normalizedDet_coeff, normalizedDet_eval_center, ← abs_mul]
  congr 1
  rw [mul_assoc, base_det_mul_relative_det A M hA]

/-- Symmetric relative matrix when `S` is a square root of the base matrix. -/
def symmetricRelativeMatrix (S M : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n) (Fin n) ℝ := S⁻¹ * M * S⁻¹

theorem square_root_det_identity
    (A M S : Matrix (Fin n) (Fin n) ℝ)
    (hS : S * S = A) (hdet : S.det ≠ 0) :
    A.det * (symmetricRelativeMatrix S M).det = M.det := by
  rw [← hS, symmetricRelativeMatrix]
  simp only [Matrix.det_mul, Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
  field_simp

/-- The same finite identity for the square-root-conjugated spectral matrix. -/
theorem abs_top_coefficient_eq_eval_mul_spectral_det
    (A M S : Matrix (Fin n) (Fin n) ℝ) (xi scale : ℝ)
    (hS : S * S = A) (hdet : S.det ≠ 0) :
    |(normalizedDet A M xi scale).coeff n| =
      |(normalizedDet A M xi scale).eval xi| * |(symmetricRelativeMatrix S M).det| := by
  rw [normalizedDet_coeff, normalizedDet_eval_center, ← abs_mul]
  congr 1
  rw [mul_assoc, square_root_det_identity A M S hS hdet]

/-- Positive definiteness constructs the square root used in the manuscript's
relative spectral matrix; no extra square-root witness is required. -/
theorem abs_top_coefficient_eq_eval_mul_sqrt_det
    (A M : Matrix (Fin n) (Fin n) ℝ) (xi scale : ℝ) (hA : A.PosDef) :
    |(normalizedDet A M xi scale).coeff n| =
      |(normalizedDet A M xi scale).eval xi| *
        |(symmetricRelativeMatrix (CFC.sqrt A) M).det| := by
  have hS : CFC.sqrt A * CFC.sqrt A = A := by
    simpa [sq] using CFC.sq_sqrt A hA.posSemidef.nonneg
  have hdet : (CFC.sqrt A).det ≠ 0 := by
    intro hz
    have hd := congrArg Matrix.det hS
    rw [Matrix.det_mul, hz, zero_mul] at hd
    exact (ne_of_gt hA.det_pos) hd.symm
  exact abs_top_coefficient_eq_eval_mul_spectral_det A M (CFC.sqrt A) xi scale hS hdet

theorem abs_leadingCoeff_eq_eval_mul_sqrt_det
    (A M : Matrix (Fin n) (Fin n) ℝ) (xi scale : ℝ)
    (hA : A.PosDef) (hscale : scale ≠ 0) (hM : M.det ≠ 0) :
    |(normalizedDet A M xi scale).leadingCoeff| =
      |(normalizedDet A M xi scale).eval xi| *
        |(symmetricRelativeMatrix (CFC.sqrt A) M).det| := by
  rw [Polynomial.leadingCoeff, normalizedDet_natDegree A M xi scale hscale hM]
  exact abs_top_coefficient_eq_eval_mul_sqrt_det A M xi scale hA

end Zetahyperbolic.Theorem6_10

#print axioms Zetahyperbolic.Theorem6_10.abs_top_coefficient_eq_eval_mul_relative_det
#print axioms Zetahyperbolic.Theorem6_10.abs_top_coefficient_eq_eval_mul_spectral_det
#print axioms Zetahyperbolic.Theorem6_10.abs_top_coefficient_eq_eval_mul_sqrt_det
#print axioms Zetahyperbolic.Theorem6_10.abs_leadingCoeff_eq_eval_mul_sqrt_det
