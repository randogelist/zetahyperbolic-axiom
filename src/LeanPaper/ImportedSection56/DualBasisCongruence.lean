import LeanPaper.ImportedSection56.DualWeightInvariance

/-!
# Theorem 5.2 — rational change of polynomial basis (slope and degree)

For a finite dual Beukers coefficient family C and an arbitrary square
rational matrix A, row change of the polynomial coefficients is precisely
A*C. The X-slope consequently becomes A*(C*Cᵀ)*Aᵀ. This is a genuine
all-size algebraic theorem, not a test instance or an analytic hypothesis.
The top coefficient of det G_A(X) transforms by det(A)^2.
-/

noncomputable section
open scoped BigOperators
namespace PaperOrder.CoreAlgebra
open ManuscriptChain.Real

/-- Action of an arbitrary rational polynomial-basis matrix on coefficient rows. -/
def dualRowChange {h K : ℕ}
    (A : Matrix (Fin h) (Fin h) ℚ)
    (c : Fin h → Fin (K + 1) → ℚ) : Fin h → Fin (K + 1) → ℚ :=
  fun i r => ∑ j : Fin h, A i j * c j r

/-- Exact coefficient-matrix multiplication under a polynomial-basis change. -/
theorem dualCoefficientMatrix_rowChange {h K : ℕ}
    (A : Matrix (Fin h) (Fin h) ℚ)
    (c : Fin h → Fin (K + 1) → ℚ) :
    dualCoefficientMatrix (dualRowChange A c) = A * dualCoefficientMatrix c := by
  ext i r
  simp only [dualCoefficientMatrix, dualRowChange, Matrix.mul_apply]

/-- The dual X-slope transforms by congruence in arbitrary finite dimension. -/
theorem dualSlopeMatrix_rowChange {h K : ℕ}
    (A : Matrix (Fin h) (Fin h) ℚ)
    (c : Fin h → Fin (K + 1) → ℚ) :
    dualSlopeMatrix (dualRowChange A c) =
      A * dualSlopeMatrix c * A.transpose := by
  calc
    dualSlopeMatrix (dualRowChange A c) =
        dualCoefficientMatrix (dualRowChange A c) *
          (dualCoefficientMatrix (dualRowChange A c)).transpose :=
      dualSlopeMatrix_eq_CCT _
    _ = (A * dualCoefficientMatrix c) * (A * dualCoefficientMatrix c).transpose := by
      rw [dualCoefficientMatrix_rowChange]
    _ = A * (dualCoefficientMatrix c * (dualCoefficientMatrix c).transpose) *
          A.transpose := by
      rw [Matrix.transpose_mul]
      simp only [Matrix.mul_assoc]
    _ = A * dualSlopeMatrix c * A.transpose := by
      rw [dualSlopeMatrix_eq_CCT]

/-- Basis invariance of the highest coefficient, including singular A. -/
theorem dualDelta_top_coeff_rowChange {h K : ℕ} (s : ℕ)
    (A : Matrix (Fin h) (Fin h) ℚ)
    (c : Fin h → Fin (K + 1) → ℚ) :
    (dualDelta s (dualRowChange A c)).coeff h =
      A.det ^ 2 * (dualDelta s c).coeff h := by
  calc
    (dualDelta s (dualRowChange A c)).coeff h =
        (dualSlopeMatrix (dualRowChange A c)).det :=
      dualDelta_coefficient_dimension s _
    _ = (A * dualSlopeMatrix c * A.transpose).det := by
      rw [dualSlopeMatrix_rowChange]
    _ = A.det ^ 2 * (dualSlopeMatrix c).det := by
      rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
      ring
    _ = A.det ^ 2 * (dualDelta s c).coeff h := by
      rw [dualDelta_coefficient_dimension]

/-- A nonsingular row change preserves exact degree h when the original
coefficient Gram determinant is nonzero. -/
theorem dualDelta_degree_rowChange {h K : ℕ} (s : ℕ)
    (A : Matrix (Fin h) (Fin h) ℚ)
    (c : Fin h → Fin (K + 1) → ℚ)
    (hA : A.det ≠ 0)
    (hc : (dualDelta s c).coeff h ≠ 0) :
    (dualDelta s (dualRowChange A c)).natDegree = h := by
  have htop : (dualDelta s (dualRowChange A c)).coeff h ≠ 0 := by
    rw [dualDelta_top_coeff_rowChange]
    exact mul_ne_zero (pow_ne_zero _ hA) hc
  exact Nat.le_antisymm
    (dualDelta_natDegree_le s (dualRowChange A c))
    (Polynomial.le_natDegree_of_ne_zero htop)

end PaperOrder.CoreAlgebra

#print axioms PaperOrder.CoreAlgebra.dualSlopeMatrix_rowChange
#print axioms PaperOrder.CoreAlgebra.dualDelta_top_coeff_rowChange
#print axioms PaperOrder.CoreAlgebra.dualDelta_degree_rowChange
