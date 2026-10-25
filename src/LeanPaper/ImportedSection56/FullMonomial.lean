import LeanPaper.ImportedSection56.DualSOS

/-!
# Theorem 5.2 — full monomial dual pencil is MONIC and has full degree

When the selected family consists of all monomials of degree <= K, its
coefficient matrix is the identity and hence its X-derivative is exactly I.
Thus det G_A(X) has degree K+1 and leading coefficient 1, independently
of the unknown value ζ(7) or of any analytic estimate.
-/

noncomputable section
open Polynomial
namespace PaperOrder.CoreAlgebra
open ManuscriptChain.Real

/-- Full monomial coefficient family, with h=K+1. -/
def dualFullMonomialCoefficients (K : ℕ) :
    Fin (K + 1) → Fin (K + 1) → ℚ :=
  fun i r => if i = r then 1 else 0

/-- The full monomial coefficient matrix is literally the identity. -/
theorem dualFullMonomialCoefficientMatrix_one (K : ℕ) :
    dualCoefficientMatrix (dualFullMonomialCoefficients K) = 1 := by
  ext i j
  simp [dualCoefficientMatrix, dualFullMonomialCoefficients,
    Matrix.one_apply]

/-- The X-derivative coefficient matrix equals the identity. -/
theorem dualFullMonomialSlope_one (K : ℕ) :
    dualSlopeMatrix (dualFullMonomialCoefficients K) = 1 := by
  rw [dualSlopeMatrix_eq_CCT]
  rw [dualFullMonomialCoefficientMatrix_one]
  simp

/-- Exact coefficient 1 of the highest possible power of X. -/
theorem dualFullMonomialDelta_top_coeff (K s : ℕ) :
    (dualDelta s (dualFullMonomialCoefficients K)).coeff (K + 1) = 1 := by
  rw [dualDelta_coefficient_dimension, dualFullMonomialSlope_one]
  simp

/-- Exact degree K+1, with no residual hypothesis. -/
theorem dualFullMonomialDelta_degree (K s : ℕ) :
    (dualDelta s (dualFullMonomialCoefficients K)).natDegree = K + 1 := by
  have htop : (dualDelta s (dualFullMonomialCoefficients K)).coeff (K + 1) ≠ 0 := by
    rw [dualFullMonomialDelta_top_coeff]
    exact one_ne_zero
  apply Nat.le_antisymm
  · exact dualDelta_natDegree_le s (dualFullMonomialCoefficients K)
  · exact Polynomial.le_natDegree_of_ne_zero htop

end PaperOrder.CoreAlgebra

#print axioms PaperOrder.CoreAlgebra.dualFullMonomialSlope_one
#print axioms PaperOrder.CoreAlgebra.dualFullMonomialDelta_degree
