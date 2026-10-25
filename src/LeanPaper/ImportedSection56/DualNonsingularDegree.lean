import LeanPaper.ImportedSection56.DualBasisCongruence

/-!
# Theorem 5.2: full polynomial degree and basis-invariant nondegeneracy

The coefficient of X^h is *exactly* the slope determinant. Whenever that
finite rational determinant is nonzero, the dual Beukers determinant has
exact degree h. A nonsingular rational change of polynomial basis
preserves this nondegeneracy in both directions. No analytic or zeta-value
premise is inserted.
-/

noncomputable section
namespace PaperOrder.CoreAlgebra
open ManuscriptChain.Real

/-- A nonsingular *actual* dual slope forces exact degree h. -/
theorem dualDelta_degree_of_nonsingular_slope {h K : ℕ} (s : ℕ)
    (c : Fin h → Fin (K + 1) → ℚ)
    (hslope : (dualSlopeMatrix c).det ≠ 0) :
    (dualDelta s c).natDegree = h := by
  have hc : (dualDelta s c).coeff h ≠ 0 := by
    rw [dualDelta_coefficient_dimension]
    exact hslope
  exact Nat.le_antisymm (dualDelta_natDegree_le s c)
    (Polynomial.le_natDegree_of_ne_zero hc)

/-- Nonzero top coefficient is preserved AND reflected by any rational
basis change with nonzero determinant. -/
theorem dualDelta_topCoeff_nonzero_rowChange_iff {h K : ℕ} (s : ℕ)
    (A : Matrix (Fin h) (Fin h) ℚ)
    (c : Fin h → Fin (K + 1) → ℚ)
    (hA : A.det ≠ 0) :
    (dualDelta s (dualRowChange A c)).coeff h ≠ 0 ↔
      (dualDelta s c).coeff h ≠ 0 := by
  rw [dualDelta_top_coeff_rowChange]
  constructor
  · intro htop hc
    apply htop
    rw [hc, mul_zero]
  · intro hc
    exact mul_ne_zero (pow_ne_zero _ hA) hc

/-- All-dimensional basis invariance of exact polynomial degree under
nonsingular slope; applies in particular to the paper's dual pencil. -/
theorem dualDelta_degree_rowChange_of_nonsingular_slope {h K : ℕ} (s : ℕ)
    (A : Matrix (Fin h) (Fin h) ℚ)
    (c : Fin h → Fin (K + 1) → ℚ)
    (hA : A.det ≠ 0)
    (hslope : (dualSlopeMatrix c).det ≠ 0) :
    (dualDelta s (dualRowChange A c)).natDegree = h := by
  apply dualDelta_degree_rowChange s A c hA
  rw [dualDelta_coefficient_dimension]
  exact hslope

end PaperOrder.CoreAlgebra

#print axioms PaperOrder.CoreAlgebra.dualDelta_degree_of_nonsingular_slope
#print axioms PaperOrder.CoreAlgebra.dualDelta_topCoeff_nonzero_rowChange_iff
#print axioms PaperOrder.CoreAlgebra.dualDelta_degree_rowChange_of_nonsingular_slope
