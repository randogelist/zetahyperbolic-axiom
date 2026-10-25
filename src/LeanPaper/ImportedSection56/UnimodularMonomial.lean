import LeanPaper.ImportedSection56.DualBasisCongruence
import LeanPaper.ImportedSection56.SelectedMonomial

/-!
# Theorem 5.2 — unimodular change of a selected-monomial basis

Any rational basis transform with squared determinant one preserves
exact MONICITY of the coefficient determinant. No unknown zeta value,
quantitative estimate, or external hypothesis enters this theorem.
-/

noncomputable section
namespace PaperOrder.CoreAlgebra
open ManuscriptChain.Real

/-- Coordinate-selected monomials remain monic under determinant ±1 basis
changes (the square condition is the exact algebraic requirement). -/
theorem dualUnimodularSelectedMonomial_top_coeff {h K : ℕ}
    (s : ℕ) (A : Matrix (Fin h) (Fin h) ℚ)
    (f : Fin h → Fin (K + 1))
    (hf : Function.Injective f)
    (hA : A.det ^ 2 = 1) :
    (dualDelta s (dualRowChange A (dualSelectedMonomialCoefficients f))).coeff h = 1 := by
  rw [dualDelta_top_coeff_rowChange,
      dualSelectedMonomialDelta_monic s f hf, mul_one]
  exact hA

/-- Consequently the transformed determinant still has the full degree h. -/
theorem dualUnimodularSelectedMonomial_degree {h K : ℕ}
    (s : ℕ) (A : Matrix (Fin h) (Fin h) ℚ)
    (f : Fin h → Fin (K + 1))
    (hf : Function.Injective f)
    (hA : A.det ^ 2 = 1) :
    (dualDelta s (dualRowChange A (dualSelectedMonomialCoefficients f))).natDegree = h := by
  have htop :
      (dualDelta s (dualRowChange A (dualSelectedMonomialCoefficients f))).coeff h ≠ 0 := by
    rw [dualUnimodularSelectedMonomial_top_coeff s A f hf hA]
    exact one_ne_zero
  exact Nat.le_antisymm
    (dualDelta_natDegree_le s (dualRowChange A (dualSelectedMonomialCoefficients f)))
    (Polynomial.le_natDegree_of_ne_zero htop)

end PaperOrder.CoreAlgebra

#print axioms PaperOrder.CoreAlgebra.dualUnimodularSelectedMonomial_top_coeff
#print axioms PaperOrder.CoreAlgebra.dualUnimodularSelectedMonomial_degree
