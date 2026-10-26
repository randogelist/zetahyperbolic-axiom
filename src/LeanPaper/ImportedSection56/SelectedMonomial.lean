import LeanPaper.ImportedSection56.FullMonomial

/-!
# Theorem 5.2: exact monicity for EVERY coordinate-selected subspace

The full monomial special case is already present in the previous base.
Here a family of pairwise distinct monomials is selected in any order from
Q[x] of degree at most K. Its coefficient rows are standard basis vectors.
The X derivative of the dual pencil is exactly the identity, so its
determinant is monic of degree h, independently of ζ(7) and without any
analytic assumptions.
-/

noncomputable section
open Polynomial
namespace PaperOrder.CoreAlgebra
open ManuscriptChain.Real

/-- Coordinate matrix of a list of distinct selected monomials. -/
def dualSelectedMonomialCoefficients {h K : ℕ}
    (f : Fin h → Fin (K + 1)) : Fin h → Fin (K + 1) → ℚ :=
  fun i r => if f i = r then 1 else 0

/-- The selected monomial slope is the identity for an injective selection. -/
theorem dualSelectedMonomialSlope_one {h K : ℕ}
    (f : Fin h → Fin (K + 1)) (hf : Function.Injective f) :
    dualSlopeMatrix (dualSelectedMonomialCoefficients f) = 1 := by
  classical
  ext i j
  by_cases hij : i = j
  · subst j
    simp [dualSlopeMatrix, dualSelectedMonomialCoefficients, Matrix.one_apply]
  · have hne : f i ≠ f j := fun h => hij (hf h)
    simp [dualSlopeMatrix, dualSelectedMonomialCoefficients,
      Matrix.one_apply, hij, hne, mul_ite]

/-- The coefficient of X^h in every such dual pencil is exactly 1. -/
theorem dualSelectedMonomialDelta_monic {h K : ℕ} (s : ℕ)
    (f : Fin h → Fin (K + 1)) (hf : Function.Injective f) :
    (dualDelta s (dualSelectedMonomialCoefficients f)).coeff h = 1 := by
  rw [dualDelta_coefficient_dimension, dualSelectedMonomialSlope_one f hf]
  simp

/-- Consequently, the dual determinant has exact degree h (including h=0). -/
theorem dualSelectedMonomialDelta_degree {h K : ℕ} (s : ℕ)
    (f : Fin h → Fin (K + 1)) (hf : Function.Injective f) :
    (dualDelta s (dualSelectedMonomialCoefficients f)).natDegree = h := by
  have htop :
      (dualDelta s (dualSelectedMonomialCoefficients f)).coeff h ≠ 0 := by
    rw [dualSelectedMonomialDelta_monic s f hf]
    exact one_ne_zero
  exact Nat.le_antisymm
    (dualDelta_natDegree_le s (dualSelectedMonomialCoefficients f))
    (Polynomial.le_natDegree_of_ne_zero htop)

end PaperOrder.CoreAlgebra

#print axioms PaperOrder.CoreAlgebra.dualSelectedMonomialSlope_one
#print axioms PaperOrder.CoreAlgebra.dualSelectedMonomialDelta_degree
