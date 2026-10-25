import LeanPaper.ImportedSection56.DualTopCoefficient

/-!
# Theorem 5.2 — slope and highest coefficient are weight independent

For the actual rational two-variable Beukers pencil, varying the odd-weight
index changes the rational constant matrix, but not the coefficient Gram
matrix CCᵀ. This is a finite algebraic identity in every dimension, even
when the coefficient rows are linearly dependent.
-/

noncomputable section
open Polynomial
namespace PaperOrder.CoreAlgebra
open ManuscriptChain.Real

/-- Entrywise X-derivative of the dual polynomial pencil does not depend
on the weight index. -/
theorem dualEntry_derivative_weight_independent {h K : ℕ}
    (s t : ℕ) (c : Fin h → Fin (K + 1) → ℚ)
    (i j : Fin h) :
    derivative (dualEntry s c i j) =
      derivative (dualEntry t c i j) := by
  rw [dualEntry_derivative, dualEntry_derivative]

/-- The highest possible coefficient in the dual determinant is fixed by
the coefficient Gram matrix, independent of the weight and its harmonic
constants. It can be zero if the coefficient rows are dependent. -/
theorem dualDelta_top_coefficient_weight_independent {h K : ℕ}
    (s t : ℕ) (c : Fin h → Fin (K + 1) → ℚ) :
    (dualDelta s c).coeff h = (dualDelta t c).coeff h := by
  rw [dualDelta_coefficient_dimension, dualDelta_coefficient_dimension]

end PaperOrder.CoreAlgebra

#print axioms PaperOrder.CoreAlgebra.dualEntry_derivative_weight_independent
#print axioms PaperOrder.CoreAlgebra.dualDelta_top_coefficient_weight_independent
