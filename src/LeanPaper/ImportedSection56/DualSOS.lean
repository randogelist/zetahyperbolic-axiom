import LeanPaper.ImportedSection56.DualTopCoefficient
import Mathlib.Tactic.Positivity

/-!
# Theorem 5.2 — universal dual slope sum-of-squares identity

For the dual Beukers coefficient matrix C, the derivative pencil has
slope CC^T. The quadratic form of this slope equals the sum over columns
of the squares of the projected coefficient vectors. This proves positivity
SEMIDEFINITENESS without presupposing row independence or an analytic
integral representation. No witness or asymptotic assumption is used.
-/

noncomputable section
open scoped BigOperators
namespace PaperOrder.CoreAlgebra

/-- Quadratic form of the rational dual derivative matrix. -/
def dualSlopeQuadraticForm {h K : ℕ}
    (c : Fin h → Fin (K + 1) → ℚ) (v : Fin h → ℚ) : ℚ :=
  ∑ i : Fin h, ∑ j : Fin h, v i * dualSlopeMatrix c i j * v j

/-- Exact sum-of-squares certificate, in EVERY finite dimension. -/
theorem dualSlopeQuadraticForm_sos {h K : ℕ}
    (c : Fin h → Fin (K + 1) → ℚ) (v : Fin h → ℚ) :
    dualSlopeQuadraticForm c v =
      ∑ r : Fin (K + 1), (∑ i : Fin h, v i * c i r)^2 := by
  unfold dualSlopeQuadraticForm dualSlopeMatrix
  calc
    (∑ i : Fin h, ∑ j : Fin h,
        v i * (∑ r : Fin (K + 1), c i r * c j r) * v j) =
      ∑ i : Fin h, ∑ j : Fin h, ∑ r : Fin (K + 1),
        (v i * c i r) * (v j * c j r) := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro r hr
      ring
    _ = ∑ i : Fin h, ∑ r : Fin (K + 1), ∑ j : Fin h,
        (v i * c i r) * (v j * c j r) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.sum_comm]
    _ = ∑ r : Fin (K + 1), ∑ i : Fin h, ∑ j : Fin h,
        (v i * c i r) * (v j * c j r) := by
      rw [Finset.sum_comm]
    _ = ∑ r : Fin (K + 1), (∑ i : Fin h, v i * c i r)^2 := by
      apply Finset.sum_congr rfl
      intro r hr
      rw [pow_two, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mul_sum]

/-- Every rational coefficient family has a positive-semidefinite dual
Beukers X-derivative, even if its rows are linearly dependent. -/
theorem dualSlopeQuadraticForm_nonneg {h K : ℕ}
    (c : Fin h → Fin (K + 1) → ℚ) (v : Fin h → ℚ) :
    0 ≤ dualSlopeQuadraticForm c v := by
  rw [dualSlopeQuadraticForm_sos]
  apply Finset.sum_nonneg
  intro r hr
  exact sq_nonneg _

end PaperOrder.CoreAlgebra

#print axioms PaperOrder.CoreAlgebra.dualSlopeQuadraticForm_sos
#print axioms PaperOrder.CoreAlgebra.dualSlopeQuadraticForm_nonneg
