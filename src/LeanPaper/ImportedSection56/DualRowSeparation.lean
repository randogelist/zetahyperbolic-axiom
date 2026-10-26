import LeanPaper.ImportedSection56.DualSOS
import Mathlib.Tactic.Ring

/-!
# Theorem 5.2: strict positivity of CC^T from coefficient separation

The universal sum-of-squares identity was established previously. A
coefficient family separating its left coefficient vectors upgrades the
semidefinite result to strict positivity. This is the algebraic
consequence of the paper's linearly independent polynomial family, not an
analytic witness or a spectral estimate.
-/

noncomputable section
open scoped BigOperators
namespace PaperOrder.CoreAlgebra

/-- Finite-dimensional left kernel of C is trivial. The paper's statement
`A_0,...,A_(h-1)` linearly independent is exactly this criterion. -/
def dualCoefficientRowsSeparate {h K : ℕ}
    (c : Fin h → Fin (K + 1) → ℚ) : Prop :=
  ∀ v : Fin h → ℚ,
    (∀ r : Fin (K + 1), (∑ i : Fin h, v i * c i r) = 0) →
      ∀ i : Fin h, v i = 0

/-- A nonzero left vector has at least one nonzero projected coefficient. -/
theorem dualCoefficientRowsSeparate_exists_nonzero {h K : ℕ}
    (c : Fin h → Fin (K + 1) → ℚ)
    (hc : dualCoefficientRowsSeparate c)
    (v : Fin h → ℚ) (hv : v ≠ 0) :
    ∃ r : Fin (K + 1), (∑ i : Fin h, v i * c i r) ≠ 0 := by
  classical
  by_contra hnone
  have hall : ∀ r : Fin (K + 1), (∑ i : Fin h, v i * c i r) = 0 := by
    intro r
    by_contra hr
    exact hnone ⟨r, hr⟩
  have hvzero := hc v hall
  apply hv
  funext i
  exact hvzero i

/-- Universal strict positivity in any finite dimension where coefficient
rows are linearly independent; no determinant bound is required. -/
theorem dualSlopeQuadraticForm_pos_of_separation {h K : ℕ}
    (c : Fin h → Fin (K + 1) → ℚ)
    (hc : dualCoefficientRowsSeparate c)
    (v : Fin h → ℚ) (hv : v ≠ 0) :
    0 < dualSlopeQuadraticForm c v := by
  classical
  obtain ⟨r, hr⟩ := dualCoefficientRowsSeparate_exists_nonzero c hc v hv
  rw [dualSlopeQuadraticForm_sos]
  have hle :
      (∑ i : Fin h, v i * c i r)^2 ≤
      ∑ j : Fin (K + 1), (∑ i : Fin h, v i * c i j)^2 := by
    exact Finset.single_le_sum
      (s := (Finset.univ : Finset (Fin (K + 1))))
      (f := fun j : Fin (K + 1) => (∑ i : Fin h, v i * c i j)^2)
      (by
        intro j hj
        exact sq_nonneg _)
      (Finset.mem_univ r)
  exact lt_of_lt_of_le (sq_pos_of_ne_zero hr) hle

end PaperOrder.CoreAlgebra

#print axioms PaperOrder.CoreAlgebra.dualCoefficientRowsSeparate_exists_nonzero
#print axioms PaperOrder.CoreAlgebra.dualSlopeQuadraticForm_pos_of_separation
