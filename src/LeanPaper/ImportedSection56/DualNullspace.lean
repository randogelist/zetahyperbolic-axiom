import LeanPaper.ImportedSection56.DualRowSeparation

/-!
# Theorem 5.2 — exact dual Gram nullspace criterion

For arbitrary rational coefficient arrays C, the quadratic form of
C C^T vanishes exactly on the left nullspace of C. Consequently strict
quadratic positivity for all nonzero vectors is *equivalent* to algebraic
independence of the coefficient rows, with no auxiliary analytical or
witness hypotheses. This sharpens the previously proved one-way theorem.
-/

noncomputable section
open scoped BigOperators
namespace PaperOrder.CoreAlgebra

/-- Sum-of-squares is zero precisely when every projected coefficient
vanishes, in arbitrary finite dimensions. -/
theorem dualSlopeQuadraticForm_zero_iff {h K : ℕ}
    (c : Fin h → Fin (K + 1) → ℚ) (v : Fin h → ℚ) :
    dualSlopeQuadraticForm c v = 0 ↔
      ∀ r : Fin (K + 1), (∑ i : Fin h, v i * c i r) = 0 := by
  rw [dualSlopeQuadraticForm_sos]
  constructor
  · intro hsum r
    have hle : (∑ i : Fin h, v i * c i r) ^ 2 ≤
        ∑ j : Fin (K + 1), (∑ i : Fin h, v i * c i j) ^ 2 := by
      exact Finset.single_le_sum
        (s := (Finset.univ : Finset (Fin (K + 1))))
        (f := fun j : Fin (K + 1) => (∑ i : Fin h, v i * c i j)^2)
        (by
          intro j hj
          exact sq_nonneg _)
        (Finset.mem_univ r)
    have hsq_le : (∑ i : Fin h, v i * c i r)^2 ≤ 0 := by
      simpa only [hsum] using hle
    have hsq : (∑ i : Fin h, v i * c i r)^2 = 0 :=
      le_antisymm hsq_le (sq_nonneg _)
    have hmul : (∑ i : Fin h, v i * c i r) *
        (∑ i : Fin h, v i * c i r) = 0 := by
      simpa only [pow_two] using hsq
    rcases mul_eq_zero.mp hmul with hz | hz
    · exact hz
    · exact hz
  · intro hzero
    simp [hzero]

/-- Complete equivalence between the positive-definite Gram quadratic
criterion and left-row separation of the actual dual coefficient matrix. -/
theorem dualSlopeQuadraticForm_pos_iff_rowsSeparate {h K : ℕ}
    (c : Fin h → Fin (K + 1) → ℚ) :
    (∀ v : Fin h → ℚ, v ≠ 0 → 0 < dualSlopeQuadraticForm c v) ↔
      dualCoefficientRowsSeparate c := by
  constructor
  · intro hpos v hkernel
    have hvzero : v = 0 := by
      by_contra hv
      have hquad := (dualSlopeQuadraticForm_zero_iff c v).mpr hkernel
      exact (ne_of_gt (hpos v hv)) hquad
    intro i
    simp [hvzero]
  · intro hc v hv
    exact dualSlopeQuadraticForm_pos_of_separation c hc v hv

end PaperOrder.CoreAlgebra

#print axioms PaperOrder.CoreAlgebra.dualSlopeQuadraticForm_zero_iff
#print axioms PaperOrder.CoreAlgebra.dualSlopeQuadraticForm_pos_iff_rowsSeparate
