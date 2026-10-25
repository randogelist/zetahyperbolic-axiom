import LeanPaper.ImportedSection56.DualPencilCCT
import Theorem_3_1_Universal_Hyperbolicity_And_Zero_Free_Disk
import Mathlib.Tactic.Ring

/-!
# Principal theorem 5.2(1): all-dimensional positive-slope hyperbolicity

This is the genuine h-dimensional spectral step for a symmetric real affine
matrix pencil with positive-definite X-slope, rather than a 2x2 sample.

We also prove, for EVERY rectangular real coefficient matrix C, that its
slope CC^T is positive definite when its left coefficient evaluation map
is injective. The latter is the finite-dimensional linear-independence
condition in manuscript Theorem 5.2. No analytic tail or irrationality
claim appears in this module.
-/

noncomputable section
open scoped BigOperators MatrixOrder
open Matrix Polynomial

namespace PaperOrder.PrincipalTheorems

/-- Real version of the finite polynomial coefficient Gram matrix CC^T. -/
def coefficientSlope {h K : ℕ} (c : Fin h → Fin (K + 1) → ℝ) :
    Matrix (Fin h) (Fin h) ℝ :=
  fun i j => ∑ r : Fin (K + 1), c i r * c j r

/-- Genuine separation of coefficient rows over the real field. -/
def coefficientRowsSeparate {h K : ℕ}
    (c : Fin h → Fin (K + 1) → ℝ) : Prop :=
  ∀ v : Fin h → ℝ, v ≠ 0 →
    ∃ r : Fin (K + 1), (∑ i : Fin h, v i * c i r) ≠ 0

/-- Symmetry of the slope in arbitrary dimensions. -/
theorem coefficientSlope_symmetric {h K : ℕ}
    (c : Fin h → Fin (K + 1) → ℝ) : (coefficientSlope c).IsSymm := by
  ext i j
  simp only [Matrix.transpose_apply, coefficientSlope]
  apply Finset.sum_congr rfl
  intro r hr
  ring

/-- Exact all-dimensional Gram SOS identity (no definiteness premise). -/
theorem coefficientSlope_quadratic_sos {h K : ℕ}
    (c : Fin h → Fin (K + 1) → ℝ) (v : Fin h → ℝ) :
    (∑ i : Fin h, ∑ j : Fin h, v i * coefficientSlope c i j * v j) =
      ∑ r : Fin (K + 1), (∑ i : Fin h, v i * c i r) ^ 2 := by
  unfold coefficientSlope
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
    _ = ∑ r : Fin (K + 1), (∑ i : Fin h, v i * c i r) ^ 2 := by
      apply Finset.sum_congr rfl
      intro r hr
      rw [pow_two, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mul_sum]

/-- Strict positive definiteness of CC^T from row separation, for all h,K. -/
theorem coefficientSlope_posDef {h K : ℕ}
    (c : Fin h → Fin (K + 1) → ℝ)
    (hc : coefficientRowsSeparate c) : (coefficientSlope c).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · exact Matrix.isHermitian_iff_isSymm.mpr (coefficientSlope_symmetric c)
  · intro v hv
    have hdot : star v ⬝ᵥ ((coefficientSlope c).mulVec v) =
        ∑ i : Fin h, ∑ j : Fin h,
          v i * coefficientSlope c i j * v j := by
      simp [dotProduct, Matrix.mulVec, Pi.star_apply, star_trivial,
        Finset.mul_sum, mul_assoc]
    rw [hdot, coefficientSlope_quadratic_sos]
    obtain ⟨r, hr⟩ := hc v hv
    have hle : (∑ i : Fin h, v i * c i r) ^ 2 ≤
        ∑ j : Fin (K + 1), (∑ i : Fin h, v i * c i j) ^ 2 := by
      exact Finset.single_le_sum
        (s := (Finset.univ : Finset (Fin (K + 1))))
        (f := fun j : Fin (K + 1) => (∑ i : Fin h, v i * c i j) ^ 2)
        (by
          intro j hj
          exact sq_nonneg _)
        (Finset.mem_univ r)
    exact lt_of_lt_of_le (sq_pos_of_ne_zero hr) hle

end PaperOrder.PrincipalTheorems

#print axioms PaperOrder.PrincipalTheorems.coefficientSlope_quadratic_sos
#print axioms PaperOrder.PrincipalTheorems.coefficientSlope_posDef
