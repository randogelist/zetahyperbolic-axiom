import ProofAdvances.Corollary_3_6_WeightedCorrected
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Tactic

/-!
# Corollary 3.6: complete finite atomic rank threshold, including EVERY n

The finite weighted Hankel matrix is positive definite at each order n ≤ h,
provided the h atoms are pairwise distinct and all weights are positive.
Its determinant is zero for every n > h, *even for signed weights*.
Hence we obtain the exact (sharp) full-size positive determinant criterion.
This is the correct finite-support replacement for the PDF's impossible
all-orders strict-Hankel-positivity clause. It does not assert the stronger,
false printed claim or any infinite-atom spectral theorem.
-/

noncomputable section
open Matrix

namespace PaperAdvances.Corollary3_6_ExactFiniteRank

open PaperAdvances.Corollary3_6
open PaperAdvances.Corollary3_6_WeightedCorrected

/-- Every lower-order Hankel matrix is a leading principal submatrix of
  the full h-by-h atomic Hankel matrix, with no weight restrictions. -/
theorem weighted_leading_block {h : ℕ} (u w : Fin h → ℝ)
    (n : ℕ) (hn : n ≤ h) :
    weightedHankel u w n =
      (weightedHankel u w h).submatrix (Fin.castLE hn) (Fin.castLE hn) := by
  ext i j
  simp only [weightedHankel, Matrix.submatrix_apply, Fin.val_castLE]

/-- All moment Hankel truncations up to the number of distinct atoms
  are strictly positive definite, including n=0 and all intermediate n. -/
theorem weighted_posDef_up_to_support {h : ℕ} (u w : Fin h → ℝ)
    (hu : Function.Injective u) (hw : ∀ i, 0 < w i)
    (n : ℕ) (hn : n ≤ h) :
    (weightedHankel u w n).PosDef := by
  rw [weighted_leading_block u w n hn]
  exact (weighted_hankel_full_posDef u w hu hw).submatrix
    (Fin.castLE_injective hn)

/-- Precise sign criterion of the finite positive measure's determinants.
  No claim of strict positivity beyond finite support is possible. -/
theorem weighted_det_pos_iff_order_le_support {h : ℕ} (u w : Fin h → ℝ)
    (hu : Function.Injective u) (hw : ∀ i, 0 < w i)
    (n : ℕ) :
    0 < (weightedHankel u w n).det ↔ n ≤ h := by
  constructor
  · intro hp
    by_contra hn
    have hstrict : h < n := by omega
    have hz := weighted_hankel_det_zero_above_support u w n hstrict
    rw [hz] at hp
    exact (lt_irrefl 0) hp
  · intro hn
    exact (weighted_posDef_up_to_support u w hu hw n hn).det_pos

/-- Exact unweighted Stieltjes determinant dichotomy. -/
theorem unweighted_det_pos_iff_order_le_support {h : ℕ} (u : Fin h → ℝ)
    (hu : Function.Injective u) (n : ℕ) :
    0 < (finiteHankel u n).det ↔ n ≤ h := by
  have heq : weightedHankel u (fun _ => (1 : ℝ)) n = finiteHankel u n := by
    ext i j
    simp [weightedHankel, finiteHankel]
  rw [← heq]
  exact weighted_det_pos_iff_order_le_support u (fun _ => 1) hu
    (fun _ => by norm_num) n

end PaperAdvances.Corollary3_6_ExactFiniteRank

#print axioms PaperAdvances.Corollary3_6_ExactFiniteRank.weighted_leading_block
#print axioms PaperAdvances.Corollary3_6_ExactFiniteRank.weighted_posDef_up_to_support
#print axioms PaperAdvances.Corollary3_6_ExactFiniteRank.weighted_det_pos_iff_order_le_support
#print axioms PaperAdvances.Corollary3_6_ExactFiniteRank.unweighted_det_pos_iff_order_le_support
