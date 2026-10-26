import ProofAdvances.Corollary_3_6_ExactFiniteRank
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Tactic

/-!
# Corollary 3.6 (corrected): every principal minor of an atomic Hankel matrix

The existing certified Gram factorization gives positive semidefiniteness
at EVERY finite truncation order, including orders beyond the atom count.
Consequently each principal minor is nonnegative, even if its indices
are repeated. For positive masses at distinct atoms, each principal
minor extracted with an injective index map from n <= h is strictly
positive. This is a genuine finite principal-minor extension, NOT the
manuscript's unrestricted total-positivity assertion about all minors.
-/

noncomputable section
open Matrix

namespace PaperAdvances.Corollary3_6_AllPrincipalMinors

open PaperAdvances.Corollary3_6_WeightedCorrected
open PaperAdvances.Corollary3_6_ExactFiniteRank

/-- Every square principal minor is nonnegative at EVERY truncation order,
including orders above the finite support; indices need not be injective. -/
theorem weighted_all_principal_minors_nonnegative
    {h n m : ℕ} (u w : Fin h → ℝ)
    (hw : ∀ k, 0 ≤ w k) (e : Fin m → Fin n) :
    0 ≤ ((weightedHankel u w n).submatrix e e).det := by
  exact ((weighted_hankel_posSemidef u w n hw).submatrix e).det_nonneg

/-- Under the sharp support bound, all DISTINCT-index principal minors
are strictly positive. This includes nonconsecutive principal minors. -/
theorem weighted_all_principal_minors_positive
    {h n m : ℕ} (u w : Fin h → ℝ)
    (hu : Function.Injective u) (hw : ∀ k, 0 < w k)
    (hn : n ≤ h) (e : Fin m → Fin n) (he : Function.Injective e) :
    0 < ((weightedHankel u w n).submatrix e e).det := by
  exact ((weighted_posDef_up_to_support u w hu hw n hn).submatrix he).det_pos

/-- At full atomic order, all injectively selected principal minors
are positive, irrespective of which powers/rows are selected. -/
theorem weighted_full_order_principal_minors_positive
    {h m : ℕ} (u w : Fin h → ℝ)
    (hu : Function.Injective u) (hw : ∀ k, 0 < w k)
    (e : Fin m → Fin h) (he : Function.Injective e) :
    0 < ((weightedHankel u w h).submatrix e e).det := by
  exact weighted_all_principal_minors_positive u w hu hw (le_refl h) e he

end PaperAdvances.Corollary3_6_AllPrincipalMinors

#print axioms PaperAdvances.Corollary3_6_AllPrincipalMinors.weighted_all_principal_minors_nonnegative
#print axioms PaperAdvances.Corollary3_6_AllPrincipalMinors.weighted_all_principal_minors_positive
#print axioms PaperAdvances.Corollary3_6_AllPrincipalMinors.weighted_full_order_principal_minors_positive
