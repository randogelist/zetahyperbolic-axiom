import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# The k=0 endpoint of the odd-beta measure (Theorem 6.15)

These are evaluations of the actual continuous measure du/(1+u^2).
The odd first moment is log(2)/2, so the printed eta formula at s=1
requires the removable value eta(1)=log(2). Multiplying the vanishing
factor 1-2^(1-s) by a totalized zeta value at s=1 gives zero instead.
-/

noncomputable section
open MeasureTheory

namespace LeanPaper.BetaOneMoments

theorem density_positive (u : ℝ) : 0 < 1 / (1 + u ^ 2) := by positivity

theorem zeroth_moment :
    (∫ u : ℝ in (0 : ℝ)..1, 1 / (1 + u ^ 2)) = Real.pi / 4 := by
  rw [integral_one_div_one_add_sq]
  simp [Real.arctan_one]

theorem first_moment :
    (∫ u : ℝ in (0 : ℝ)..1, u / (1 + u ^ 2)) = Real.log 2 / 2 := by
  have hd (u : ℝ) :
      HasDerivAt (fun v : ℝ => Real.log (1 + v ^ 2) / 2)
        (u / (1 + u ^ 2)) u := by
    have hp : 1 + u ^ 2 ≠ 0 := ne_of_gt (by positivity)
    have hb : HasDerivAt (fun v : ℝ => 1 + v ^ 2) (2 * u) u := by
      simpa using ((hasDerivAt_id u).pow 2).const_add 1
    convert (hb.log hp).div_const (2 : ℝ) using 1
    field_simp
    <;> ring
  have hc : Continuous (fun u : ℝ => u / (1 + u ^ 2)) :=
    continuous_id.div (continuous_const.add (continuous_id.pow 2))
      (fun u => ne_of_gt (by positivity))
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := (0 : ℝ)) (b := 1)
    (fun u _ => hd u) (hc.intervalIntegrable 0 1)
  norm_num at h ⊢
  exact h

theorem first_moment_positive :
    0 < ∫ u : ℝ in (0 : ℝ)..1, u / (1 + u ^ 2) := by
  rw [first_moment]
  exact div_pos (Real.log_pos (by norm_num)) (by norm_num)

theorem eta_at_one_needs_removable_value (zetaAtOne : ℝ) :
    (∫ u : ℝ in (0 : ℝ)..1, u / (1 + u ^ 2)) ≠
      ((1 - (2 : ℝ) ^ (1 - (1 : ℕ))) * zetaAtOne) / 2 := by
  simp only [Nat.sub_self, pow_zero, sub_self, zero_mul, zero_div]
  exact ne_of_gt first_moment_positive

end LeanPaper.BetaOneMoments

#print axioms LeanPaper.BetaOneMoments.zeroth_moment
#print axioms LeanPaper.BetaOneMoments.first_moment
#print axioms LeanPaper.BetaOneMoments.eta_at_one_needs_removable_value
