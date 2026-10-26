import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Tactic

/-! Mellin logarithmic moments on `(0,1)`, with a proved exponential substitution. -/
noncomputable section
open MeasureTheory Set Real
namespace LeanPaper.UnitLogMoments

lemma image_exp_neg : (fun x : ℝ => Real.exp (-x)) '' Ioi 0 = Ioo 0 1 := by
  ext u
  constructor
  · rintro ⟨x, hx, rfl⟩
    change 0<x at hx
    exact ⟨Real.exp_pos _, Real.exp_lt_one_iff.mpr (by linarith)⟩
  · intro hu
    refine ⟨-Real.log u, ?_, ?_⟩
    · exact neg_pos.mpr (Real.log_neg hu.1 hu.2)
    · simpa using Real.exp_log hu.1

/-- Exact change of variables `u=exp(-x)` with its absolute Jacobian. -/
theorem integral_exp_neg_substitution (g : ℝ → ℝ) :
    (∫ u : ℝ in Ioo 0 1, g u) =
      ∫ x : ℝ in Ioi 0, Real.exp (-x)*g (Real.exp (-x)) := by
  rw [← image_exp_neg]
  have h := integral_image_eq_integral_abs_deriv_smul (measurableSet_Ioi (a := (0 : ℝ)))
    (fun x (_hx : x∈Ioi (0 : ℝ)) =>
      (((hasDerivAt_id x).neg).exp).hasDerivWithinAt)
    (show Set.InjOn (fun x : ℝ => Real.exp (-x)) (Ioi 0) from
      fun x hx y hy hxy => neg_injective (Real.exp_injective hxy)) g
  simpa [Real.exp_pos, abs_of_pos, abs_neg] using h

/-- The primitive Mellin/log moment, including both endpoints' integrability. -/
theorem integral_pow_log (a m : ℕ) :
    (∫ u : ℝ in Ioo 0 1, u^a * (-Real.log u)^m) =
      (m.factorial : ℝ)/(a+1)^(m+1) := by
  rw [integral_exp_neg_substitution]
  have he : (fun x : ℝ => Real.exp (-x) *
      (Real.exp (-x)^a * (-Real.log (Real.exp (-x)))^m)) =
      (fun x : ℝ => x^m * Real.exp (-(((a : ℝ)+1)*x))) := by
    funext x
    rw [Real.log_exp, neg_neg, ← Real.exp_nat_mul, ← mul_assoc, ← Real.exp_add]
    rw [show -x + (a : ℝ)*(-x) = -(((a : ℝ)+1)*x) by ring]
    ring
  rw [he]
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi
    (a := (m : ℝ)+1) (r := (a : ℝ)+1) (by positivity) (by positivity)
  simp only [add_sub_cancel_right, Real.rpow_natCast] at h
  rw [Real.Gamma_nat_eq_factorial] at h
  rw [show (m : ℝ)+1 = ((m+1 : ℕ) : ℝ) by push_cast; rfl,
    Real.rpow_natCast] at h
  rw [h, div_pow, one_pow]
  ring

theorem integrable_pow_log (a m : ℕ) :
    IntegrableOn (fun u : ℝ => u^a * (-Real.log u)^m) (Ioo 0 1) := by
  apply Integrable.of_integral_ne_zero
  rw [integral_pow_log]
  positivity

end LeanPaper.UnitLogMoments
