import LeanPaper.ContinuousDensityNormalization
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! Convergence and all polynomial moments of the corrected continuous weight.
The coefficient correction is kept explicit in ContinuousDensityNormalization.
-/
noncomputable section
open scoped BigOperators
open MeasureTheory Set
namespace LeanPaper.ContinuousWeightMoments
open ManuscriptChain ContinuousDensityNormalization

theorem summable_exponentialTerm (s : ℝ) {y : ℝ} (hy : 0 < y) :
    Summable (fun n : ℕ => exponentialTerm s n y) := by
  let d : ℕ := ⌈s - 1⌉₊
  have hd : s - 1 ≤ (d : ℝ) := Nat.le_ceil _
  have hsum := (summable_nat_add_iff 1).mpr
    (_root_.Real.summable_pow_mul_exp_neg_nat_mul d
      (show 0 < 2 * _root_.Real.pi * y by positivity))
  apply Summable.of_nonneg_of_le (fun n => by unfold exponentialTerm; positivity) _ hsum
  intro n
  unfold exponentialTerm
  apply mul_le_mul_of_nonneg_right _ (le_of_lt (_root_.Real.exp_pos _))
  simpa only [_root_.Real.rpow_natCast] using
    _root_.Real.rpow_le_rpow_of_exponent_le
      (show (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)) hd

theorem correctedDensity_pos {s y : ℝ} (hs : 1 < s) (hy : 0 < y) :
    0 < correctedDensity s y := by
  have hseries : 0 < ∑' n : ℕ, exponentialTerm s n y :=
    (summable_exponentialTerm s hy).tsum_pos
      (fun n => by unfold exponentialTerm; positivity) 0 (by unfold exponentialTerm; positivity)
  unfold correctedDensity
  exact mul_pos (mul_pos (div_pos (by positivity)
    (_root_.Real.Gamma_pos_of_pos (by linarith)))
    (_root_.Real.rpow_pos_of_pos hy _)) hseries

theorem measurable_correctedDensity (s : ℝ) : Measurable (correctedDensity s) := by
  unfold correctedDensity exponentialTerm
  fun_prop

def momentTerm (s : ℝ) (e n : ℕ) (y : ℝ) : ℝ :=
  ((n + 1 : ℕ) : ℝ) ^ (s - 1) *
    (y ^ (s + (2 * e : ℕ)) *
      _root_.Real.exp (-((2 * _root_.Real.pi * ((n + 1 : ℕ) : ℝ)) * y)))

def momentCoefficient (s : ℝ) (e : ℕ) : ℝ :=
  _root_.Real.Gamma (s + (2 * e : ℕ) + 1) /
    (2 * _root_.Real.pi) ^ (s + (2 * e : ℕ) + 1)

theorem integral_momentTerm {s : ℝ} (hs : 1 < s) (e n : ℕ) :
    (∫ y : ℝ in Ioi 0, momentTerm s e n y) =
      momentCoefficient s e * (1 / ((n + 1 : ℕ) : ℝ) ^ (2 * e + 2)) := by
  have hn : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  have hp : (0 : ℝ) < 2 * _root_.Real.pi := by positivity
  have hs0 : 0 < s := by linarith
  have ha : 0 < s + (2 * e : ℕ) + 1 := by positivity
  unfold momentTerm momentCoefficient
  rw [integral_const_mul]
  have hint := _root_.Real.integral_rpow_mul_exp_neg_mul_Ioi
    (a := s + (2 * e : ℕ) + 1) (r := 2 * _root_.Real.pi * ((n + 1 : ℕ) : ℝ)) ha
    (mul_pos hp hn)
  simp only [add_sub_cancel_right] at hint
  rw [hint, _root_.Real.div_rpow (by positivity) (by positivity),
    _root_.Real.one_rpow, _root_.Real.mul_rpow hp.le hn.le]
  have he : s + (2 * e : ℕ) + 1 = (s - 1) + ((2 * e + 2 : ℕ) : ℝ) := by
    push_cast
    ring
  rw [he, _root_.Real.rpow_add hn, _root_.Real.rpow_natCast]
  have hna := _root_.Real.rpow_pos_of_pos hn (s - 1)
  field_simp
  ring

theorem momentTerm_integrable {s : ℝ} (hs : 1 < s) (e n : ℕ) :
    IntegrableOn (momentTerm s e n) (Ioi 0) := by
  apply Integrable.of_integral_ne_zero
  rw [integral_momentTerm hs]
  have hs0 : 0 < s := by linarith
  have hg := _root_.Real.Gamma_pos_of_pos (show 0 < s + (2 * e : ℕ) + 1 by positivity)
  unfold momentCoefficient
  positivity

theorem summable_integral_norm_momentTerm {s : ℝ} (hs : 1 < s) (e : ℕ) :
    Summable (fun n => ∫ y : ℝ in Ioi 0, ‖momentTerm s e n y‖) := by
  have h (n : ℕ) : (∫ y : ℝ in Ioi 0, ‖momentTerm s e n y‖) =
      momentCoefficient s e * (1 / ((n + 1 : ℕ) : ℝ) ^ (2 * e + 2)) := by
    rw [← integral_momentTerm hs]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro y hy
    apply _root_.Real.norm_of_nonneg
    unfold momentTerm
    positivity
  simp_rw [h]
  exact (Real.zeta_series_summable (s := 2 * e + 2) (by omega)).mul_left _

theorem integral_tsum_momentTerm {s : ℝ} (hs : 1 < s) (e : ℕ) :
    (∫ y : ℝ in Ioi 0, ∑' n, momentTerm s e n y) =
      momentCoefficient s e * Real.zeta (2 * e + 2) := by
  rw [← integral_tsum_of_summable_integral_norm (momentTerm_integrable hs e)
    (summable_integral_norm_momentTerm hs e)]
  simp_rw [integral_momentTerm hs]
  rw [tsum_mul_left]
  rfl

theorem integrableOn_tsum_momentTerm {s : ℝ} (hs : 1 < s) (e : ℕ) :
    IntegrableOn (fun y : ℝ => ∑' n, momentTerm s e n y) (Ioi 0) := by
  apply Integrable.of_integral_ne_zero
  rw [integral_tsum_momentTerm hs]
  have hs0 : 0 < s := by linarith
  have hg := _root_.Real.Gamma_pos_of_pos (show 0 < s + (2 * e : ℕ) + 1 by positivity)
  have hz := Real.zeta_pos (s := 2 * e + 2) (by omega)
  unfold momentCoefficient
  positivity

theorem monomial_density_eq_tsum (s : ℝ) (e : ℕ) {y : ℝ} (hy : 0 < y) :
    y ^ (2 * e) * correctedDensity s y =
      (2 * (2 * _root_.Real.pi) ^ (s - 1) / _root_.Real.Gamma s) *
        ∑' n, momentTerm s e n y := by
  unfold correctedDensity
  rw [← tsum_mul_left, ← tsum_mul_left, ← tsum_mul_left]
  apply tsum_congr
  intro n
  unfold exponentialTerm momentTerm
  rw [_root_.Real.rpow_add hy, _root_.Real.rpow_natCast]
  have hexp : -(2 * _root_.Real.pi * y) * ((n + 1 : ℕ) : ℝ) =
      -(2 * _root_.Real.pi * ((n + 1 : ℕ) : ℝ) * y) := by ring
  rw [hexp]
  ring

theorem integrableOn_monomial_density {s : ℝ} (hs : 1 < s) (e : ℕ) :
    IntegrableOn (fun y : ℝ => y ^ (2 * e) * correctedDensity s y) (Ioi 0) := by
  apply ((integrableOn_tsum_momentTerm hs e).const_mul
    (2 * (2 * _root_.Real.pi) ^ (s - 1) / _root_.Real.Gamma s)).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
  exact (monomial_density_eq_tsum s e hy).symm

theorem integral_monomial_density {s : ℝ} (hs : 1 < s) (e : ℕ) :
    (∫ y : ℝ in Ioi 0, y ^ (2 * e) * correctedDensity s y) =
      (2 * (2 * _root_.Real.pi) ^ (s - 1) / _root_.Real.Gamma s) *
        momentCoefficient s e * Real.zeta (2 * e + 2) := by
  calc
    _ = ∫ y : ℝ in Ioi 0,
        (2 * (2 * _root_.Real.pi) ^ (s - 1) / _root_.Real.Gamma s) *
          ∑' n, momentTerm s e n y :=
      setIntegral_congr_fun measurableSet_Ioi (fun y hy => monomial_density_eq_tsum s e hy)
    _ = _ := by rw [integral_const_mul, integral_tsum_momentTerm hs]; ring

end LeanPaper.ContinuousWeightMoments
