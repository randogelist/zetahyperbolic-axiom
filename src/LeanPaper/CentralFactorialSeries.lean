import LeanPaper.CentralFactorialSecant
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# The corrected infinite series in Theorem 6.13(1)

All exchanges of differentiation and summation are proved on a positive
half-line using summable polynomial times geometric bounds.  The manuscript
index is `k+1`; its reversed product requires the factor `(-1)^k`.
-/
noncomputable section
open Real Filter Set Finset
open scoped Topology

namespace LeanPaper.CentralFactorialSeries
open LeanPaper.CentralFactorialSecant

def frequency (n : ℕ) : ℝ := 2*n+1

lemma frequency_pos (n : ℕ) : 0 < frequency n := by
  unfold frequency
  positivity

/-- Every polynomial moment of the odd exponential modes is summable. -/
lemma summable_frequency_pow_exp (d : ℕ) {z : ℝ} (hz : 0 < z) :
    Summable (fun n : ℕ => frequency n ^ d * exp (-frequency n*z)) := by
  have hr : ‖exp (-z)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (exp_pos _), exp_lt_one_iff]
    linarith
  have hs := (summable_norm_pow_mul_geometric_of_norm_lt_one d hr).mul_left (3^d : ℝ)
  apply hs.of_norm_bounded_eventually_nat
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hf : frequency n ≤ 3*(n : ℝ) := by dsimp [frequency]; linarith
  have he : exp (-frequency n*z) ≤ exp (-z)^n := by
    rw [← exp_nat_mul]
    apply exp_le_exp.mpr
    dsimp [frequency]
    nlinarith
  rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (frequency_pos n).le _),
    Real.norm_eq_abs, abs_of_pos (exp_pos _)]
  calc
    _ ≤ (3*(n : ℝ))^d * exp (-z)^n :=
      mul_le_mul (pow_le_pow_left₀ (frequency_pos n).le hf _) he
        (exp_pos _).le (by positivity)
    _ = 3^d * ‖(n : ℝ)^d * exp (-z)^n‖ := by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), mul_pow, mul_assoc]

/-- A coefficient sequence with every exponentially damped polynomial moment. -/
def Admissible (c : ℕ → ℝ) : Prop :=
  ∀ (d : ℕ) (z : ℝ), 0 < z →
    Summable (fun n => ‖c n‖ * frequency n ^ d * exp (-frequency n*z))

lemma admissible_alternating : Admissible (fun n => (-1 : ℝ)^n) := by
  intro d z hz
  simpa using summable_frequency_pow_exp d hz

lemma Admissible.const_mul {c : ℕ → ℝ} (hc : Admissible c) (a : ℝ) :
    Admissible (fun n => a*c n) := by
  intro d z hz
  simpa only [norm_mul, mul_assoc] using (hc d z hz).mul_left ‖a‖

lemma Admissible.mul_frequency_pow {c : ℕ → ℝ} (hc : Admissible c) (e : ℕ) :
    Admissible (fun n => c n * frequency n ^ e) := by
  intro d z hz
  convert hc (e+d) z hz using 1
  funext n
  rw [norm_mul, norm_pow, Real.norm_eq_abs, abs_of_pos (frequency_pos n), pow_add]
  ring

lemma Admissible.sub {a b : ℕ → ℝ} (ha : Admissible a) (hb : Admissible b) :
    Admissible (fun n => a n-b n) := by
  intro d z hz
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
    ((ha d z hz).add (hb d z hz))
  calc
    _ ≤ (‖a n‖+‖b n‖) * frequency n^d * exp (-frequency n*z) := by
      gcongr
      exact norm_sub_le _ _
    _ = _ := by ring

lemma Admissible.neg_frequency {c : ℕ → ℝ} (hc : Admissible c) :
    Admissible (fun n => -frequency n*c n) := by
  convert (hc.mul_frequency_pow 1).const_mul (-1) using 1
  funext n
  ring

def laplaceSeries (c : ℕ → ℝ) (z : ℝ) : ℝ :=
  ∑' n, c n * exp (-frequency n*z)

lemma Admissible.summable {c : ℕ → ℝ} (hc : Admissible c)
    {z : ℝ} (hz : 0 < z) : Summable (fun n => c n*exp (-frequency n*z)) := by
  apply (hc 0 z hz).of_norm_bounded
  intro n
  simp [norm_mul, Real.norm_eq_abs, abs_of_pos (exp_pos _)]

/-- The actual derivative is the termwise derivative; the majorant is supplied,
not assumed, from admissibility at the smaller positive argument `z/2`. -/
lemma Admissible.hasDerivAt {c : ℕ → ℝ} (hc : Admissible c)
    {z : ℝ} (hz : 0 < z) :
    HasDerivAt (laplaceSeries c)
      (laplaceSeries (fun n => -frequency n*c n) z) z := by
  apply hasDerivAt_tsum_of_isPreconnected (hc 1 (z/2) (half_pos hz))
    isOpen_Ioi (convex_Ioi (z/2)).isPreconnected
  · intro n y hy
    convert ((((hasDerivAt_id y).const_mul (-frequency n)).exp).const_mul (c n)) using 1
      <;> simp only [id_eq] <;> ring
  · intro n y hy
    simp only [norm_mul, norm_neg, Real.norm_eq_abs,
      abs_of_pos (frequency_pos n), abs_of_pos (exp_pos _), pow_one]
    calc
      frequency n * |c n| * exp (-frequency n*y)
          ≤ frequency n * |c n| * exp (-frequency n*(z/2)) := by
            gcongr
            exact le_of_lt hy
      _ = _ := by ring
  · exact (show z/2 < z by linarith)
  · exact hc.summable hz
  · exact (show z/2 < z by linarith)

lemma Admissible.deriv {c : ℕ → ℝ} (hc : Admissible c)
    {z : ℝ} (hz : 0 < z) :
    deriv (laplaceSeries c) z = laplaceSeries (fun n => -frequency n*c n) z :=
  (hc.hasDerivAt hz).deriv

lemma Admissible.deriv_twice {c : ℕ → ℝ} (hc : Admissible c)
    {z : ℝ} (hz : 0 < z) :
    deriv (deriv (laplaceSeries c)) z =
      laplaceSeries (fun n => c n*frequency n^2) z := by
  have he : deriv (laplaceSeries c) =ᶠ[𝓝 z]
      laplaceSeries (fun n => -frequency n*c n) := by
    filter_upwards [eventually_gt_nhds hz] with y hy using hc.deriv hy
  rw [he.deriv_eq, hc.neg_frequency.deriv hz]
  apply tsum_congr
  intro n
  congr 1
  ring

lemma laplaceSeries_alternating {z : ℝ} (hz : 0 < z) :
    laplaceSeries (fun n => (-1 : ℝ)^n) z = halfSech z := by
  have hr : ‖-exp (-2*z)‖ < 1 := by
    rw [norm_neg, Real.norm_eq_abs, abs_of_pos (exp_pos _), exp_lt_one_iff]
    linarith
  have ht : (fun n : ℕ => (-exp (-2*z))^n * exp (-z)) =
      (fun n => (-1 : ℝ)^n * exp (-frequency n*z)) := by
    funext n
    rw [show -exp (-2*z) = (-1)*exp (-2*z) by ring, mul_pow,
      mul_assoc, ← exp_nat_mul, ← exp_add]
    congr 2
    dsimp [frequency]
    ring
  have hs := ((hasSum_geometric_of_norm_lt_one hr).mul_right (exp (-z))).tsum_eq
  rw [ht] at hs
  change laplaceSeries (fun n => (-1 : ℝ)^n) z = _ at hs
  rw [hs, halfSech, sechPower, pow_one, cosh_eq]
  rw [show -2*z = -z + -z by ring, exp_add, exp_neg]
  have he : exp z ≠ 0 := (exp_pos z).ne'
  field_simp
  <;> ring

def coefficients (k n : ℕ) : ℝ := (-1 : ℝ)^n * modeMultiplier k (frequency n)

lemma coefficients_succ (k n : ℕ) :
    coefficients (k+1) n = ((2*k+1 : ℕ) : ℝ)^2 * coefficients k n -
      coefficients k n * frequency n^2 := by
  simp only [coefficients, modeMultiplier, prod_range_succ]
  ring

lemma coefficients_admissible (k : ℕ) : Admissible (coefficients k) := by
  induction k with
  | zero => simpa [coefficients, modeMultiplier] using admissible_alternating
  | succ k ih =>
      simpa only [coefficients_succ] using
        (ih.const_mul (((2*k+1 : ℕ) : ℝ)^2)).sub (ih.mul_frequency_pow 2)

/-- The central-factorial operator acts on the convergent infinite series. -/
theorem centralOperator_eq_series (k : ℕ) {z : ℝ} (hz : 0 < z) :
    centralOperator k halfSech z = laplaceSeries (coefficients k) z := by
  induction k generalizing z with
  | zero => simpa [centralOperator, coefficients, modeMultiplier] using
      (laplaceSeries_alternating hz).symm
  | succ k ih =>
      have he : deriv (centralOperator k halfSech) =ᶠ[𝓝 z]
          deriv (laplaceSeries (coefficients k)) := by
        filter_upwards [eventually_gt_nhds hz] with y hy
        apply Filter.EventuallyEq.deriv_eq
        filter_upwards [eventually_gt_nhds hy] with w hw using ih hw
      change ((2*k+1 : ℕ) : ℝ)^2 * centralOperator k halfSech z -
        deriv (deriv (centralOperator k halfSech)) z = _
      rw [ih hz, he.deriv_eq, (coefficients_admissible k).deriv_twice hz]
      unfold laplaceSeries
      have hs₁ := ((coefficients_admissible k).summable hz).mul_left
        (((2*k+1 : ℕ) : ℝ)^2)
      have hs₂ := ((coefficients_admissible k).mul_frequency_pow 2).summable hz
      rw [← tsum_mul_left, ← hs₁.tsum_sub hs₂]
      apply tsum_congr
      intro n
      rw [coefficients_succ]
      ring

/-- The missing infinite-series equality, with the unreversed operator factors. -/
theorem central_secant_series (k : ℕ) {z : ℝ} (hz : 0 < z) :
    HasSum (fun n => (-1 : ℝ)^n * frequency n * modeMultiplier k (frequency n) *
      exp (-frequency n*z))
      (((2*k+1).factorial : ℝ)/2 * sinh z * sechPower (2*k+2) z) := by
  have hs := ((coefficients_admissible k).neg_frequency.summable hz).hasSum.neg
  have he : centralOperator k halfSech =ᶠ[𝓝 z] laplaceSeries (coefficients k) := by
    filter_upwards [eventually_gt_nhds hz] with y hy using centralOperator_eq_series k hy
  have hd := he.deriv_eq
  rw [(coefficients_admissible k).deriv hz] at hd
  have hv : -laplaceSeries (fun n => -frequency n*coefficients k n) z =
      ((2*k+1).factorial : ℝ)/2 * sinh z * sechPower (2*k+2) z := by
    rw [← hd, central_secant_derivative]
  rw [show -(∑' n, (-frequency n*coefficients k n)*exp (-frequency n*z)) =
      ((2*k+1).factorial : ℝ)/2 * sinh z * sechPower (2*k+2) z from hv] at hs
  convert hs using 1
  funext n
  dsimp [coefficients]
  ring

/-- Corrected manuscript (6.5).  The product is reversed exactly as printed,
and the required global sign is included.  Absolute convergence is part of
`HasSum`, while positivity follows from the actual closed form. -/
theorem theorem_6_13_1_corrected_series (k : ℕ) {z : ℝ} (hz : 0 < z) :
    HasSum (fun n => (-1 : ℝ)^(n+k) * frequency n *
      (∏ r ∈ range k, (frequency n^2 - ((2*r+1 : ℕ) : ℝ)^2)) *
      exp (-frequency n*z))
      (((2*k+1).factorial : ℝ)/2 * sinh z * sechPower (2*k+2) z) ∧
      0 < ((2*k+1).factorial : ℝ)/2 * sinh z * sechPower (2*k+2) z := by
  constructor
  · convert central_secant_series k hz using 1
    funext n
    rw [modeMultiplier_reversed, pow_add]
    ring
  · rw [← central_secant_derivative]
    exact central_secant_positive k hz

end LeanPaper.CentralFactorialSeries
