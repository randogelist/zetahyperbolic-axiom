import LeanPaper.CentralFactorialSecant

/-!
# Theorem 6.13(1): accelerated exponential envelope

This is a pointwise bound for the actual closed-form positive density, stronger
than the printed big-O assertion. As in `CentralFactorialSecant`, index `k`
here denotes manuscript index `k+1`.
-/
noncomputable section
namespace LeanPaper.CentralFactorialDecay
open Real

lemma inv_cosh_le (z : ℝ) : (Real.cosh z)⁻¹ ≤ 2 * Real.exp (-z) := by
  have hc := Real.cosh_pos z
  have he := Real.exp_pos z
  have hb : Real.exp z / 2 ≤ Real.cosh z := by
    rw [Real.cosh_eq]
    linarith [Real.exp_pos (-z)]
  have h := one_div_le_one_div_of_le (half_pos he) hb
  simpa [one_div, Real.exp_neg, div_eq_mul_inv] using h

/-- The final differentiated secant power has the exact geometric envelope. -/
theorem sinh_sech_bound (n : ℕ) (z : ℝ) :
    Real.sinh z * (Real.cosh z)⁻¹ ^ (n+1) ≤
      2^n * Real.exp (-(n : ℝ)*z) := by
  calc
    _ ≤ Real.cosh z * (Real.cosh z)⁻¹ ^ (n+1) :=
      mul_le_mul_of_nonneg_right (Real.sinh_lt_cosh z).le (by positivity)
    _ = (Real.cosh z)⁻¹ ^ n :=
      LeanPaper.CentralFactorialSecant.cosh_mul_inv_pow n z
    _ ≤ (2 * Real.exp (-z))^n :=
      pow_le_pow_left₀ (by positivity) (inv_cosh_le z) n
    _ = 2^n * Real.exp (-(n : ℝ)*z) := by
      rw [mul_pow, ← Real.exp_nat_mul]
      congr 2
      ring

/-- The manuscript's accelerated density, with shifted natural index. -/
def density (k : ℕ) (u : ℝ) : ℝ :=
  (4 : ℝ)⁻¹ ^ k * Real.pi * u^(2*k+1) *
    (Real.sinh (Real.pi*u) * (Real.cosh (Real.pi*u))⁻¹^(2*k+2))

theorem density_pos (k : ℕ) {u : ℝ} (hu : 0<u) : 0<density k u := by
  unfold density
  have hs : 0<Real.sinh (Real.pi*u) := Real.sinh_pos_iff.mpr (mul_pos Real.pi_pos hu)
  positivity

lemma coefficient_simplify (k : ℕ) : (4 : ℝ)⁻¹ ^ k * 2^(2*k+1) = 2 := by
  rw [pow_succ, pow_mul]
  norm_num only [show (2 : ℝ)^2=4 by norm_num]
  rw [← mul_assoc, ← mul_pow]
  norm_num

/-- An explicit all-positive-arguments bound proves accelerated decay without
    relying on an interchange of differentiation and an infinite series. -/
theorem density_le_exp (k : ℕ) {u : ℝ} (hu : 0≤u) :
    density k u ≤ 2 * Real.pi * u^(2*k+1) *
      Real.exp (-((2*k+1 : ℕ) : ℝ)*Real.pi*u) := by
  have h := mul_le_mul_of_nonneg_left (sinh_sech_bound (2*k+1) (Real.pi*u))
    (show 0≤(4 : ℝ)⁻¹ ^ k * Real.pi * u^(2*k+1) by positivity)
  change density k u ≤ _ at h
  convert h using 1
  have hc := coefficient_simplify k
  have he : -((2*k+1 : ℕ) : ℝ) * (Real.pi*u) =
      -((2*k+1 : ℕ) : ℝ)*Real.pi*u := by ring
  rw [he]
  calc
    _ = ((4 : ℝ)⁻¹ ^ k * 2^(2*k+1)) * Real.pi * u^(2*k+1) *
        Real.exp (-((2*k+1 : ℕ) : ℝ)*Real.pi*u) := by rw [hc]
    _ = _ := by ring

end LeanPaper.CentralFactorialDecay
