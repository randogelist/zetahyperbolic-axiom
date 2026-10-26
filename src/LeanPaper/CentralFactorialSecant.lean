import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic

/-!
# Theorem 6.13: central-factorial hyperbolic secant operator

The operator has one factor `(2r+1)^2 - D^2` for every `r < k`.
Thus `k` here corresponds to manuscript index `k+1`.  The finite
Laplace multiplier also records the missing factor `(-1)^k` in (6.5).
No termwise differentiation of an infinite series is presumed.
-/
noncomputable section
open Real Finset

namespace LeanPaper.CentralFactorialSecant

/-- The reciprocal hyperbolic-cosine power, defined on all real arguments. -/
def sechPower (n : ℕ) (z : ℝ) : ℝ := (Real.cosh z)⁻¹ ^ n

lemma hasDerivAt_sechPower (n : ℕ) (z : ℝ) :
    HasDerivAt (sechPower n)
      (-(n : ℝ) * Real.sinh z * (Real.cosh z)⁻¹ ^ (n+1)) z := by
  have hc := (Real.cosh_pos z).ne'
  have h := ((Real.hasDerivAt_cosh z).inv hc).pow n
  cases n with
  | zero =>
      unfold sechPower
      simpa using hasDerivAt_const z (1 : ℝ)
  | succ n =>
      apply h.congr_deriv
      simp only [Pi.inv_apply, Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel, pow_succ]
      field_simp
      <;> ring

lemma deriv_sechPower (n : ℕ) :
    deriv (sechPower n) = fun z => -(n : ℝ) * Real.sinh z * (Real.cosh z)⁻¹ ^ (n+1) := by
  funext z
  exact (hasDerivAt_sechPower n z).deriv

lemma cosh_mul_inv_pow (n : ℕ) (z : ℝ) :
    Real.cosh z * (Real.cosh z)⁻¹ ^ (n+1) = (Real.cosh z)⁻¹ ^ n := by
  rw [pow_succ]
  field_simp

lemma sinh_sq_mul_inv_pow (n : ℕ) (z : ℝ) :
    Real.sinh z ^ 2 * (Real.cosh z)⁻¹ ^ (n+2) =
      (Real.cosh z)⁻¹ ^ n - (Real.cosh z)⁻¹ ^ (n+2) := by
  have hc := (Real.cosh_pos z).ne'
  have hs : Real.sinh z ^ 2 = Real.cosh z ^ 2 - 1 := by
    linarith [Real.cosh_sq_sub_sinh_sq z]
  rw [hs, pow_add]
  field_simp
  <;> ring

lemma deriv_twice_sechPower (n : ℕ) :
    deriv (deriv (sechPower n)) = fun z =>
      (n : ℝ)^2 * sechPower n z - (n : ℝ) * (n+1) * sechPower (n+2) z := by
  rw [deriv_sechPower]
  funext z
  have h := ((Real.hasDerivAt_sinh z).const_mul (-(n : ℝ))).mul
    (hasDerivAt_sechPower (n+1) z)
  have he : (fun x => -(n : ℝ) * Real.sinh x * (Real.cosh x)⁻¹ ^ (n+1)) =
      (fun x => -(n : ℝ) * Real.sinh x * sechPower (n+1) x) := rfl
  rw [he]
  calc
    _ = _ := h.deriv
    _ = _ := by
      simp only [sechPower, Nat.cast_add, Nat.cast_one]
      have h₁ := cosh_mul_inv_pow n z
      have h₂ := sinh_sq_mul_inv_pow n z
      simp only [show n+1+1 = n+2 by omega] at *
      nlinarith

/-- Product of the first `k` central-factorial differential factors. -/
def centralOperator : ℕ → (ℝ → ℝ) → (ℝ → ℝ)
  | 0, f => f
  | k+1, f => fun z => ((2*k+1 : ℕ) : ℝ)^2 * centralOperator k f z -
      deriv (deriv (centralOperator k f)) z

/-- The hyperbolic secant input has normalization `1/(2 cosh z)`. -/
def halfSech (z : ℝ) : ℝ := (1/2 : ℝ) * sechPower 1 z

lemma deriv_const_mul_sech (a : ℝ) (n : ℕ) :
    deriv (fun z => a * sechPower n z) = fun z => a * deriv (sechPower n) z := by
  funext z
  exact deriv_const_mul a (hasDerivAt_sechPower n z).differentiableAt

lemma deriv_twice_const_mul_sech (a : ℝ) (n : ℕ) :
    deriv (deriv (fun z => a * sechPower n z)) =
      fun z => a * ((n : ℝ)^2 * sechPower n z -
        (n : ℝ) * (n+1) * sechPower (n+2) z) := by
  rw [deriv_const_mul_sech]
  have hd : Differentiable ℝ (deriv (sechPower n)) := by
    rw [deriv_sechPower]
    intro z
    exact ((Real.hasDerivAt_sinh z).const_mul (-(n : ℝ))).differentiableAt.mul
      (hasDerivAt_sechPower (n+1) z).differentiableAt
  funext z
  rw [deriv_const_mul a (hd z), deriv_twice_sechPower]

/-- The all-order central-factorial closed form, before the last derivative. -/
theorem centralOperator_halfSech (k : ℕ) :
    centralOperator k halfSech =
      fun z => ((2*k).factorial : ℝ) / 2 * sechPower (2*k+1) z := by
  induction k with
  | zero =>
      funext z
      simp [centralOperator, halfSech]
  | succ k ih =>
      simp only [centralOperator, ih, deriv_twice_const_mul_sech]
      funext z
      have he₁ : 2*(k+1) = (2*k+1)+1 := by omega
      have he₂ : 2*(k+1)+1 = (2*k+1)+2 := by omega
      rw [he₂, he₁, Nat.factorial_succ, Nat.factorial_succ]
      push_cast
      ring

/-- Negative final derivative is the positive closed form in Theorem 6.13(1). -/
theorem central_secant_derivative (k : ℕ) (z : ℝ) :
    -deriv (centralOperator k halfSech) z =
      ((2*k+1).factorial : ℝ) / 2 * Real.sinh z * sechPower (2*k+2) z := by
  rw [centralOperator_halfSech, deriv_const_mul_sech, deriv_sechPower]
  rw [Nat.factorial_succ]
  simp only [sechPower, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  ring

/-- Strict positivity is unconditional at every positive real argument. -/
theorem central_secant_positive (k : ℕ) {z : ℝ} (hz : 0 < z) :
    0 < -deriv (centralOperator k halfSech) z := by
  rw [central_secant_derivative]
  have hs : 0 < Real.sinh z := Real.sinh_pos_iff.mpr hz
  have hf : 0 < ((2*k+1).factorial : ℝ) := by positivity
  unfold sechPower
  positivity

/-- Exact eigenvalue multiplier of the product operator on an exponential mode. -/
def modeMultiplier (k : ℕ) (a : ℝ) : ℝ :=
  ∏ r ∈ Finset.range k, (((2*r+1 : ℕ) : ℝ)^2 - a^2)

/-- Every one of the first `k` odd Laplace modes is annihilated. -/
theorem modeMultiplier_zero {k l : ℕ} (hl : l < k) :
    modeMultiplier k ((2*l+1 : ℕ) : ℝ) = 0 := by
  apply Finset.prod_eq_zero (Finset.mem_range.mpr hl)
  simp

lemma deriv_scaled_exp (a c : ℝ) :
    deriv (fun z : ℝ => c * Real.exp (-a*z)) =
      fun z => (-a*c)*Real.exp (-a*z) := by
  funext z
  have h := (((hasDerivAt_id z).const_mul (-a)).exp).const_mul c
  convert h.deriv using 1 <;> simp only [id_eq] <;> ring

lemma deriv_twice_scaled_exp (a c : ℝ) :
    deriv (deriv (fun z : ℝ => c * Real.exp (-a*z))) =
      fun z => (a^2*c)*Real.exp (-a*z) := by
  rw [deriv_scaled_exp, deriv_scaled_exp]
  funext z
  ring

/-- The finite multiplier is genuinely the differential operator's eigenvalue. -/
theorem centralOperator_exp (k : ℕ) (a : ℝ) :
    centralOperator k (fun z => Real.exp (-a*z)) =
      fun z => modeMultiplier k a * Real.exp (-a*z) := by
  induction k with
  | zero => simp [centralOperator, modeMultiplier]
  | succ k ih =>
      simp only [centralOperator, ih, deriv_twice_scaled_exp]
      funext z
      simp only [modeMultiplier, Finset.prod_range_succ]
      ring

/-- The first `k` actual Laplace modes vanish as functions under the operator. -/
theorem centralOperator_annihilates {k l : ℕ} (hl : l<k) :
    centralOperator k (fun z => Real.exp (-((2*l+1 : ℕ) : ℝ)*z)) = 0 := by
  rw [centralOperator_exp, modeMultiplier_zero hl]
  funext z
  simp

/-- Reversing all factors introduces the sign missing in printed equation (6.5). -/
theorem modeMultiplier_reversed (k : ℕ) (a : ℝ) :
    modeMultiplier k a = (-1 : ℝ)^k *
      ∏ r ∈ Finset.range k, (a^2 - ((2*r+1 : ℕ) : ℝ)^2) := by
  unfold modeMultiplier
  have he : (-1 : ℝ)^k = ∏ _r ∈ Finset.range k, (-1 : ℝ) := by simp
  rw [he, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro r hr
  ring

/-- At manuscript k=2 the printed reversal changes the sign of the first surviving mode. -/
theorem first_surviving_mode_sign : modeMultiplier 1 3 = -8 ∧
    (∏ r ∈ Finset.range 1, ((3 : ℝ)^2 - ((2*r+1 : ℕ) : ℝ)^2)) = 8 := by
  norm_num [modeMultiplier]

end LeanPaper.CentralFactorialSecant
