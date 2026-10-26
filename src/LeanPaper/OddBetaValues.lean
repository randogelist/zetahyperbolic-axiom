import LeanPaper.OddPiPowers
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Theorem 6.15(1): actual odd beta values and rational pi powers

For positive odd exponents greater than one, the actual alternating Dirichlet
series is evaluated by the Bernoulli Fourier series at `1/4`. At exponent one
we use the ordered Leibniz series, since unconditional `HasSum` is inappropriate.
Nonvanishing of the rational coefficient follows from an explicit two-term
alternating-series lower bound. No Euler-number evaluation or beta closed form
is assumed. The effective irrationality measure is a separate obligation.
-/
noncomputable section
open scoped Real
open Polynomial Finset Filter
namespace LeanPaper.OddBetaValues

/-- A rational coefficient obtained from the Bernoulli Fourier evaluation. -/
def coefficient (k : ℕ) : ℚ :=
  if k=0 then 1/4 else
    (-1)^(k+1) * 2^(2*k) / ((2*k+1).factorial : ℚ) *
      (Polynomial.bernoulli (2*k+1)).eval (1/4)

lemma sin_odd_pi_half (n : ℕ) :
    Real.sin (2*Real.pi*((2*n+1 : ℕ) : ℝ)*(1/4)) = (-1 : ℝ)^n := by
  have he : 2*Real.pi*((2*n+1 : ℕ) : ℝ)*(1/4) =
      (n : ℝ)*Real.pi+Real.pi/2 := by push_cast; ring
  rw [he, Real.sin_add_pi_div_two, Real.cos_nat_mul_pi]

/-- Evaluation of the absolutely convergent odd beta series for `k>=1`. -/
theorem hasSum_beta_odd {k : ℕ} (hk : k≠0) :
    HasSum (fun n : ℕ => (-1 : ℝ)^n/(2*n+1)^(2*k+1))
      ((coefficient k : ℝ)*Real.pi^(2*k+1)) := by
  let f : ℕ → ℝ := fun n => 1/(n : ℝ)^(2*k+1) *
    Real.sin (2*Real.pi*n*(1/4))
  have hf := hasSum_one_div_nat_pow_mul_sin hk
    (x := (1/4 : ℝ)) (by norm_num : (1/4 : ℝ)∈Set.Icc 0 1)
  have hg : Function.Injective (fun n : ℕ => 2*n+1) := by
    intro a b h
    change 2*a+1=2*b+1 at h
    omega
  have hz : ∀ n, n∉Set.range (fun j : ℕ => 2*j+1) → f n=0 := by
    intro n hn
    have heven : Even n := by
      rcases Nat.even_or_odd n with h | h
      · exact h
      · obtain ⟨m, hm⟩ := h
        exact False.elim (hn ⟨m, by change 2*m+1=n; omega⟩)
    obtain ⟨m, rfl⟩ := heven
    have he : 2*Real.pi*((m+m : ℕ) : ℝ)*(1/4) = (m : ℝ)*Real.pi := by
      push_cast
      ring
    simp only [f, he, Real.sin_nat_mul_pi, mul_zero]
  have h := (hg.hasSum_iff hz).mpr hf
  convert h using 1
  · funext n
    change (-1 : ℝ)^n/(2*n+1)^(2*k+1) = f (2*n+1)
    dsimp only [f]
    rw [sin_odd_pi_half]
    push_cast
    ring
  · have hx : (1/4 : ℝ) = algebraMap ℚ ℝ (1/4 : ℚ) := by norm_num
    rw [hx, Polynomial.eval_map, Polynomial.eval₂_at_apply, mul_pow, pow_succ]
    have hmap : ∀ q : ℚ, algebraMap ℚ ℝ q = (q : ℝ) := fun q => rfl
    simp only [coefficient, if_neg hk, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
      Rat.cast_neg, Rat.cast_one, Rat.cast_natCast, Rat.cast_ofNat, hmap]
    ring

lemma inverse_odd_power_antitone (s : ℕ) :
    Antitone (fun n : ℕ => (1 : ℝ)/(2*n+1)^s) := by
  intro a b hab
  apply one_div_le_one_div_of_le (by positivity)
  gcongr

/-- A genuine numerical lower bound for the evaluated series. -/
theorem coefficient_value_pos {k : ℕ} (hk : k≠0) :
    0 < (coefficient k : ℝ)*Real.pi^(2*k+1) := by
  have hsum := (hasSum_beta_odd hk).tendsto_sum_nat
  have hsum' : Tendsto (fun N => ∑ n ∈ Finset.range N,
      (-1 : ℝ)^n * (1/(2*n+1)^(2*k+1))) atTop
      (nhds ((coefficient k : ℝ)*Real.pi^(2*k+1))) := by
    simpa only [mul_one_div] using hsum
  have hb := (inverse_odd_power_antitone (2*k+1)).alternating_series_le_tendsto hsum' 1
  norm_num [Finset.sum_range_succ] at hb
  have hp : (1 : ℝ) < 3^(2*k+1) := one_lt_pow₀ (by norm_num) (by omega)
  have hlo : (0 : ℝ) < 1-1/3^(2*k+1) := by
    apply sub_pos.mpr
    exact (div_lt_one (by positivity)).mpr hp
  rw [one_div] at hlo
  linarith

/-- The Fourier coefficient is never zero, proved from the actual series. -/
theorem coefficient_ne_zero (k : ℕ) : coefficient k≠0 := by
  by_cases hk : k=0
  · simp [coefficient, hk]
  · intro he
    have hp := coefficient_value_pos hk
    simp [he] at hp

/-- The actual odd beta value: ordinary sum at exponent >1; Leibniz value at 1. -/
def betaOdd (k : ℕ) : ℝ :=
  if k=0 then Real.pi/4 else ∑' n : ℕ, (-1 : ℝ)^n/(2*n+1)^(2*k+1)

theorem betaOdd_eq_coefficient (k : ℕ) :
    betaOdd k = (coefficient k : ℝ)*Real.pi^(2*k+1) := by
  by_cases hk : k=0
  · subst k
    norm_num [betaOdd, coefficient]
    ring
  · simp only [betaOdd, if_neg hk]
    exact (hasSum_beta_odd hk).tsum_eq

/-- This identifies every defined value with the intended ordered Dirichlet series. -/
theorem betaOdd_ordered_series (k : ℕ) :
    Tendsto (fun N => ∑ n ∈ Finset.range N,
      (-1 : ℝ)^n/(2*n+1)^(2*k+1)) atTop (nhds (betaOdd k)) := by
  by_cases hk : k=0
  · subst k
    simpa [betaOdd] using LeanPaper.OddPiPowers.beta_one_ordered_series
  · rw [betaOdd_eq_coefficient]
    exact (hasSum_beta_odd hk).tendsto_sum_nat

/-- Unconditional transcendence of all actual odd Dirichlet beta values. -/
theorem betaOdd_transcendental (k : ℕ) : Transcendental ℚ (betaOdd k) := by
  rw [betaOdd_eq_coefficient]
  exact LeanPaper.OddPiPowers.rational_pi_pow_transcendental
    (coefficient k) (coefficient_ne_zero k) (2*k+1) (by omega)

/-- Rational linear independence of one and every finite initial odd-beta family. -/
theorem betaOdd_linearIndependent (N : ℕ) :
    LinearIndependent ℚ (fun i : Option (Fin N) =>
      match i with
      | none => (1 : ℝ)
      | some j => betaOdd j.val) := by
  convert LeanPaper.OddPiPowers.constant_and_scaled_odd_powers_linearIndependent N
    (fun i => coefficient i.val) (fun i => coefficient_ne_zero i.val) using 1
  funext i
  cases i with
  | none => rfl
  | some j => exact betaOdd_eq_coefficient j.val

end LeanPaper.OddBetaValues
