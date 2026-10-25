import LeanPaper.ExternalPi.PiTranscendental
import Mathlib.Algebra.Polynomial.Basis
import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.RingTheory.Algebraic.Basic
import Mathlib.Analysis.Real.Pi.Leibniz

/-!
# The algebraic part of Theorem 6.15(1)

The imported Lindemann proof supplies actual pi-transcendence. Therefore
nonzero rational multiples of all positive powers are transcendental and
the constant together with independently scaled odd powers is linearly
independent. Identifying the odd beta series with its Euler-number/pi
closed form is a distinct analytic obligation, not an assumption hidden
in these unconditional algebraic theorems.
-/
noncomputable section
open Polynomial
namespace LeanPaper.OddPiPowers

/-- Every positive power of the actual real constant pi is transcendental. -/
theorem pi_pow_transcendental (n : ℕ) (hn : 0<n) :
    Transcendental ℚ (Real.pi^n) :=
  LeanFormalizations.Transcendence.transcendental_pi_axiomClean.pow hn

/-- All nonzero rational scalings preserve that transcendence. -/
theorem rational_pi_pow_transcendental (q : ℚ) (hq : q≠0) (n : ℕ) (hn : 0<n) :
    Transcendental ℚ ((q : ℝ)*Real.pi^n) := by
  intro h
  have hqinv : IsAlgebraic ℚ ((q⁻¹ : ℚ) : ℝ) := isAlgebraic_algebraMap q⁻¹
  have hmul := hqinv.mul h
  apply pi_pow_transcendental n hn
  simpa [mul_assoc, hq] using hmul

/-- The entire power sequence of pi is Q-linearly independent. -/
theorem pi_powers_linearIndependent : LinearIndependent ℚ (fun n : ℕ => Real.pi^n) := by
  have h := (Polynomial.basisMonomials ℚ).linearIndependent.map'
    (Polynomial.aeval Real.pi).toLinearMap
    (transcendental_iff_injective.mp
      LeanFormalizations.Transcendence.transcendental_pi_axiomClean)
  simpa [Polynomial.coe_basisMonomials] using h

/-- Constant exponent zero followed by the distinct odd exponents. -/
def oddExponent {N : ℕ} : Option (Fin N) → ℕ
  | none => 0
  | some i => 2*i.val+1

lemma oddExponent_injective (N : ℕ) : Function.Injective (@oddExponent N) := by
  intro i j h
  cases i with
  | none => cases j <;> simp_all [oddExponent]
  | some i =>
      cases j with
      | none => simp_all [oddExponent]
      | some j =>
          have hv : i.val=j.val := by simpa [oddExponent] using h
          simpa using Fin.ext hv

/-- The exact linear-independence shape needed after the beta closed form is identified. -/
theorem constant_and_scaled_odd_powers_linearIndependent (N : ℕ)
    (q : Fin N → ℚ) (hq : ∀ i, q i≠0) :
    LinearIndependent ℚ (fun i : Option (Fin N) =>
      match i with
      | none => (1 : ℝ)
      | some j => (q j : ℝ)*Real.pi^(2*j.val+1)) := by
  let c : Option (Fin N) → ℚˣ := fun i =>
    match i with
    | none => 1
    | some j => Units.mk0 (q j) (hq j)
  have h := (pi_powers_linearIndependent.comp (@oddExponent N)
    (oddExponent_injective N)).units_smul c
  convert h using 1
  funext i
  cases i <;> simp [c, oddExponent, Algebra.smul_def]

/-- Beta at one uses ordered partial sums (the conditionally convergent series). -/
theorem beta_one_ordered_series :
    Filter.Tendsto (fun N => ∑ j ∈ Finset.range N,
      (-1 : ℝ)^j/(2*j+1)) Filter.atTop (nhds (Real.pi/4)) :=
  Real.tendsto_sum_pi_div_four

/-- The identified beta-one value is transcendental, not merely irrational. -/
theorem beta_one_transcendental : Transcendental ℚ (Real.pi/4) := by
  simpa [div_eq_mul_inv, mul_comm] using
    rational_pi_pow_transcendental (1/4) (by norm_num) 1 (by omega)

/-- Any real value of the ordered beta-one series is the transcendental value. -/
theorem beta_one_limit_transcendental (b : ℝ)
    (hb : Filter.Tendsto (fun N => ∑ j ∈ Finset.range N,
      (-1 : ℝ)^j/(2*j+1)) Filter.atTop (nhds b)) :
    b=Real.pi/4 ∧ Transcendental ℚ b := by
  have he := tendsto_nhds_unique hb beta_one_ordered_series
  exact ⟨he, he.symm ▸ beta_one_transcendental⟩

end LeanPaper.OddPiPowers
