import LeanPaper.Section2RatFuncTranslation
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-! The normalized analytic derivative in Lemma 2.3 for every admissible
finite rational linear combination of simple poles, not merely one generator. -/
noncomputable section
open scoped BigOperators
open Polynomial
namespace LeanPaper.Section2DifferenceDerivative
open Section2TauLinear Section2RatFuncTranslation

def poleSpan (s : Finset ℤ) (c : ℤ → ℚ) (x : ℝ) : ℝ :=
  ∑ r ∈ s, (c r : ℝ) * (x-(r : ℝ))⁻¹

theorem normalized_even_derivative_span (k : ℕ) (s : Finset ℤ) (c : ℤ → ℚ)
    (hs : ∀ r ∈ s, r ≠ 0) :
    iteratedDeriv (2*k) (poleSpan s c) 0 / ((2*k).factorial : ℝ) =
      ∑ r ∈ s, (c r : ℝ) * (-((r : ℝ)^(2*k+1))⁻¹) := by
  have hr (r : ℤ) (hmem : r ∈ s) :
      ContDiffAt ℝ (2*k) (fun x : ℝ => (c r : ℝ) * (x-(r : ℝ))⁻¹) 0 := by
    have hzero : (0 : ℝ) - (r : ℝ) ≠ 0 := by
      have hh : (r : ℝ) ≠ 0 := by exact_mod_cast hs r hmem
      simpa using neg_ne_zero.mpr hh
    exact ((contDiffAt_id.sub contDiffAt_const).inv hzero).const_mul (c r : ℝ)
  unfold poleSpan
  rw [iteratedDeriv_fun_sum hr, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro r hmem
  rw [iteratedDeriv_const_mul_field, mul_div_assoc, iteratedDeriv_eq_iterate,
    pole_even_derivative]

theorem tau_difference_span_derivative (k : ℕ) (s : Finset ℤ) (c : ℤ → ℚ)
    (hs : ∀ r ∈ s, r ≠ 0 ∧ r ≠ 1) (x : ℝ) :
    ((tau k (translation (∑ r ∈ s, c r • pole r) -
      ∑ r ∈ s, c r • pole r)).map (algebraMap ℚ ℝ)).eval x =
        iteratedDeriv (2*k) (poleSpan s c) 0 / ((2*k).factorial : ℝ) := by
  rw [tau_difference_span k s c hs,
    normalized_even_derivative_span k s c (fun r hr => (hs r hr).1)]
  simp

end LeanPaper.Section2DifferenceDerivative
