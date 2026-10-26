import ProofAdvances.Corollary_3_6_ExactFiniteRank
import Mathlib.Tactic

/-!
# Corollary 3.6: sharp finite-power-sum bound at an extremal atom

This proves the universal finite geometric bound used in the manuscript's
power-sum hierarchy: if a nonnegative finite family is bounded above by
one of its actual values U, then U^r ≤ ∑ u_i^r ≤ h U^r for all r ≥ 0.
When u_i=(root_i - shift)^(-2), this is exactly the finite root-gap
moment estimate, before taking a limit in r.
No limit theorem, uniform asymptotic root clustering, or irrationality
claim is inferred from this finite inequality.
-/

noncomputable section
open scoped BigOperators

namespace PaperAdvances.Corollary3_6_PowerSumExtrema

/-- Both sides of the finite extremal moment inequality for every exponent,
  every dimension, and every choice of an index attaining the maximum. -/
theorem positive_atomic_moment_bounds {h : ℕ} (u : Fin h → ℝ)
    (hu : ∀ i, 0 ≤ u i)
    (j : Fin h) (hj : ∀ i, u i ≤ u j) (r : ℕ) :
    (u j) ^ r ≤ (∑ i : Fin h, u i ^ r) ∧
    (∑ i : Fin h, u i ^ r) ≤ (h : ℝ) * (u j) ^ r := by
  constructor
  · exact Finset.single_le_sum
      (fun i _ => pow_nonneg (hu i) r)
      (Finset.mem_univ j)
  · have hsum : (∑ i : Fin h, u i ^ r) ≤
        (∑ _i : Fin h, (u j) ^ r) := by
      apply Finset.sum_le_sum
      intro i hi
      exact pow_le_pow_left₀ (hu i) (hj i) r
    simpa [Finset.sum_const, nsmul_eq_mul] using hsum

/-- Even-power form used in the PDF's reciprocal-root Stieltjes moments. -/
theorem even_atomic_moment_bounds {h : ℕ} (u : Fin h → ℝ)
    (hu : ∀ i, 0 ≤ u i) (j : Fin h)
    (hj : ∀ i, u i ≤ u j) (r : ℕ) :
    (u j) ^ (2 * r) ≤ (∑ i : Fin h, u i ^ (2 * r)) ∧
    (∑ i : Fin h, u i ^ (2 * r)) ≤ (h : ℝ) * (u j) ^ (2 * r) := by
  exact positive_atomic_moment_bounds u hu j hj (2*r)

end PaperAdvances.Corollary3_6_PowerSumExtrema

#print axioms PaperAdvances.Corollary3_6_PowerSumExtrema.positive_atomic_moment_bounds
#print axioms PaperAdvances.Corollary3_6_PowerSumExtrema.even_atomic_moment_bounds
