import Definition_2_1_Order_s_Rational_Moment_Functional
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Tactic

/-!
# Theorem 6.18(1): exact polynomial-quotient disappearance

This file proves the degree threshold for the actual square-pole denominator
and shifted numerator, including the `K=30n, N=3n, M=3` specialization.
It does not infer 2-adic integrality from odd harmonic denominators: residue
weights and the remaining rational constants require their own valuation proof.
-/
noncomputable section
open Polynomial
namespace LeanPaper.DyadicQuotientThreshold
open ManuscriptChain.Real

lemma squareDenominator_monic (N : ℕ) : (D N).Monic := by
  unfold D
  apply Polynomial.monic_prod_of_monic
  intro i hi
  exact Polynomial.monic_X_add_C _

lemma squareDenominator_natDegree (N : ℕ) : (D N).natDegree = N := by
  unfold D
  rw [Polynomial.natDegree_prod]
  · simp only [Polynomial.natDegree_X_add_C, Finset.sum_const,
      Finset.card_range, nsmul_eq_mul, mul_one, Nat.cast_id]
  · intro i hi
    exact (Polynomial.monic_X_add_C _).ne_zero

/-- The literal shifted numerator in Theorem 6.18, before pole cancellation. -/
def shiftedNumerator (N M k m i j : ℕ) : ℚ[X] :=
  (-X) ^ (k+1-m) * D N ^ (2*M) * X ^ (i+j)

/-- Full numerator degree; no generic polynomial degree assumption is supplied. -/
theorem shiftedNumerator_natDegree (N M k m i j : ℕ) :
    (shiftedNumerator N M k m i j).natDegree =
      2*M*N + i+j + (k+1-m) := by
  have hD := (squareDenominator_monic N).ne_zero
  unfold shiftedNumerator
  rw [Polynomial.natDegree_mul, Polynomial.natDegree_mul]
  · simp only [Polynomial.natDegree_pow, Polynomial.natDegree_neg,
      Polynomial.natDegree_X, squareDenominator_natDegree]
    omega
  · exact pow_ne_zero _ (neg_ne_zero.mpr Polynomial.X_ne_zero)
  · exact pow_ne_zero _ hD
  · exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr Polynomial.X_ne_zero))
      (pow_ne_zero _ hD)
  · exact pow_ne_zero _ Polynomial.X_ne_zero

/-- Every entry below the manuscript threshold has zero Euclidean quotient. -/
theorem shifted_quotient_eq_zero (K N M k rmin m r i j : ℕ)
    (hm : rmin ≤ m) (hmk : m ≤ k+1)
    (hi : i < r) (hj : j < r)
    (hthreshold : 2*M*N + 2*r + k-rmin ≤ K) :
    shiftedNumerator N M k m i j / D K = 0 := by
  apply (Polynomial.div_eq_zero_iff (squareDenominator_monic K).ne_zero).mpr
  apply Polynomial.degree_lt_degree
  rw [shiftedNumerator_natDegree, squareDenominator_natDegree]
  omega

/-- Specialized vanishing in the `6n` by `6n` leading principal block. -/
theorem weight_five_six_n_quotient_zero (n i j : ℕ)
    (hi : i < 6*n) (hj : j < 6*n) :
    shiftedNumerator (3*n) 3 2 2 i j / D (30*n) = 0 := by
  apply shifted_quotient_eq_zero (30*n) (3*n) 3 2 2 2 (6*n) i j
    (by omega) (by omega) hi hj
  omega

/-- The exact full-dimension degree bound quoted in Theorem 6.18(2). -/
theorem weight_five_full_numerator_degree_bound (n i j : ℕ)
    (hn : 0 < n) (hi : i < 27*n) (hj : j < 27*n) :
    (shiftedNumerator (3*n) 3 2 2 i j).natDegree ≤ 72*n-1 := by
  rw [shiftedNumerator_natDegree]
  omega

/-- Euclidean division gives the claimed `42n-1` bound on the polynomial part. -/
theorem weight_five_full_quotient_degree_bound (n i j : ℕ)
    (hn : 0 < n) (hi : i < 27*n) (hj : j < 27*n) :
    (shiftedNumerator (3*n) 3 2 2 i j / D (30*n)).natDegree ≤ 42*n-1 := by
  rw [← Polynomial.divByMonic_eq_div _ (squareDenominator_monic (30*n)),
    Polynomial.natDegree_divByMonic _ (squareDenominator_monic (30*n)),
    squareDenominator_natDegree]
  have h := weight_five_full_numerator_degree_bound n i j hn hi hj
  omega

/-- The odd-square change of variables used in Theorem 6.11(2). -/
theorem odd_square_scaling (w : ℚ) (j : ℕ) :
    (4*w-1) + (2*(j : ℚ)+1)^2 = 4*(w+(j : ℚ)*(j+1)) := by ring

/-- The integral coefficient in that substitution is always even. -/
theorem consecutive_product_even (j : ℕ) : Even (j*(j+1)) := by
  exact Nat.even_mul_succ_self j

end LeanPaper.DyadicQuotientThreshold
