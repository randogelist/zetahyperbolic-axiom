import LeanPaper.BeukersDensityActual
import Mathlib.Tactic

/-!
# Theorem 5.2(2): actual ζ(7) Beukers modes and Krein polarization

This first layer proves the genuine monomial-moment Krein identity for
Theorem 5.1's actual two-variable Beukers measure. The Mellin channels
are the integrals of x^(r+m) (-log x)^ν.

The full printed statement for any f in L²(0,1) requires additional
finite-polynomial bilinearity and L² continuity.
-/

noncomputable section
open scoped BigOperators
open MeasureTheory Set

namespace ManuscriptChain.Beukers

def kreinChannel (r m ν : ℕ) : ℝ :=
  (ν.factorial : ℝ) / (((r + m : ℕ) : ℝ) + 1) ^ (ν + 1)

def kreinSixPairing (a b : ℕ → ℝ) : ℝ :=
  (1 / 720 : ℝ) * ∑ ν : Fin 6,
    (Nat.choose 5 ν.val : ℝ) * a ν.val * b (5 - ν.val)

def kreinSignedPairing (a b : ℕ → ℝ) : ℝ :=
  (1 / 1440 : ℝ) * ∑ ν : Fin 3,
    (Nat.choose 5 ν.val : ℝ) *
      ((a ν.val + a (5 - ν.val)) * (b ν.val + b (5 - ν.val)) -
       (a ν.val - a (5 - ν.val)) * (b ν.val - b (5 - ν.val)))

theorem kreinSix_eq_signed (a b : ℕ → ℝ) :
    kreinSixPairing a b = kreinSignedPairing a b := by
  unfold kreinSixPairing kreinSignedPairing
  norm_num [Fin.sum_univ_succ, Nat.choose] <;> ring

private theorem binomial_factorial_5 (ν : Fin 6) :
    (Nat.choose 5 ν.val : ℝ) * (ν.val.factorial : ℝ) *
      ((5 - ν.val).factorial : ℝ) = 120 := by
  fin_cases ν <;> norm_num [Nat.choose, Nat.factorial]

private theorem channel_term_eq (r t m : ℕ) (ν : Fin 6) :
    (Nat.choose 5 ν.val : ℝ) * kreinChannel r m ν.val *
      kreinChannel t m (5 - ν.val) =
      120 * (1 / (((r + m : ℕ) : ℝ) + 1) ^ (ν.val + 1) *
        (1 / (((t + m : ℕ) : ℝ) + 1) ^ (5 - ν.val + 1))) := by
  simp only [kreinChannel, div_eq_mul_inv, one_div]
  calc
    _ = ((Nat.choose 5 ν.val : ℝ) * (ν.val.factorial : ℝ) *
          ((5 - ν.val).factorial : ℝ)) *
          (((((r + m : ℕ) : ℝ) + 1) ^ (ν.val + 1))⁻¹ *
           ((((t + m : ℕ) : ℝ) + 1) ^ (5 - ν.val + 1))⁻¹) := by ring
    _ = _ := by rw [binomial_factorial_5]; ring

theorem integral_momentTerm_eq_kreinSix (r t m : ℕ) :
    (∫ z, momentTerm r t m z ∂squareMeasure) =
      kreinSixPairing (kreinChannel r m) (kreinChannel t m) := by
  rw [integral_momentTerm]
  unfold kreinSixPairing
  simp_rw [channel_term_eq r t m]
  rw [← Finset.mul_sum]
  ring

theorem actual_monomial_krein_bilinear (r t : ℕ) :
    (∫ z, z.1 ^ r * z.2 ^ t * density z ∂squareMeasure) =
      ∑' m : ℕ, kreinSignedPairing (kreinChannel r m) (kreinChannel t m) := by
  calc
    _ = ∑' m : ℕ, ∫ z, momentTerm r t m z ∂squareMeasure := by
      rw [integral_density_moment_series]
      apply tsum_congr
      intro m
      exact (integral_momentTerm r t m).symm
    _ = ∑' m : ℕ, kreinSignedPairing (kreinChannel r m) (kreinChannel t m) := by
      apply tsum_congr
      intro m
      rw [integral_momentTerm_eq_kreinSix, kreinSix_eq_signed]

theorem actual_monomial_krein_quadratic (r : ℕ) :
    (∫ z, z.1 ^ r * z.2 ^ r * density z ∂squareMeasure) =
      ∑' m : ℕ, (1 / 1440 : ℝ) * ∑ ν : Fin 3,
        (Nat.choose 5 ν.val : ℝ) *
         ((kreinChannel r m ν.val + kreinChannel r m (5 - ν.val)) ^ 2 -
          (kreinChannel r m ν.val - kreinChannel r m (5 - ν.val)) ^ 2) := by
  rw [actual_monomial_krein_bilinear]
  apply tsum_congr
  intro m
  simp only [kreinSignedPairing, pow_two]

end ManuscriptChain.Beukers
