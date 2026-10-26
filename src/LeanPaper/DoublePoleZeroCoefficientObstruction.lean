import Mathlib

/-!
# Theorem 5.7: the printed double-pole coefficient at zero

At n=1 the printed numerator is `(6!)^2 t^5` and the common
denominator is `prod_{k=0}^6 (t+k)^2`. The numerator has a factor t^5,
so a valid double-pole decomposition must have zero t^(-2) coefficient.
The printed formula instead gives A_(1,0)=1.

The certificate below rejects the exact cleared polynomial identity for
every possible choice of simple-pole coefficients. It does not refute the
separate conditional determinant valuation statement: no integer relation
between zeta(5) and zeta(6) is supplied or presumed.
-/

noncomputable section
open scoped BigOperators
open Polynomial

namespace LeanPaper.DoublePoleZeroCoefficientObstruction

def numeratorOne : ℚ[X] := C ((Nat.factorial 6 : ℚ)^2) * X^5

def poleCofactorOne (k : Fin 7) : ℚ[X] :=
  ∏ j : Fin 7, if j = k then 1 else (X+C (j.val : ℚ))^2

/-- Multiplication of a double/simple-pole expansion by its common
denominator has this exact numerator. -/
def clearedPartialFractionNumerator (A B : Fin 7 → ℚ) : ℚ[X] :=
  ∑ k : Fin 7, (C (A k)+C (B k)*(X+C (k.val : ℚ))) * poleCofactorOne k

theorem numeratorOne_divisible_by_zero_pole : X^2 ∣ numeratorOne := by
  refine ⟨C ((Nat.factorial 6 : ℚ)^2)*X^3, ?_⟩
  unfold numeratorOne
  ring

theorem poleCofactorOne_at_zero (k : Fin 7) :
    (poleCofactorOne k).eval 0 = if k = 0 then (518400 : ℚ) else 0 := by
  simp only [poleCofactorOne, Polynomial.eval_prod, apply_ite,
    Polynomial.eval_one, Polynomial.eval_pow, Polynomial.eval_add,
    Polynomial.eval_X, Polynomial.eval_C, zero_add]
  by_cases hk : k = 0
  · subst k
    norm_num [Fin.prod_univ_succ, Fin.ext_iff]
  · rw [if_neg hk]
    apply Finset.prod_eq_zero (Finset.mem_univ (0 : Fin 7))
    simp [Ne.symm hk]

/-- Every valid cleared decomposition of the actual n=1 rational function
has zero double-pole coefficient at the zero node. -/
theorem zero_coefficient_of_cleared_identity (A B : Fin 7 → ℚ)
    (h : numeratorOne = clearedPartialFractionNumerator A B) : A 0 = 0 := by
  have he := congrArg (fun p : ℚ[X] => p.eval 0) h
  simp [numeratorOne, clearedPartialFractionNumerator,
    Polynomial.eval_finsetSum, poleCofactorOne_at_zero, mul_ite] at he
  linarith

/-- The literal printed formula (5.8) at n=1, with 1!=1. -/
def printedAOne (k : Fin 7) : ℚ :=
  (-1 : ℚ)^k.val * (Nat.choose 6 k.val : ℚ)^2 *
    (Nat.choose (1+k.val) k.val : ℚ)^5

theorem printed_zero_coefficient : printedAOne 0 = 1 := by
  norm_num [printedAOne]

/-- No adjustment of the simple-pole coefficients repairs the printed
double-pole coefficients for the actual n=1 numerator. -/
theorem printed_cleared_partial_fraction_impossible (B : Fin 7 → ℚ) :
    numeratorOne ≠ clearedPartialFractionNumerator printedAOne B := by
  intro h
  have he := zero_coefficient_of_cleared_identity printedAOne B h
  rw [printed_zero_coefficient] at he
  norm_num at he

end LeanPaper.DoublePoleZeroCoefficientObstruction

#print axioms LeanPaper.DoublePoleZeroCoefficientObstruction.zero_coefficient_of_cleared_identity
#print axioms LeanPaper.DoublePoleZeroCoefficientObstruction.printed_cleared_partial_fraction_impossible
