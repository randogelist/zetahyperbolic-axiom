import Mathlib

/-!
# Theorem 5.1: finite six-factor off-diagonal Beukers kernel

The positive double integral in the manuscript expands into finite six-term
rational expressions before the infinite n-sum. This module isolates the
exact divided-difference algebra for these expressions, independently of
the analytic interchange of infinite summation and integration.

It does NOT assert that the two-variable Beukers measure is integrated,
nor that the off-diagonal infinite moment is already rational.
-/

noncomputable section
open scoped BigOperators

namespace LeanPaper.BeukersOffDiagonalKernel

/-- The six rational factors occurring after the Mellin product integral
in the weight-seven Beukers moment expansion. -/
def sixKernel (a b : ℚ) : ℚ :=
  1 / (a * b ^ 6) +
  1 / (a ^ 2 * b ^ 5) +
  1 / (a ^ 3 * b ^ 4) +
  1 / (a ^ 4 * b ^ 3) +
  1 / (a ^ 5 * b ^ 2) +
  1 / (a ^ 6 * b)

/-- This explicit expression is the j=0,...,5 finite Beukers sum. -/
theorem sixKernel_eq_sum (a b : ℚ) :
    sixKernel a b =
      ∑ j ∈ Finset.range 6, 1 / (a ^ (j + 1) * b ^ (6 - j)) := by
  simp [sixKernel, Finset.sum_range_succ]
  ring

/-- The key finite difference: a six-term positive kernel becomes a
difference of reciprocal sixth powers, divided by the index gap. -/
theorem divided_difference (a b : ℚ) (ha : a ≠ 0) (hb : b ≠ 0) :
    (b - a) * sixKernel a b = 1 / a ^ 6 - 1 / b ^ 6 := by
  unfold sixKernel
  field_simp [ha, hb]
  ring

/-- The gap b-a depends only on the row indices r,t, not on n. -/
theorem shifted_divided_difference (r t n : ℕ) :
    ((t : ℚ) - (r : ℚ)) *
      sixKernel ((r + n + 1 : ℕ) : ℚ) ((t + n + 1 : ℕ) : ℚ) =
      1 / (((r + n + 1 : ℕ) : ℚ) ^ 6) -
      1 / (((t + n + 1 : ℕ) : ℚ) ^ 6) := by
  have ha : (((r + n + 1 : ℕ) : ℚ)) ≠ 0 := by positivity
  have hb : (((t + n + 1 : ℕ) : ℚ)) ≠ 0 := by positivity
  have h := divided_difference
    ((r + n + 1 : ℕ) : ℚ) ((t + n + 1 : ℕ) : ℚ) ha hb
  convert h using 1 <;> push_cast <;> ring

/-- The finite n-truncation needed before any analytic exchange of sums. -/
def finiteKernelSum (r t N : ℕ) : ℚ :=
  ∑ n ∈ Finset.range N,
    sixKernel ((r + n + 1 : ℕ) : ℚ) ((t + n + 1 : ℕ) : ℚ)

/-- Exact finite-sum consequence, without an unproved infinite-series step. -/
theorem finiteKernelSum_divided_difference (r t N : ℕ) :
    ((t : ℚ) - (r : ℚ)) * finiteKernelSum r t N =
      ∑ n ∈ Finset.range N,
        (1 / (((r + n + 1 : ℕ) : ℚ) ^ 6) -
         1 / (((t + n + 1 : ℕ) : ℚ) ^ 6)) := by
  unfold finiteKernelSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  exact shifted_divided_difference r t n

#print axioms sixKernel_eq_sum
#print axioms divided_difference
#print axioms shifted_divided_difference
#print axioms finiteKernelSum_divided_difference

end LeanPaper.BeukersOffDiagonalKernel
