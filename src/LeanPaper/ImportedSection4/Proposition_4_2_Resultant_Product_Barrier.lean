import Mathlib

/-!
# Proposition 4.2: integer resultant product obstruction

The full paper proposition also needs an integer resultant identity for the
concrete polynomial family and its conjugates, plus uniform height estimates.
Here the finite norm-of-resultant contradiction is proved with the exact
product structure of that identity, with no axioms or hidden hypotheses.
-/

noncomputable section
open scoped BigOperators
namespace PaperOrder.Section4

/-- A nonzero integer has real absolute value at least one. -/
theorem proposition_4_2_nonzero_integer_abs_bound (z : ℤ) (hz : z ≠ 0) :
    (1 : ℝ) ≤ |(z : ℝ)| := by
  have hpos : (0 : ℤ) < |z| := abs_pos.mpr hz
  have hzint : (1 : ℤ) ≤ |z| := by
    omega
  exact_mod_cast hzint

/-- The resultant obstruction: a nonzero integer cannot be equal to a
product whose absolute value is strictly less than one. The parameter
`conjugateEval` may represent the polynomial values at all conjugates;
proving that this product is the integer resultant is a separate step. -/
theorem proposition_4_2_resultant_product_barrier
    {d : ℕ} (z : ℤ) (hz : z ≠ 0)
    (leading : ℝ) (conjugateEval : Fin d → ℝ)
    (hresultant : (z : ℝ) = leading * ∏ i, conjugateEval i)
    (hsmall : |leading| * (∏ i, |conjugateEval i|) < 1) : False := by
  have hlarge : (1 : ℝ) ≤
      |leading| * (∏ i, |conjugateEval i|) := by
    simpa only [hresultant, abs_mul, Finset.abs_prod] using
      proposition_4_2_nonzero_integer_abs_bound z hz
  exact (not_lt_of_ge hlarge) hsmall

end PaperOrder.Section4

#print axioms PaperOrder.Section4.proposition_4_2_resultant_product_barrier
