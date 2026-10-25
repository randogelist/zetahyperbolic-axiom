import LeanPaper.ImportedSection4.Proposition_4_2_Resultant_Product_Barrier

/-!
# Theorem 4.6 — finite integer leading-coefficient barrier

This reconstructs the elementary link between the nonzero integer
leading coefficient c_K, the determinant of the relative pencil B_K,
and the value Q_K(xi). It does NOT establish the numerical growth
rate of det(B_K) or the paper's asymptotic coefficient height.
-/

namespace PaperOrder.Section4

/-- A nonzero integer leading coefficient forces a product at least 1
whenever the spectral determinant identity is available. -/
theorem theorem_4_6_integer_leading_coefficient_barrier
    (c : ℤ) (ξvalue detValue : ℝ)
    (hc : c ≠ 0)
    (hidentity : (((|c| : ℤ) : ℝ)) = |ξvalue| * |detValue|) :
    (1 : ℝ) ≤ |ξvalue| * |detValue| := by
  have hcpos : (0 : ℤ) < |c| := abs_pos.mpr hc
  have hcinteger : (1 : ℤ) ≤ |c| := by omega
  have hcreal : (1 : ℝ) ≤ (((|c| : ℤ) : ℝ)) := by
    exact_mod_cast hcinteger
  calc
    (1 : ℝ) ≤ (((|c| : ℤ) : ℝ)) := hcreal
    _ = |ξvalue| * |detValue| := hidentity

/-- A finite upper bound on the spectral determinant gives a lower
bound on the center evaluation of the integer polynomial. -/
theorem theorem_4_6_integer_evaluation_lower_bound
    (c : ℤ) (ξvalue detValue T : ℝ)
    (hc : c ≠ 0)
    (hidentity : (((|c| : ℤ) : ℝ)) = |ξvalue| * |detValue|)
    (hdet : |detValue| ≤ T) :
    (1 : ℝ) ≤ |ξvalue| * T := by
  calc
    (1 : ℝ) ≤ |ξvalue| * |detValue| :=
      theorem_4_6_integer_leading_coefficient_barrier c ξvalue detValue hc hidentity
    _ ≤ |ξvalue| * T := mul_le_mul_of_nonneg_left hdet (abs_nonneg _)

/-- Explicit reciprocal evaluation lower bound for positive T. -/
theorem theorem_4_6_reciprocal_evaluation_lower_bound
    (c : ℤ) (ξvalue detValue T : ℝ)
    (hc : c ≠ 0)
    (hidentity : (((|c| : ℤ) : ℝ)) = |ξvalue| * |detValue|)
    (hT : 0 < T) (hdet : |detValue| ≤ T) :
    1 / T ≤ |ξvalue| := by
  have h := theorem_4_6_integer_evaluation_lower_bound
    c ξvalue detValue T hc hidentity hdet
  exact (div_le_iff₀ hT).2 (by nlinarith [h])

end PaperOrder.Section4

#print axioms PaperOrder.Section4.theorem_4_6_integer_leading_coefficient_barrier
#print axioms PaperOrder.Section4.theorem_4_6_integer_evaluation_lower_bound
#print axioms PaperOrder.Section4.theorem_4_6_reciprocal_evaluation_lower_bound
