import LeanPaper.Section4ConjugateBounds
import Mathlib.Data.Nat.Choose.Bounds

/-!
# Actual integer factor heights for the separation route in Theorem 4.7

The cofactor of a nonzero integer polynomial has Mahler measure at least one.
Thus Mathlib's Mignotte coefficient bound applies to every genuine divisor,
and Landau's inequality bounds its height in terms of the parent's actual
naive coefficient height. No caller-supplied factor-height assertion is used.
-/

noncomputable section
open Polynomial

namespace LeanPaper.Section4FactorHeight
open Section4Resultant

/-- A nonzero integer polynomial has Mahler measure at least one, because
its actual leading coefficient is a nonzero integer. -/
theorem integer_mahler_one_le (F : ℤ[X]) (hF : F ≠ 0) :
    1 ≤ (complexPolynomial F).mahlerMeasure := by
  apply Polynomial.one_le_mahlerMeasure_of_one_le_norm_leadingCoeff
  have hinj : Function.Injective (algebraMap ℤ ℂ) := Int.cast_injective
  rw [complexPolynomial, Polynomial.leadingCoeff_map_of_injective hinj]
  simpa only [eq_intCast, Complex.norm_intCast] using
    PaperOrder.Section4.proposition_4_2_nonzero_integer_abs_bound
      F.leadingCoeff (Polynomial.leadingCoeff_ne_zero.mpr hF)

/-- Every coefficient of an actual divisor is controlled by the parent's
height, with the explicit binomial and square-root factors. -/
theorem integer_divisor_coefficient_bound (P F : ℤ[X]) (hP : P ≠ 0)
    (hdiv : F ∣ P) (n : ℕ) :
    |(F.coeff n : ℝ)| ≤ (F.natDegree.choose n : ℝ) *
      Real.sqrt ((P.natDegree : ℝ)+1) * naiveHeight P := by
  obtain ⟨D, hD⟩ := hdiv
  have hD0 : D ≠ 0 := by
    intro hz
    apply hP
    rw [hD, hz, mul_zero]
  have hcoeff := Polynomial.norm_coeff_le_choose_mul_mahlerMeasure_of_one_le_mahlerMeasure
    n (complexPolynomial F) (complexPolynomial D) (integer_mahler_one_le D hD0)
  have hprod : complexPolynomial F * complexPolynomial D = complexPolynomial P := by
    simp only [complexPolynomial, hD, Polynomial.map_mul]
  rw [hprod] at hcoeff
  have hinj : Function.Injective (algebraMap ℤ ℂ) := Int.cast_injective
  have hcoeff' : |(F.coeff n : ℝ)| ≤
      (F.natDegree.choose n : ℝ) * (complexPolynomial P).mahlerMeasure := by
    simpa only [complexPolynomial, Polynomial.coeff_map, eq_intCast,
      Complex.norm_intCast, Polynomial.natDegree_map_eq_of_injective hinj] using hcoeff
  have hmahler : (complexPolynomial P).mahlerMeasure ≤
      Real.sqrt ((P.natDegree : ℝ)+1) * naiveHeight P := by
    simpa only [naiveHeight, complexPolynomial,
      Polynomial.natDegree_map_eq_of_injective hinj] using
      (complexPolynomial P).mahlerMeasure_le_sqrt_natDegree_add_one_mul_supNorm
  calc
    _ ≤ (F.natDegree.choose n : ℝ) * (complexPolynomial P).mahlerMeasure := hcoeff'
    _ ≤ (F.natDegree.choose n : ℝ) *
        (Real.sqrt ((P.natDegree : ℝ)+1) * naiveHeight P) :=
      mul_le_mul_of_nonneg_left hmahler (Nat.cast_nonneg _)
    _ = _ := by ring

/-- Uniform naive-height bound for every actual integer divisor. -/
theorem integer_divisor_height_bound (P F : ℤ[X]) (hP : P ≠ 0)
    (hdiv : F ∣ P) :
    naiveHeight F ≤ (2 : ℝ)^P.natDegree *
      Real.sqrt ((P.natDegree : ℝ)+1) * naiveHeight P := by
  obtain ⟨i, hi⟩ := (complexPolynomial F).exists_eq_supNorm
  have hdeg : F.natDegree ≤ P.natDegree := Polynomial.natDegree_le_of_dvd hdiv hP
  have hchoose : (F.natDegree.choose i : ℝ) ≤ (2 : ℝ)^P.natDegree := by
    calc
      _ ≤ (2 : ℝ)^F.natDegree := by exact_mod_cast Nat.choose_le_two_pow F.natDegree i
      _ ≤ _ := pow_le_pow_right₀ (by norm_num) hdeg
  have hheight : 0 ≤ naiveHeight P := (complexPolynomial P).supNorm_nonneg
  calc
    naiveHeight F = |(F.coeff i : ℝ)| := by
      rw [naiveHeight, hi]
      simp only [complexPolynomial, Polynomial.coeff_map, eq_intCast, Complex.norm_intCast]
    _ ≤ (F.natDegree.choose i : ℝ) *
        Real.sqrt ((P.natDegree : ℝ)+1) * naiveHeight P :=
      integer_divisor_coefficient_bound P F hP hdiv i
    _ ≤ (2 : ℝ)^P.natDegree *
        Real.sqrt ((P.natDegree : ℝ)+1) * naiveHeight P := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hchoose (Real.sqrt_nonneg _)) hheight

/-- The finite factor-height estimate for the actual manuscript primitive
polynomial. Its numerical quadratic height rate remains a separate premise. -/
theorem manuscript_divisor_height_bound (p : ManuscriptChain.Real.Parameters)
    (F : ℤ[X]) (hdiv : F ∣ ManuscriptChain.GeneralIrrationality.primitivePolynomial p) :
    naiveHeight F ≤ (2 : ℝ)^p.h * Real.sqrt ((p.h : ℝ)+1) *
      naiveHeight (ManuscriptChain.GeneralIrrationality.primitivePolynomial p) := by
  simpa only [ManuscriptChain.GeneralIrrationality.primitivePolynomial_natDegree] using
    integer_divisor_height_bound (ManuscriptChain.GeneralIrrationality.primitivePolynomial p)
      F (ManuscriptChain.GeneralIrrationality.primitivePolynomial_isPrimitive p).ne_zero hdiv

end LeanPaper.Section4FactorHeight

#print axioms LeanPaper.Section4FactorHeight.integer_mahler_one_le
#print axioms LeanPaper.Section4FactorHeight.integer_divisor_coefficient_bound
#print axioms LeanPaper.Section4FactorHeight.integer_divisor_height_bound
#print axioms LeanPaper.Section4FactorHeight.manuscript_divisor_height_bound
