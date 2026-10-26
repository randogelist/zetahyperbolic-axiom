import LeanPaper.Section4Resultant

/-! # Exact coefficient-height and resultant upper bounds for Proposition 4.2 -/
noncomputable section
open Polynomial
open scoped BigOperators
namespace LeanPaper.Section4ConjugateBounds
open Section4Resultant

private theorem norm_product_nonneg (P : ℂ[X]) (s : Multiset ℂ) :
    0 ≤ (s.map (fun z => ‖P.eval z‖)).prod := by
  apply Multiset.prod_nonneg
  intro a ha
  obtain ⟨z, _, rfl⟩ := Multiset.mem_map.1 ha
  exact norm_nonneg _

private theorem max_product_nonneg (s : Multiset ℂ) :
    0 ≤ (s.map (fun z => max 1 ‖z‖)).prod := by
  apply Multiset.prod_nonneg
  intro a ha
  obtain ⟨z, _, rfl⟩ := Multiset.mem_map.1 ha
  exact (by norm_num : (0 : ℝ) ≤ 1).trans (le_max_left _ _)

/-- The naive height of an integer polynomial is an actual natural number,
so the denominator-index construction applies to algebraic heights. -/
theorem naiveHeight_is_nat (f : ℤ[X]) : ∃ B : ℕ, naiveHeight f = B := by
  obtain ⟨i, hi⟩ := (complexPolynomial f).exists_eq_supNorm
  refine ⟨(f.coeff i).natAbs, ?_⟩
  change (complexPolynomial f).supNorm = _
  rw [hi]
  simp only [complexPolynomial, Polynomial.coeff_map, eq_intCast, Complex.norm_intCast]
  simpa only [Int.cast_abs] using (Nat.cast_natAbs (α := ℝ) (f.coeff i)).symm

/-- Every nonzero integer polynomial has height at least one. -/
theorem one_le_naiveHeight (f : ℤ[X]) (hf : f ≠ 0) : 1 ≤ naiveHeight f := by
  have hlc : f.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hf
  have hlow := PaperOrder.Section4.proposition_4_2_nonzero_integer_abs_bound f.leadingCoeff hlc
  have hsup := (complexPolynomial f).le_supNorm f.natDegree
  simp only [complexPolynomial, Polynomial.coeff_map, eq_intCast, Complex.norm_intCast,
    Polynomial.coeff_natDegree] at hsup
  exact hlow.trans hsup

/-- The standard naive-height evaluation bound, proved directly on coefficients. -/
theorem polynomial_eval_height_bound (P : ℂ[X]) (z : ℂ) :
    ‖P.eval z‖ ≤ ((P.natDegree : ℝ)+1) * P.supNorm * (max 1 ‖z‖)^P.natDegree := by
  rw [Polynomial.eval_eq_sum_range]
  calc
    ‖∑ i ∈ Finset.range (P.natDegree+1), P.coeff i * z^i‖
        ≤ ∑ i ∈ Finset.range (P.natDegree+1), ‖P.coeff i * z^i‖ := norm_sum_le _ _
    _ ≤ ∑ _i ∈ Finset.range (P.natDegree+1), P.supNorm * (max 1 ‖z‖)^P.natDegree := by
      apply Finset.sum_le_sum
      intro i hi
      rw [norm_mul, norm_pow]
      apply mul_le_mul (P.le_supNorm i) _ (by positivity) P.supNorm_nonneg
      exact (pow_le_pow_left₀ (norm_nonneg z) (le_max_right 1 ‖z‖) i).trans
        (pow_le_pow_right₀ (le_max_left 1 ‖z‖) (by simpa using Nat.le_of_lt_succ (Finset.mem_range.1 hi)))
    _ = ((P.natDegree : ℝ)+1) * P.supNorm * (max 1 ‖z‖)^P.natDegree := by simp; ring

private theorem product_eval_height_bound (P : ℂ[X]) (s : Multiset ℂ) :
    (s.map (fun z => ‖P.eval z‖)).prod ≤
      (((P.natDegree : ℝ)+1)*P.supNorm)^s.card *
        (s.map (fun z => max 1 ‖z‖)).prod^P.natDegree := by
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons z s ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons, pow_succ]
    have hnon : 0 ≤ ((P.natDegree : ℝ)+1)*P.supNorm :=
      mul_nonneg (by positivity) P.supNorm_nonneg
    calc
      ‖P.eval z‖ * (s.map (fun z => ‖P.eval z‖)).prod
          ≤ (((P.natDegree : ℝ)+1)*P.supNorm*(max 1 ‖z‖)^P.natDegree) *
            ((((P.natDegree : ℝ)+1)*P.supNorm)^s.card *
              (s.map (fun z => max 1 ‖z‖)).prod^P.natDegree) :=
        mul_le_mul (polynomial_eval_height_bound P z) ih (norm_product_nonneg P s) (by positivity)
      _ = _ := by rw [mul_pow]; ring

/-- Isolate one conjugate and control all remaining conjugates by the naive
heights and Mahler's inequality. Multiplicities are kept by multiset erase. -/
theorem resultant_upper_bound (f Q : ℤ[X]) (a : ℂ)
    (hfa : a ∈ (complexPolynomial f).roots) :
    |((Polynomial.resultant f Q f.natDegree Q.natDegree : ℤ) : ℝ)| ≤
      ‖(complexPolynomial Q).eval a‖ *
      (((Q.natDegree : ℝ)+1)*naiveHeight Q)^(f.natDegree-1) *
      (Real.sqrt ((f.natDegree : ℝ)+1)*naiveHeight f)^Q.natDegree := by
  classical
  set s := (complexPolynomial f).roots
  have hcard : s.card = f.natDegree := by
    rw [show s = (complexPolynomial f).roots from rfl,
      ← (IsAlgClosed.splits (complexPolynomial f)).natDegree_eq_card_roots]
    exact Polynomial.natDegree_map_eq_of_injective
      (show Function.Injective (algebraMap ℤ ℂ) from Int.cast_injective) _
  have hnat : (complexPolynomial Q).natDegree = Q.natDegree :=
    Polynomial.natDegree_map_eq_of_injective
      (show Function.Injective (algebraMap ℤ ℂ) from Int.cast_injective) _
  have hprod := product_eval_height_bound (complexPolynomial Q) (s.erase a)
  rw [hnat, Multiset.card_erase_of_mem hfa, hcard] at hprod
  have hmax : ((s.erase a).map (fun z => max 1 ‖z‖)).prod ≤
      (s.map (fun z => max 1 ‖z‖)).prod := by
    rw [← Multiset.prod_map_erase (f := fun z : ℂ => max 1 ‖z‖) hfa]
    have hh := max_product_nonneg (s.erase a)
    nlinarith [le_max_left 1 ‖a‖]
  have hmaxnon := max_product_nonneg (s.erase a)
  have hQnon : 0 ≤ naiveHeight Q := (complexPolynomial Q).supNorm_nonneg
  have hmahler := integer_mahler_bound f
  have hmass : |(f.leadingCoeff : ℝ)| *
      ((s.erase a).map (fun z : ℂ => max 1 ‖z‖)).prod ≤
      Real.sqrt ((f.natDegree : ℝ)+1)*naiveHeight f :=
    (mul_le_mul_of_nonneg_left hmax (abs_nonneg _)).trans hmahler
  rw [integer_resultant_abs_product,
    ← Multiset.prod_map_erase (f := fun z => ‖(complexPolynomial Q).eval z‖) hfa]
  calc
    |(f.leadingCoeff : ℝ)|^Q.natDegree *
        (‖(complexPolynomial Q).eval a‖ *
          ((s.erase a).map (fun z => ‖(complexPolynomial Q).eval z‖)).prod)
        ≤ |(f.leadingCoeff : ℝ)|^Q.natDegree *
          (‖(complexPolynomial Q).eval a‖ *
            ((((Q.natDegree : ℝ)+1)*naiveHeight Q)^(f.natDegree-1) *
              ((s.erase a).map (fun z => max 1 ‖z‖)).prod^Q.natDegree)) := by
          gcongr
          simpa only [naiveHeight, Nat.pred_eq_sub_one] using hprod
    _ = ‖(complexPolynomial Q).eval a‖ *
          (((Q.natDegree : ℝ)+1)*naiveHeight Q)^(f.natDegree-1) *
          (|(f.leadingCoeff : ℝ)| *
            ((s.erase a).map (fun z => max 1 ‖z‖)).prod)^Q.natDegree := by
      rw [mul_pow]; ring
    _ ≤ _ := by gcongr

/-- Constructed lower and upper resultant bounds for a single algebraic
approximation. This is the finite arithmetic core used by Proposition 4.2. -/
theorem algebraic_approximation_barrier (f Q : ℤ[X]) (a : ℂ)
    (hf : Irreducible (rationalPolynomial f))
    (hfa : (complexPolynomial f).eval a = 0)
    (hQa : (complexPolynomial Q).eval a ≠ 0) :
    1 ≤ ‖(complexPolynomial Q).eval a‖ *
      (((Q.natDegree : ℝ)+1)*naiveHeight Q)^(f.natDegree-1) *
      (Real.sqrt ((f.natDegree : ℝ)+1)*naiveHeight f)^Q.natDegree := by
  have hcop := coprime_of_irreducible_of_eval_ne_zero f Q hf a hfa hQa
  have hne := integer_resultant_ne_zero f Q hcop
  have hlow := PaperOrder.Section4.proposition_4_2_nonzero_integer_abs_bound _ hne
  have hf0 : complexPolynomial f ≠ 0 := by
    intro hz
    have hfQ0 : rationalPolynomial f = 0 := by
      apply (Polynomial.map_injective (algebraMap ℚ ℂ) (show Function.Injective (algebraMap ℚ ℂ)
        from Rat.cast_injective))
      rw [complexPolynomial_from_rational, hz, Polynomial.map_zero]
    exact hf.ne_zero hfQ0
  exact hlow.trans (resultant_upper_bound f Q a ((Polynomial.mem_roots hf0).2 hfa))

#print axioms algebraic_approximation_barrier

#print axioms polynomial_eval_height_bound
#print axioms resultant_upper_bound
end LeanPaper.Section4ConjugateBounds
