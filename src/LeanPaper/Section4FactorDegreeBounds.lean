import LeanPaper.Section4Resultant

/-!
# Proposition 4.8: logarithmic degree bounds for actual polynomial factors

The finite product inequalities are applied to the roots of an actual complex
polynomial, counted with multiplicity. The factorization identity is obtained
from algebraic closedness, rather than passed in as a proof field. The final
theorems apply to genuine integer-polynomial divisors of the manuscript's
primitive polynomial and obtain their root separation from its exact norm disk.

The numerical exponential norm estimate of Theorem 4.4 is still an explicit
input. An upper cluster radius is used only for the upper degree bound; it is
never inferred from the lower root-separation bound.
-/

noncomputable section
open Polynomial
open scoped Matrix.Norms.L2Operator

namespace LeanPaper.Section4FactorDegreeBounds

private theorem root_product_lower (s : Multiset ℂ) (z : ℂ) (δ : ℝ)
    (hδ : 0 ≤ δ) (hsep : ∀ r ∈ s, δ ≤ ‖z-r‖) :
    δ ^ s.card ≤ ‖(s.map (fun r => z-r)).prod‖ := by
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons r s ih =>
    have hr := hsep r (by simp)
    have hs : ∀ t ∈ s, δ ≤ ‖z-t‖ := fun t ht => hsep t (by simp [ht])
    have hi := ih hs
    simpa only [Multiset.card_cons, pow_succ, Multiset.map_cons,
      Multiset.prod_cons, norm_mul, mul_comm] using
      mul_le_mul hr hi (pow_nonneg hδ _) (norm_nonneg _)

private theorem root_product_upper (s : Multiset ℂ) (z : ℂ) (η : ℝ)
    (hη : 0 ≤ η) (hcluster : ∀ r ∈ s, ‖z-r‖ ≤ η) :
    ‖(s.map (fun r => z-r)).prod‖ ≤ η ^ s.card := by
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons r s ih =>
    have hr := hcluster r (by simp)
    have hs : ∀ t ∈ s, ‖z-t‖ ≤ η := fun t ht => hcluster t (by simp [ht])
    have hi := ih hs
    simpa only [Multiset.card_cons, pow_succ, Multiset.map_cons,
      Multiset.prod_cons, norm_mul, mul_comm] using
      mul_le_mul hr hi (norm_nonneg _) hη

/-- Lower separation of every actual root gives the exact logarithmic lower
degree bound. In particular, nonvanishing at the center is derived. -/
theorem polynomial_log_degree_lower (F : ℂ[X]) (z : ℂ) (a : ℝ)
    (hF : F ≠ 0) (ha : 0 < a)
    (hsep : ∀ r ∈ F.roots, Real.exp (-a) ≤ ‖z-r‖) :
    F.eval z ≠ 0 ∧
      (Real.log ‖F.leadingCoeff‖ - Real.log ‖F.eval z‖) / a ≤
        (F.natDegree : ℝ) := by
  have hs := IsAlgClosed.splits F
  have hp := root_product_lower F.roots z (Real.exp (-a))
    (Real.exp_pos _).le hsep
  rw [← hs.natDegree_eq_card_roots, ← Real.exp_nat_mul] at hp
  have hlc : 0 < ‖F.leadingCoeff‖ :=
    norm_pos_iff.mpr (Polynomial.leadingCoeff_ne_zero.mpr hF)
  have hbound : ‖F.leadingCoeff‖ * Real.exp ((F.natDegree : ℝ) * (-a)) ≤
      ‖F.eval z‖ := by
    calc
      _ ≤ ‖F.leadingCoeff‖ * ‖(F.roots.map (fun r => z-r)).prod‖ :=
        mul_le_mul_of_nonneg_left hp hlc.le
      _ = _ := by rw [hs.eval_eq_prod_roots z, norm_mul]
  have hv : 0 < ‖F.eval z‖ :=
    (mul_pos hlc (Real.exp_pos _)).trans_le hbound
  refine ⟨norm_pos_iff.mp hv, (div_le_iff₀ ha).2 ?_⟩
  have hlog := Real.log_le_log (mul_pos hlc (Real.exp_pos _)) hbound
  rw [Real.log_mul hlc.ne' (Real.exp_ne_zero _), Real.log_exp] at hlog
  nlinarith

/-- An upper cluster bound gives the complementary upper degree bound.
Center nonvanishing is indispensable for the logarithm and is explicit. -/
theorem polynomial_log_degree_upper (F : ℂ[X]) (z : ℂ) (b : ℝ)
    (hF : F ≠ 0) (hb : 0 < b) (hv : F.eval z ≠ 0)
    (hcluster : ∀ r ∈ F.roots, ‖z-r‖ ≤ Real.exp (-b)) :
    (F.natDegree : ℝ) ≤
      (Real.log ‖F.leadingCoeff‖ - Real.log ‖F.eval z‖) / b := by
  have hs := IsAlgClosed.splits F
  have hp := root_product_upper F.roots z (Real.exp (-b))
    (Real.exp_pos _).le hcluster
  rw [← hs.natDegree_eq_card_roots, ← Real.exp_nat_mul] at hp
  have hlc : 0 < ‖F.leadingCoeff‖ :=
    norm_pos_iff.mpr (Polynomial.leadingCoeff_ne_zero.mpr hF)
  have hbound : ‖F.eval z‖ ≤
      ‖F.leadingCoeff‖ * Real.exp ((F.natDegree : ℝ) * (-b)) := by
    calc
      _ = ‖F.leadingCoeff‖ * ‖(F.roots.map (fun r => z-r)).prod‖ := by
        rw [hs.eval_eq_prod_roots z, norm_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_left hp hlc.le
  have hlog := Real.log_le_log (norm_pos_iff.mpr hv) hbound
  rw [Real.log_mul hlc.ne' (Real.exp_ne_zero _), Real.log_exp] at hlog
  apply (le_div_iff₀ hb).2
  nlinarith

open ManuscriptChain
open Section4Resultant OperatorNormDisk PrimitiveNormDisk

/-- Roots of an actual integer divisor inherit the actual primitive
polynomial's exact inverse-operator-norm separation. -/
theorem manuscript_divisor_root_separation
    (p : Real.Parameters) (hp : Real.Admissible p) (F : ℤ[X])
    (hdiv : F ∣ GeneralIrrationality.primitivePolynomial p)
    (r : ℂ) (hr : r ∈ (complexPolynomial F).roots) :
    1 / ‖whitened (Real.manuscriptPencil p)‖ ≤
      ‖(Real.zeta p.weight : ℂ) - r‖ := by
  have hroot : (complexPolynomial F).eval r = 0 :=
    (Polynomial.mem_roots (Polynomial.ne_zero_of_mem_roots hr)).mp hr
  obtain ⟨D, hD⟩ := hdiv
  have hrootP : (GeneralIrrationality.primitivePolynomial p).eval₂
      (algebraMap ℤ ℂ) r = 0 := by
    rw [hD, Polynomial.eval₂_mul]
    have hFroot : F.eval₂ (algebraMap ℤ ℂ) r = 0 := by
      simpa only [complexPolynomial, Polynomial.eval_map] using hroot
    rw [hFroot, zero_mul]
  simpa only [norm_sub_rev] using primitive_root_distance p hp r hrootP

/-- The lower degree bound in 4.8(2), for genuine divisors of the actual
manuscript polynomial. Only the quantitative norm estimate remains an input. -/
theorem manuscript_divisor_log_degree_lower
    (p : Real.Parameters) (hp : Real.Admissible p) (F : ℤ[X]) (hF : F ≠ 0)
    (hdiv : F ∣ GeneralIrrationality.primitivePolynomial p)
    (a : ℝ) (ha : 0 < a)
    (hnorm : ‖whitened (Real.manuscriptPencil p)‖ ≤ Real.exp a) :
    (complexPolynomial F).eval (Real.zeta p.weight : ℂ) ≠ 0 ∧
    (Real.log |(F.leadingCoeff : ℝ)| -
      Real.log ‖(complexPolynomial F).eval (Real.zeta p.weight : ℂ)‖) / a ≤
      (F.natDegree : ℝ) ∧
    -Real.log ‖(complexPolynomial F).eval (Real.zeta p.weight : ℂ)‖ / a ≤
      (F.natDegree : ℝ) := by
  have hinj : Function.Injective (algebraMap ℤ ℂ) := Int.cast_injective
  have hFc : complexPolynomial F ≠ 0 := by
    intro hz
    exact hF ((Polynomial.map_injective _ hinj) (by simpa [complexPolynomial] using hz))
  have hpos : 0 < ‖whitened (Real.manuscriptPencil p)‖ :=
    one_div_pos.mp (primitive_exact_norm_disk p hp).1
  have hsep : ∀ r ∈ (complexPolynomial F).roots,
      Real.exp (-a) ≤ ‖(Real.zeta p.weight : ℂ)-r‖ := by
    intro r hr
    calc
      Real.exp (-a) = 1 / Real.exp a := by rw [Real.exp_neg, one_div]
      _ ≤ 1 / ‖whitened (Real.manuscriptPencil p)‖ :=
        one_div_le_one_div_of_le hpos hnorm
      _ ≤ _ := manuscript_divisor_root_separation p hp F hdiv r hr
  obtain ⟨hv, hdegree⟩ := polynomial_log_degree_lower
    (complexPolynomial F) (Real.zeta p.weight : ℂ) a hFc ha hsep
  have hnormlc : ‖(complexPolynomial F).leadingCoeff‖ = |(F.leadingCoeff : ℝ)| := by
    rw [complexPolynomial, Polynomial.leadingCoeff_map_of_injective hinj]
    simp only [eq_intCast, Complex.norm_intCast]
  have hdeg : (complexPolynomial F).natDegree = F.natDegree :=
    Polynomial.natDegree_map_eq_of_injective hinj _
  rw [hnormlc, hdeg] at hdegree
  refine ⟨hv, hdegree, le_trans ?_ hdegree⟩
  apply div_le_div_of_nonneg_right _ ha.le
  have hlc : 0 ≤ Real.log |(F.leadingCoeff : ℝ)| :=
    Real.log_nonneg (PaperOrder.Section4.proposition_4_2_nonzero_integer_abs_bound
      F.leadingCoeff (Polynomial.leadingCoeff_ne_zero.mpr hF))
  linarith

/-- The upper degree bound in 4.8(2), retaining a separate actual upper
closeness hypothesis on every root of the divisor. -/
theorem manuscript_divisor_log_degree_upper
    (p : Real.Parameters) (hp : Real.Admissible p) (F : ℤ[X]) (hF : F ≠ 0)
    (hdiv : F ∣ GeneralIrrationality.primitivePolynomial p)
    (b : ℝ) (hb : 0 < b)
    (hcluster : ∀ r ∈ (complexPolynomial F).roots,
      ‖(Real.zeta p.weight : ℂ)-r‖ ≤ Real.exp (-b)) :
    (F.natDegree : ℝ) ≤
      (Real.log |(F.leadingCoeff : ℝ)| -
        Real.log ‖(complexPolynomial F).eval (Real.zeta p.weight : ℂ)‖) / b := by
  have hinj : Function.Injective (algebraMap ℤ ℂ) := Int.cast_injective
  have hFc : complexPolynomial F ≠ 0 := by
    intro hz
    exact hF ((Polynomial.map_injective _ hinj) (by simpa [complexPolynomial] using hz))
  have hv : (complexPolynomial F).eval (Real.zeta p.weight : ℂ) ≠ 0 := by
    intro hz
    have hr := (Polynomial.mem_roots hFc).mpr hz
    have hs := manuscript_divisor_root_separation p hp F hdiv _ hr
    have hpos := (primitive_exact_norm_disk p hp).1
    have hs0 : 1 / ‖whitened (Real.manuscriptPencil p)‖ ≤ 0 := by
      simpa only [sub_self, norm_zero] using hs
    exact not_le_of_gt hpos hs0
  have hdegree := polynomial_log_degree_upper (complexPolynomial F)
    (Real.zeta p.weight : ℂ) b hFc hb hv hcluster
  have hnormlc : ‖(complexPolynomial F).leadingCoeff‖ = |(F.leadingCoeff : ℝ)| := by
    rw [complexPolynomial, Polynomial.leadingCoeff_map_of_injective hinj]
    simp only [eq_intCast, Complex.norm_intCast]
  have hdeg : (complexPolynomial F).natDegree = F.natDegree :=
    Polynomial.natDegree_map_eq_of_injective hinj _
  simpa only [hnormlc, hdeg] using hdegree

/-- The straddling-root part of 4.7(2) for the actual manuscript polynomial,
with its exact radius and no asymptotic norm premise. -/
theorem manuscript_straddling_root_gap
    (p : Real.Parameters) (hp : Real.Admissible p) (rminus rplus : ℝ)
    (hm : rminus < Real.zeta p.weight) (hp' : Real.zeta p.weight < rplus)
    (hrminus : (GeneralIrrationality.primitivePolynomial p).eval₂
      (algebraMap ℤ ℂ) (rminus : ℂ) = 0)
    (hrplus : (GeneralIrrationality.primitivePolynomial p).eval₂
      (algebraMap ℤ ℂ) (rplus : ℂ) = 0) :
    2 / ‖whitened (Real.manuscriptPencil p)‖ ≤ rplus-rminus := by
  have hminus := primitive_root_distance p hp (rminus : ℂ) hrminus
  have hplus := primitive_root_distance p hp (rplus : ℂ) hrplus
  have hm' : 1 / ‖whitened (Real.manuscriptPencil p)‖ ≤
      Real.zeta p.weight-rminus := by
    simpa only [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
      abs_of_neg (sub_neg.mpr hm), neg_sub] using hminus
  have hp'' : 1 / ‖whitened (Real.manuscriptPencil p)‖ ≤
      rplus-Real.zeta p.weight := by
    simpa only [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (sub_pos.mpr hp')] using hplus
  calc
    2 / ‖whitened (Real.manuscriptPencil p)‖ =
        1 / ‖whitened (Real.manuscriptPencil p)‖ +
          1 / ‖whitened (Real.manuscriptPencil p)‖ := by ring
    _ ≤ (Real.zeta p.weight-rminus)+(rplus-Real.zeta p.weight) :=
      add_le_add hm' hp''
    _ = rplus-rminus := by ring

/-- Any separately proved norm upper bound supplies the corresponding
exponential straddling-root separation, preserving its inequality direction. -/
theorem manuscript_straddling_root_gap_of_norm_bound
    (p : Real.Parameters) (hp : Real.Admissible p) (rminus rplus a : ℝ)
    (hm : rminus < Real.zeta p.weight) (hp' : Real.zeta p.weight < rplus)
    (hrminus : (GeneralIrrationality.primitivePolynomial p).eval₂
      (algebraMap ℤ ℂ) (rminus : ℂ) = 0)
    (hrplus : (GeneralIrrationality.primitivePolynomial p).eval₂
      (algebraMap ℤ ℂ) (rplus : ℂ) = 0)
    (hnorm : ‖whitened (Real.manuscriptPencil p)‖ ≤ Real.exp a) :
    2 * Real.exp (-a) ≤ rplus-rminus := by
  have hpos : 0 < ‖whitened (Real.manuscriptPencil p)‖ :=
    one_div_pos.mp (primitive_exact_norm_disk p hp).1
  have hrecip : Real.exp (-a) ≤ 1 / ‖whitened (Real.manuscriptPencil p)‖ := by
    rw [Real.exp_neg, ← one_div]
    exact one_div_le_one_div_of_le hpos hnorm
  calc
    2 * Real.exp (-a) ≤ 2 * (1 / ‖whitened (Real.manuscriptPencil p)‖) := by
      gcongr
    _ = 2 / ‖whitened (Real.manuscriptPencil p)‖ := by ring
    _ ≤ rplus-rminus := manuscript_straddling_root_gap p hp rminus rplus
      hm hp' hrminus hrplus

/-- The upper arithmetic-rate premise quoted before 4.6 does not supply the
lower rate used in its proof. This is a counterexample to that inference,
not a counterexample to the manuscript's actual determinant family. -/
theorem paper_upper_rate_counterexample :
    ∃ A : ℚ, A ≤ (-232425/100000 : ℚ) ∧
      A + (2557199/1000000 : ℚ) < (23/100 : ℚ) := by
  exact ⟨-3, by norm_num, by norm_num⟩

end LeanPaper.Section4FactorDegreeBounds

#print axioms LeanPaper.Section4FactorDegreeBounds.polynomial_log_degree_lower
#print axioms LeanPaper.Section4FactorDegreeBounds.polynomial_log_degree_upper
#print axioms LeanPaper.Section4FactorDegreeBounds.manuscript_divisor_root_separation
#print axioms LeanPaper.Section4FactorDegreeBounds.manuscript_divisor_log_degree_lower
#print axioms LeanPaper.Section4FactorDegreeBounds.manuscript_divisor_log_degree_upper
#print axioms LeanPaper.Section4FactorDegreeBounds.manuscript_straddling_root_gap
#print axioms LeanPaper.Section4FactorDegreeBounds.manuscript_straddling_root_gap_of_norm_bound
#print axioms LeanPaper.Section4FactorDegreeBounds.paper_upper_rate_counterexample
