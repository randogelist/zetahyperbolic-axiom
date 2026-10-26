import LeanPaper.BeukersIntegralPencil

/-!
# The actual two-variable beta(4) Beukers moments

The alternating geometric expansion is absolutely integrable: its nth
term is dominated in integral norm by `(n+1)^(-4)`. The two diagonal and
off-diagonal formulas concern the printed positive density itself.
The beta values are defined by their convergent Dirichlet series, and the
finite harmonic corrections are rational numbers. No special-value
evaluation or assumed moment identity is used.
-/

noncomputable section
open scoped BigOperators
open MeasureTheory Set

namespace ManuscriptChain.BetaBeukers
open Beukers

def betaValue (s : ℕ) : ℝ := ∑' n : ℕ, (-1 : ℝ)^n / ((2*n+1 : ℕ) : ℝ)^s

def betaHarmonic (s m : ℕ) : ℚ :=
  ∑ n ∈ Finset.range m, (-1 : ℚ)^n / ((2*n+1 : ℕ) : ℚ)^s

theorem beta_series_summable {s : ℕ} (hs : 1 < s) :
    Summable (fun n : ℕ => (-1 : ℝ)^n / ((2*n+1 : ℕ) : ℝ)^s) := by
  apply (Real.zeta_series_summable hs).of_norm_bounded
  intro n
  have hn : 0 ≤ ((2*n+1 : ℕ) : ℝ) := by positivity
  simp only [norm_div, norm_pow, norm_neg, norm_one, one_pow,
    Real.norm_of_nonneg hn]
  apply one_div_le_one_div_of_le (by positivity)
  apply pow_le_pow_left₀ (by positivity)
  exact_mod_cast (by omega : n+1 ≤ 2*n+1)

theorem beta_even_tail_sum {s : ℕ} (hs : 1 < s) (k : ℕ) :
    (∑' n : ℕ, (-1 : ℝ)^n / ((4*k+2*n+1 : ℕ) : ℝ)^s) =
      betaValue s - (betaHarmonic s (2*k) : ℝ) := by
  have h := (beta_series_summable hs).sum_add_tsum_nat_add (2*k)
  change (∑ n ∈ Finset.range (2*k), (-1 : ℝ)^n / ((2*n+1 : ℕ) : ℝ)^s) +
    (∑' n : ℕ, (-1 : ℝ)^(n+2*k) / ((2*(n+2*k)+1 : ℕ) : ℝ)^s) =
      betaValue s at h
  have hsign (n : ℕ) : (-1 : ℝ)^(n+2*k) = (-1 : ℝ)^n := by
    rw [pow_add, pow_mul]
    norm_num
  have hindex (n : ℕ) : 2*(n+2*k)+1 = 4*k+2*n+1 := by omega
  simp_rw [hsign, hindex] at h
  have hfinite :
      (∑ n ∈ Finset.range (2*k), (-1 : ℝ)^n / ((2*n+1 : ℕ) : ℝ)^s) =
        (betaHarmonic s (2*k) : ℝ) := by simp [betaHarmonic]
  rw [hfinite] at h
  linarith

theorem beta_even_tail_summable {s : ℕ} (hs : 1 < s) (k : ℕ) :
    Summable (fun n : ℕ => (-1 : ℝ)^n / ((4*k+2*n+1 : ℕ) : ℝ)^s) := by
  have h := (summable_nat_add_iff (2*k)).mpr (beta_series_summable hs)
  have hsign (n : ℕ) : (-1 : ℝ)^(n+2*k) = (-1 : ℝ)^n := by
    rw [pow_add, pow_mul]
    norm_num
  have hindex (n : ℕ) : 2*(n+2*k)+1 = 4*k+2*n+1 := by omega
  simpa only [hsign, hindex] using h

def betaDensity (z : ℝ × ℝ) : ℝ :=
  (-_root_.Real.log (z.1*z.2))^2 / (6*(1+(z.1*z.2)^2))

theorem betaDensity_positive {z : ℝ × ℝ} (hz : z ∈ square) :
    0 < betaDensity z := by
  have hxy0 := mul_pos hz.1.1 hz.2.1
  have hxy1 : z.1*z.2 < 1 := by
    have h := mul_lt_mul_of_pos_right hz.1.2 hz.2.1
    nlinarith [hz.2.2]
  have hl : 0 < -_root_.Real.log (z.1*z.2) :=
    neg_pos.mpr (_root_.Real.log_neg hxy0 hxy1)
  exact div_pos (pow_pos hl _) (by positivity)

theorem betaDensity_measurable : Measurable betaDensity := by
  unfold betaDensity
  fun_prop

def betaMeasure : Measure (ℝ × ℝ) :=
  squareMeasure.withDensity (fun z => ENNReal.ofReal (betaDensity z))

theorem integral_betaMeasure (f : ℝ × ℝ → ℝ) :
    (∫ z, f z ∂betaMeasure) = ∫ z, f z * betaDensity z ∂squareMeasure := by
  rw [betaMeasure, integral_withDensity_eq_integral_toReal_smul
    betaDensity_measurable.ennreal_ofReal (by simp)]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioo)]
    with z hz
  rw [ENNReal.toReal_ofReal (betaDensity_positive hz).le]
  simp only [smul_eq_mul, mul_comm]

def positiveTerm (r t n : ℕ) (z : ℝ × ℝ) : ℝ :=
  (1/3 : ℝ) * ∑ j : Fin 3,
    logMonomial (r+2*n) j.val z.1 * logMonomial (t+2*n) (2-j.val) z.2

def signedTerm (r t n : ℕ) (z : ℝ × ℝ) : ℝ :=
  (-1 : ℝ)^n * positiveTerm r t n z

theorem positiveTerm_nonneg (r t n : ℕ) {z : ℝ × ℝ} (hz : z ∈ square) :
    0 ≤ positiveTerm r t n z := by
  apply mul_nonneg (by norm_num)
  exact Finset.sum_nonneg (fun j _ => mul_nonneg
    (logMonomial_nonneg _ _ hz.1) (logMonomial_nonneg _ _ hz.2))

theorem positiveTerm_integrable (r t n : ℕ) :
    Integrable (positiveTerm r t n) squareMeasure := by
  unfold positiveTerm squareMeasure
  rw [← Measure.prod_restrict]
  apply Integrable.const_mul
  apply integrable_finset_sum
  intro j hj
  exact (logMonomial_integrable (r+2*n) j.val).mul_prod
    (logMonomial_integrable (t+2*n) (2-j.val))

theorem signedTerm_integrable (r t n : ℕ) :
    Integrable (signedTerm r t n) squareMeasure :=
  (positiveTerm_integrable r t n).const_mul _

theorem positiveTerm_eq (r t n : ℕ) {z : ℝ × ℝ} (hz : z ∈ square) :
    positiveTerm r t n z =
      z.1^r*z.2^t*(z.1*z.2)^(2*n)*(-_root_.Real.log (z.1*z.2))^2/6 := by
  simp [positiveTerm, logMonomial, Fin.sum_univ_succ,
    _root_.Real.log_mul hz.1.1.ne' hz.2.1.ne', pow_add, mul_pow]
  ring

/-- Absolute integrability follows from the positive logarithmic term,
because the extra beta denominator is at least one on the square. -/
theorem beta_monomial_integrable (r t : ℕ) :
    Integrable (fun z => z.1^r*z.2^t*betaDensity z) squareMeasure := by
  refine (positiveTerm_integrable r t 0).mono' ?_ ?_
  · exact (by fun_prop [betaDensity] : Measurable
      (fun z : ℝ × ℝ => z.1^r*z.2^t*betaDensity z)).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioo)]
      with z hz
    have hnum : 0 ≤ z.1^r*z.2^t*(-_root_.Real.log (z.1*z.2))^2 :=
      mul_nonneg (mul_nonneg (pow_nonneg hz.1.1.le _) (pow_nonneg hz.2.1.le _))
        (sq_nonneg _)
    have hden : (6 : ℝ) ≤ 6*(1+(z.1*z.2)^2) := by nlinarith [sq_nonneg (z.1*z.2)]
    calc
      ‖z.1^r*z.2^t*betaDensity z‖ =
          (z.1^r*z.2^t*(-_root_.Real.log (z.1*z.2))^2) /
            (6*(1+(z.1*z.2)^2)) := by
        rw [Real.norm_of_nonneg (mul_nonneg
          (mul_nonneg (pow_nonneg hz.1.1.le _) (pow_nonneg hz.2.1.le _))
          (betaDensity_positive hz).le)]
        unfold betaDensity
        ring
      _ ≤ (z.1^r*z.2^t*(-_root_.Real.log (z.1*z.2))^2) / 6 :=
        div_le_div_of_nonneg_left hnum (by norm_num) hden
      _ = positiveTerm r t 0 z := by
        rw [positiveTerm_eq r t 0 hz]
        simp

theorem monomial_integrable_betaMeasure (r t : ℕ) :
    Integrable (fun z : ℝ × ℝ => z.1^r*z.2^t) betaMeasure := by
  rw [betaMeasure, integrable_withDensity_iff_integrable_smul'
    betaDensity_measurable.ennreal_ofReal (by simp)]
  apply (beta_monomial_integrable r t).congr
  filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioo)]
    with z hz
  rw [ENNReal.toReal_ofReal (betaDensity_positive hz).le]
  simp only [smul_eq_mul, mul_comm]

theorem betaDensity_moment_eq_tsum (r t : ℕ) {z : ℝ × ℝ} (hz : z ∈ square) :
    z.1^r*z.2^t*betaDensity z = ∑' n, signedTerm r t n z := by
  have hxy0 : 0 < z.1*z.2 := mul_pos hz.1.1 hz.2.1
  have hxy1 : z.1*z.2 < 1 := by
    have h := mul_lt_mul_of_pos_right hz.1.2 hz.2.1
    nlinarith [hz.2.2]
  have hnorm : ‖-((z.1*z.2)^2)‖ < 1 := by
    rw [norm_neg, Real.norm_of_nonneg (sq_nonneg _)]
    nlinarith
  have h := (hasSum_geometric_of_norm_lt_one hnorm).mul_left
    (z.1^r*z.2^t*(-_root_.Real.log (z.1*z.2))^2/6)
  have hp (n : ℕ) : (-((z.1*z.2)^2))^n =
      (-1 : ℝ)^n * (z.1*z.2)^(2*n) := by
    rw [show -((z.1*z.2)^2) = (-1 : ℝ)*(z.1*z.2)^2 by ring,
      mul_pow, ← pow_mul]
  have hterm : (fun n => signedTerm r t n z) =
      (fun n => (z.1^r*z.2^t*(-_root_.Real.log (z.1*z.2))^2/6)*
        (-((z.1*z.2)^2))^n) := by
    funext n
    rw [signedTerm, positiveTerm_eq r t n hz, hp]
    ring
  rw [hterm, h.tsum_eq]
  unfold betaDensity
  simp only [sub_neg_eq_add, div_eq_mul_inv, mul_inv_rev]
  ring

theorem integral_positiveTerm (r t n : ℕ) :
    (∫ z, positiveTerm r t n z ∂squareMeasure) =
      (1/3 : ℝ) * ∑ j : Fin 3,
        1 / (((r+2*n : ℕ) : ℝ)+1)^(j.val+1) *
        (1 / (((t+2*n : ℕ) : ℝ)+1)^(2-j.val+1)) := by
  unfold positiveTerm
  rw [integral_const_mul]
  congr 1
  rw [integral_finset_sum]
  · apply Finset.sum_congr rfl
    intro j hj
    change (∫ z in square, logMonomial (r+2*n) j.val z.1 *
      logMonomial (t+2*n) (2-j.val) z.2 ∂volume.prod volume) = _
    rw [setIntegral_prod_mul, integral_logMonomial, integral_logMonomial]
  · intro j hj
    unfold squareMeasure
    rw [← Measure.prod_restrict]
    exact (logMonomial_integrable (r+2*n) j.val).mul_prod
      (logMonomial_integrable (t+2*n) (2-j.val))

theorem integral_positiveTerm_le (r t n : ℕ) :
    (∫ z, positiveTerm r t n z ∂squareMeasure) ≤ 1 / ((n : ℝ)+1)^4 := by
  rw [integral_positiveTerm]
  have hsum : (∑ j : Fin 3,
        1 / (((r+2*n : ℕ) : ℝ)+1)^(j.val+1) *
        (1 / (((t+2*n : ℕ) : ℝ)+1)^(2-j.val+1))) ≤
      ∑ _j : Fin 3, 1 / ((n : ℝ)+1)^4 := by
    apply Finset.sum_le_sum
    intro j hj
    rw [one_div_mul_one_div]
    apply one_div_le_one_div_of_le (by positivity)
    have he : (j.val+1)+(2-j.val+1) = 4 := by omega
    rw [← he, pow_add]
    apply mul_le_mul
    · apply pow_le_pow_left₀ (by positivity)
      push_cast
      linarith
    · apply pow_le_pow_left₀ (by positivity)
      push_cast
      linarith
    · positivity
    · positivity
  have h := mul_le_mul_of_nonneg_left hsum (by norm_num : (0 : ℝ) ≤ 1/3)
  simpa using h

theorem summable_integral_norm_signedTerm (r t : ℕ) :
    Summable (fun n => ∫ z, ‖signedTerm r t n z‖ ∂squareMeasure) := by
  apply Summable.of_nonneg_of_le (fun n => integral_nonneg (fun _ => norm_nonneg _)) _
    (Real.zeta_series_summable (s := 4) (by norm_num))
  intro n
  have he : (∫ z, ‖signedTerm r t n z‖ ∂squareMeasure) =
      ∫ z, positiveTerm r t n z ∂squareMeasure := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioo)]
      with z hz
    simp only [signedTerm, norm_mul, norm_pow, norm_neg, norm_one, one_pow,
      one_mul, Real.norm_of_nonneg (positiveTerm_nonneg r t n hz)]
  rw [he]
  simpa only [Nat.cast_add, Nat.cast_one] using integral_positiveTerm_le r t n

theorem integral_betaDensity_moment_series (r t : ℕ) :
    (∫ z, z.1^r*z.2^t*betaDensity z ∂squareMeasure) =
      ∑' n, (-1 : ℝ)^n * ((1/3 : ℝ) * ∑ j : Fin 3,
        1 / (((r+2*n : ℕ) : ℝ)+1)^(j.val+1) *
        (1 / (((t+2*n : ℕ) : ℝ)+1)^(2-j.val+1))) := by
  calc
    _ = ∫ z, ∑' n, signedTerm r t n z ∂squareMeasure := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioo)]
        with z hz
      exact betaDensity_moment_eq_tsum r t hz
    _ = ∑' n, ∫ z, signedTerm r t n z ∂squareMeasure :=
      (integral_tsum_of_summable_integral_norm (signedTerm_integrable r t)
        (summable_integral_norm_signedTerm r t)).symm
    _ = _ := by simp_rw [signedTerm, integral_const_mul, integral_positiveTerm]

theorem beta_diagonal_moment (k : ℕ) :
    (∫ z, z.1^(4*k)*z.2^(4*k)*betaDensity z ∂squareMeasure) =
      betaValue 4 - (betaHarmonic 4 (2*k) : ℝ) := by
  rw [integral_betaDensity_moment_series]
  have hterm (n : ℕ) : (1/3 : ℝ) * ∑ j : Fin 3,
      1 / (((4*k+2*n : ℕ) : ℝ)+1)^(j.val+1) *
      (1 / (((4*k+2*n : ℕ) : ℝ)+1)^(2-j.val+1)) =
      1 / (((4*k+2*n : ℕ) : ℝ)+1)^4 := by
    have he (j : Fin 3) : (j.val+1)+(2-j.val+1) = 4 := by omega
    simp_rw [one_div_mul_one_div, ← pow_add, he]
    simp
  simp_rw [hterm, mul_one_div]
  simpa only [Nat.cast_add, Nat.cast_one] using beta_even_tail_sum (s := 4) (by norm_num) k

private theorem reciprocal_sum_three (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0)
    (hab : a ≠ b) :
    (1/3 : ℝ) * (∑ j : Fin 3,
      1 / a^(j.val+1) * (1 / b^(2-j.val+1))) =
      (1 / b^3 - 1 / a^3) / (3*(a-b)) := by
  have hd := sub_ne_zero.mpr hab
  simp [Fin.sum_univ_succ]
  field_simp [ha, hb, hd] <;> ring

theorem beta_offdiagonal_moment (k l : ℕ) (hkl : k ≠ l) :
    (∫ z, z.1^(4*k)*z.2^(4*l)*betaDensity z ∂squareMeasure) =
      ((betaHarmonic 3 (2*k) : ℝ) - (betaHarmonic 3 (2*l) : ℝ)) /
        (12*((k : ℝ)-(l : ℝ))) := by
  rw [integral_betaDensity_moment_series]
  have hterm (n : ℕ) : (-1 : ℝ)^n * ((1/3 : ℝ) * ∑ j : Fin 3,
        1 / (((4*k+2*n : ℕ) : ℝ)+1)^(j.val+1) *
        (1 / (((4*l+2*n : ℕ) : ℝ)+1)^(2-j.val+1))) =
      ((-1 : ℝ)^n / ((4*l+2*n+1 : ℕ) : ℝ)^3 -
       (-1 : ℝ)^n / ((4*k+2*n+1 : ℕ) : ℝ)^3) /
        (12*((k : ℝ)-(l : ℝ))) := by
    have hne : (((4*k+2*n : ℕ) : ℝ)+1) ≠ (((4*l+2*n : ℕ) : ℝ)+1) := by
      intro heq
      have hkn : 4*k+2*n = 4*l+2*n := by exact_mod_cast (add_right_cancel heq)
      omega
    rw [reciprocal_sum_three _ _ (by positivity) (by positivity) hne]
    have hd : 3*((((4*k+2*n : ℕ) : ℝ)+1)-((((4*l+2*n : ℕ) : ℝ)+1))) =
        12*((k : ℝ)-(l : ℝ)) := by push_cast; ring
    rw [hd]
    push_cast
    ring
  simp_rw [hterm]
  rw [tsum_div_const, ((beta_even_tail_summable (s := 3) (by norm_num) l).hasSum.sub
    (beta_even_tail_summable (s := 3) (by norm_num) k).hasSum).tsum_eq,
    beta_even_tail_sum (by norm_num) l, beta_even_tail_sum (by norm_num) k]
  ring

theorem beta_offdiagonal_is_rational (k l : ℕ) (hkl : k ≠ l) :
    ∃ q : ℚ, (∫ z, z.1^(4*k)*z.2^(4*l)*betaDensity z ∂squareMeasure) = (q : ℝ) := by
  refine ⟨(betaHarmonic 3 (2*k)-betaHarmonic 3 (2*l)) /
    (12*((k : ℚ)-(l : ℚ))), ?_⟩
  rw [beta_offdiagonal_moment k l hkl]
  push_cast
  rfl

/-- Exact analytic moment portion of Proposition 5.3 on the printed density. -/
theorem proposition_5_3_exact_moments (k l : ℕ) :
    (∀ z ∈ square, 0 < betaDensity z) ∧
    (∫ z, z.1^(4*k)*z.2^(4*l)*betaDensity z ∂squareMeasure) =
      (if k = l then betaValue 4 - (betaHarmonic 4 (2*k) : ℝ)
        else (((betaHarmonic 3 (2*k)-betaHarmonic 3 (2*l)) /
          (12*((k : ℚ)-(l : ℚ))) : ℚ) : ℝ)) := by
  refine ⟨fun z hz => betaDensity_positive hz, ?_⟩
  by_cases h : k = l
  · subst l
    simp only [if_pos rfl]
    exact beta_diagonal_moment k
  · rw [if_neg h, beta_offdiagonal_moment k l h]
    push_cast
    rfl

/-- The printed moments also hold as integrals against the constructed
positive measure, with integrability supplied rather than presumed. -/
theorem proposition_5_3_actual_measure (k l : ℕ) :
    Integrable (fun z : ℝ × ℝ => z.1^(4*k)*z.2^(4*l)) betaMeasure ∧
    (∫ z, z.1^(4*k)*z.2^(4*l) ∂betaMeasure) =
      (if k = l then betaValue 4 - (betaHarmonic 4 (2*k) : ℝ)
        else (((betaHarmonic 3 (2*k)-betaHarmonic 3 (2*l)) /
          (12*((k : ℚ)-(l : ℚ))) : ℚ) : ℝ)) := by
  refine ⟨monomial_integrable_betaMeasure (4*k) (4*l), ?_⟩
  rw [integral_betaMeasure]
  exact (proposition_5_3_exact_moments k l).2

end ManuscriptChain.BetaBeukers

#print axioms ManuscriptChain.BetaBeukers.proposition_5_3_exact_moments
#print axioms ManuscriptChain.BetaBeukers.proposition_5_3_actual_measure
#print axioms ManuscriptChain.BetaBeukers.beta_offdiagonal_is_rational
