import LeanPaper.UnitLogMoments
import Theorem_3_1_Zeta_Tail
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Theorem 5.1: the actual two-variable Beukers measure

The printed density is expanded into an absolutely integrable geometric
series. Every term is a sum of six products of Mellin logarithmic moments.
The resulting exact moment series retains the actual unit-square integral.
-/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace ManuscriptChain.Beukers

abbrev square : Set (ℝ × ℝ) := Ioo 0 1 ×ˢ Ioo 0 1

def squareMeasure : Measure (ℝ × ℝ) := (volume.prod volume).restrict square

def density (z : ℝ × ℝ) : ℝ :=
  (-_root_.Real.log (z.1*z.2))^5 / (720 * (1-z.1*z.2))

def logMonomial (a j : ℕ) (x : ℝ) : ℝ :=
  x^a * (-_root_.Real.log x)^j / (j.factorial : ℝ)

theorem logMonomial_integrable (a j : ℕ) :
    IntegrableOn (logMonomial a j) (Ioo 0 1) :=
  (LeanPaper.UnitLogMoments.integrable_pow_log a j).div_const _

theorem integral_logMonomial (a j : ℕ) :
    (∫ x : ℝ in Ioo 0 1, logMonomial a j x) = 1 / ((a : ℝ)+1)^(j+1) := by
  rw [show logMonomial a j = (fun x => x^a * (-_root_.Real.log x)^j / (j.factorial : ℝ)) from rfl,
    integral_div, LeanPaper.UnitLogMoments.integral_pow_log]
  have hj : (j.factorial : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_ne_zero j)
  field_simp

def momentTerm (r t n : ℕ) (z : ℝ × ℝ) : ℝ :=
  (1/6 : ℝ) * ∑ j : Fin 6,
    logMonomial (r+n) j.val z.1 * logMonomial (t+n) (5-j.val) z.2

lemma logMonomial_nonneg (a j : ℕ) {x : ℝ} (hx : x ∈ Ioo 0 1) :
    0 ≤ logMonomial a j x := by
  have hh : 0 ≤ -_root_.Real.log x := neg_nonneg.mpr
    (_root_.Real.log_nonpos hx.1.le hx.2.le)
  unfold logMonomial
  exact div_nonneg (mul_nonneg (pow_nonneg hx.1.le a) (pow_nonneg hh j))
    (by positivity)

lemma momentTerm_nonneg (r t n : ℕ) {z : ℝ × ℝ} (hz : z ∈ square) :
    0 ≤ momentTerm r t n z := by
  unfold momentTerm
  apply mul_nonneg (by norm_num)
  exact Finset.sum_nonneg fun j _ => mul_nonneg
    (logMonomial_nonneg _ _ hz.1) (logMonomial_nonneg _ _ hz.2)

lemma momentTerm_integrable (r t n : ℕ) : Integrable (momentTerm r t n) squareMeasure := by
  unfold momentTerm squareMeasure
  rw [← Measure.prod_restrict]
  apply Integrable.const_mul
  apply integrable_finset_sum
  intro j _
  exact (logMonomial_integrable (r+n) j.val).mul_prod
    (logMonomial_integrable (t+n) (5-j.val))

lemma momentTerm_eq (r t n : ℕ) {z : ℝ × ℝ} (hz : z ∈ square) :
    momentTerm r t n z =
      z.1^r*z.2^t*(z.1*z.2)^n*(-_root_.Real.log (z.1*z.2))^5/720 := by
  have hx := hz.1.1.ne'
  have hy := hz.2.1.ne'
  simp [momentTerm, logMonomial, Fin.sum_univ_succ,
    _root_.Real.log_mul hx hy, pow_add, mul_pow]
  ring

lemma density_moment_eq_tsum (r t : ℕ) {z : ℝ × ℝ} (hz : z ∈ square) :
    z.1^r*z.2^t*density z = ∑' n, momentTerm r t n z := by
  have hxy0 : 0 < z.1*z.2 := mul_pos hz.1.1 hz.2.1
  have hxy1 : z.1*z.2 < 1 := by
    have hh := mul_lt_mul_of_pos_right hz.1.2 hz.2.1
    nlinarith [hz.2.2]
  have hnorm : ‖z.1*z.2‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos hxy0]
    exact hxy1
  have h := (hasSum_geometric_of_norm_lt_one hnorm).mul_left
    (z.1^r*z.2^t*(-_root_.Real.log (z.1*z.2))^5/720)
  have hterm : (fun n => momentTerm r t n z) =
      (fun n => (z.1^r*z.2^t*(-_root_.Real.log (z.1*z.2))^5/720)*(z.1*z.2)^n) := by
    funext n
    rw [momentTerm_eq r t n hz]
    ring
  rw [hterm]
  rw [h.tsum_eq]
  unfold density
  have hden : (1-z.1*z.2 : ℝ) ≠ 0 := ne_of_gt (sub_pos.mpr hxy1)
  have hden720 : (720-z.1*z.2*720 : ℝ) ≠ 0 := by
    have hfactor : (720-z.1*z.2*720 : ℝ) = 720*(1-z.1*z.2) := by ring
    rw [hfactor]
    exact mul_ne_zero (by norm_num) hden
  field_simp [hden, hden720] <;> ring

/-- Exact separated moment of a single geometric-series term. -/
theorem integral_momentTerm (r t n : ℕ) :
    (∫ z, momentTerm r t n z ∂squareMeasure) =
      (1/6 : ℝ) * ∑ j : Fin 6,
        1 / (((r+n : ℕ) : ℝ)+1)^(j.val+1) *
        (1 / (((t+n : ℕ) : ℝ)+1)^(5-j.val+1)) := by
  unfold momentTerm
  rw [integral_const_mul]
  congr 1
  rw [integral_finset_sum]
  · apply Finset.sum_congr rfl
    intro j _
    change (∫ z in square, logMonomial (r+n) j.val z.1 *
      logMonomial (t+n) (5-j.val) z.2 ∂volume.prod volume) = _
    rw [setIntegral_prod_mul, integral_logMonomial, integral_logMonomial]
  · intro j _
    unfold squareMeasure
    rw [← Measure.prod_restrict]
    exact (logMonomial_integrable (r+n) j.val).mul_prod
      (logMonomial_integrable (t+n) (5-j.val))

lemma integral_norm_momentTerm (r t n : ℕ) :
    (∫ z, ‖momentTerm r t n z‖ ∂squareMeasure) =
      ∫ z, momentTerm r t n z ∂squareMeasure := by
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioo)] with z hz
  exact Real.norm_of_nonneg (momentTerm_nonneg r t n hz)

lemma integral_momentTerm_le (r t n : ℕ) :
    (∫ z, momentTerm r t n z ∂squareMeasure) ≤ 1 / ((n : ℝ)+1)^7 := by
  rw [integral_momentTerm]
  have hsum : (∑ j : Fin 6,
        1 / (((r+n : ℕ) : ℝ)+1)^(j.val+1) *
        (1 / (((t+n : ℕ) : ℝ)+1)^(5-j.val+1))) ≤
      ∑ _j : Fin 6, 1 / ((n : ℝ)+1)^7 := by
    apply Finset.sum_le_sum
    intro j _
    rw [one_div_mul_one_div]
    apply one_div_le_one_div_of_le (by positivity)
    have he : (j.val+1)+(5-j.val+1) = 7 := by omega
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
  have hh := mul_le_mul_of_nonneg_left hsum (by norm_num : (0 : ℝ) ≤ 1/6)
  simpa using hh

lemma summable_integral_norm_momentTerm (r t : ℕ) :
    Summable (fun n => ∫ z, ‖momentTerm r t n z‖ ∂squareMeasure) := by
  apply Summable.of_nonneg_of_le (fun n => integral_nonneg (fun _ => norm_nonneg _)) _
    (Real.zeta_series_summable (s := 7) (by norm_num))
  intro n
  rw [integral_norm_momentTerm]
  simpa only [Nat.cast_add, Nat.cast_one] using integral_momentTerm_le r t n

/-- The actual unit-square moment, with the series/integral exchange justified. -/
theorem integral_density_moment_series (r t : ℕ) :
    (∫ z, z.1^r*z.2^t*density z ∂squareMeasure) =
      ∑' n, (1/6 : ℝ) * ∑ j : Fin 6,
        1 / (((r+n : ℕ) : ℝ)+1)^(j.val+1) *
        (1 / (((t+n : ℕ) : ℝ)+1)^(5-j.val+1)) := by
  calc
    _ = ∫ z, ∑' n, momentTerm r t n z ∂squareMeasure := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioo)] with z hz
      exact density_moment_eq_tsum r t hz
    _ = ∑' n, ∫ z, momentTerm r t n z ∂squareMeasure :=
      (integral_tsum_of_summable_integral_norm (momentTerm_integrable r t)
        (summable_integral_norm_momentTerm r t)).symm
    _ = _ := by simp_rw [integral_momentTerm]

/-- Every diagonal moment of the printed density is the actual ζ(7) tail. -/
theorem diagonal_moment (r : ℕ) :
    (∫ z, z.1^r*z.2^r*density z ∂squareMeasure) =
      Real.zeta 7 - (Real.harmonic 7 r : ℝ) := by
  rw [integral_density_moment_series]
  have hterm (n : ℕ) : (1/6 : ℝ) * ∑ j : Fin 6,
      1 / (((r+n : ℕ) : ℝ)+1)^(j.val+1) *
      (1 / (((r+n : ℕ) : ℝ)+1)^(5-j.val+1)) =
      1 / (((r+n : ℕ) : ℝ)+1)^7 := by
    have he (j : Fin 6) : (j.val+1)+(5-j.val+1) = 7 := by omega
    simp_rw [one_div_mul_one_div, ← pow_add, he]
    simp
  simp_rw [hterm]
  simpa only [Nat.cast_add, Nat.cast_one] using Real.zeta_tail_sum (s := 7) (by norm_num) r

end ManuscriptChain.Beukers

#print axioms ManuscriptChain.Beukers.integral_density_moment_series
#print axioms ManuscriptChain.Beukers.diagonal_moment
