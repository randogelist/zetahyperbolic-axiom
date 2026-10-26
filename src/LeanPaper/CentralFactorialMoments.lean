import LeanPaper.CentralFactorialDecay
import Theorem_3_1_Hyperbolic_Moments
import Theorem_3_1_Positive_Moment_Realization

/-!
# Actual accelerated-secant moments for Theorem 6.13

The already proved exponential envelope is now used to construct an actual
positive measure with all polynomial moments and strictly positive moment
Gram matrices at every finite order. No series interchange, beta-functional
identification or quantitative arithmetic consequence is assumed here.
The index `k` is the manuscript's index minus one.
-/

noncomputable section
open MeasureTheory Set

namespace LeanPaper.CentralFactorialMoments
open CentralFactorialDecay

theorem density_measurable (k : ℕ) : Measurable (density k) := by
  unfold density
  fun_prop

/-- The exact accelerated secant density has every nonnegative integer moment. -/
theorem integrableOn_monomial_density (k e : ℕ) :
    IntegrableOn (fun u : ℝ => u ^ e * density k u) (Ioi 0) := by
  have h := (ManuscriptChain.Hyperbolic.integrableOn_pow_mul_exp
    (e + (2 * k + 1)) (a := ((2 * k + 1 : ℕ) : ℝ) * Real.pi) (by positivity)).const_mul
      (2 * Real.pi)
  apply h.mono' ((measurable_id.pow_const _).mul (density_measurable k)).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  have hnonneg : 0 ≤ u ^ e * density k u :=
    mul_nonneg (pow_nonneg (le_of_lt hu) _) (density_pos k hu).le
  simp only [Pi.mul_apply, id_eq]
  rw [Real.norm_of_nonneg hnonneg]
  have hb := mul_le_mul_of_nonneg_left (density_le_exp k (le_of_lt hu))
    (pow_nonneg (le_of_lt hu) e)
  have he : -((2 * k + 1 : ℕ) : ℝ) * Real.pi * u =
      -((((2 * k + 1 : ℕ) : ℝ) * Real.pi) * u) := by ring
  rw [he] at hb
  simpa only [pow_add, mul_assoc, mul_left_comm, mul_comm] using hb

/-- An explicit factorial upper bound for every actual density moment. -/
theorem integral_monomial_density_le (k e : ℕ) :
    (∫ u : ℝ in Ioi 0, u ^ e * density k u) ≤
      (2 * Real.pi) * ((e + (2 * k + 1)).factorial : ℝ) /
        (((2 * k + 1 : ℕ) : ℝ) * Real.pi) ^ (e + (2 * k + 1) + 1) := by
  have hi := (ManuscriptChain.Hyperbolic.integrableOn_pow_mul_exp
    (e + (2 * k + 1)) (a := ((2 * k + 1 : ℕ) : ℝ) * Real.pi) (by positivity)).const_mul
      (2 * Real.pi)
  calc
    _ ≤ ∫ u : ℝ in Ioi 0, (2 * Real.pi) *
        (u ^ (e + (2 * k + 1)) * Real.exp (-((((2 * k + 1 : ℕ) : ℝ) * Real.pi) * u))) := by
      apply integral_mono_ae (integrableOn_monomial_density k e) hi
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      have hb := mul_le_mul_of_nonneg_left (density_le_exp k (le_of_lt hu))
        (pow_nonneg (le_of_lt hu) e)
      have he : -((2 * k + 1 : ℕ) : ℝ) * Real.pi * u =
          -((((2 * k + 1 : ℕ) : ℝ) * Real.pi) * u) := by ring
      rw [he] at hb
      simpa only [pow_add, mul_assoc, mul_left_comm, mul_comm] using hb
    _ = _ := by
      rw [integral_const_mul, ManuscriptChain.Hyperbolic.integral_pow_mul_exp
        (e + (2 * k + 1)) (by positivity)]
      ring

def secantMeasure (k : ℕ) : Measure ℝ :=
  (volume.restrict (Ioi 0)).withDensity (fun u => ENNReal.ofReal (density k u))

instance secantMeasure_nullSingleton (k : ℕ) : NullSingletonClass (secantMeasure k) := by
  unfold secantMeasure
  infer_instance

theorem secantMeasure_nonzero (k : ℕ) : secantMeasure k ≠ 0 := by
  have hac : volume.restrict (Ioi (0 : ℝ)) ≪ secantMeasure k := by
    apply withDensity_absolutelyContinuous' (density_measurable k).ennreal_ofReal.aemeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    exact ne_of_gt (ENNReal.ofReal_pos.mpr (density_pos k hu))
  intro hz
  rw [hz] at hac
  have h := Measure.absolutelyContinuous_zero_iff.mp hac
  have hu := congrArg (fun μ : Measure ℝ => μ Set.univ) h
  simp at hu

theorem integrable_monomial_secantMeasure (k e : ℕ) :
    Integrable (fun u : ℝ => u ^ e) (secantMeasure k) := by
  rw [secantMeasure, integrable_withDensity_iff_integrable_smul'
    (density_measurable k).ennreal_ofReal (by simp)]
  apply (integrableOn_monomial_density k e).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  rw [ENNReal.toReal_ofReal (density_pos k hu).le]
  simp only [smul_eq_mul, mul_comm]

theorem integral_monomial_secantMeasure (k e : ℕ) :
    (∫ u : ℝ, u ^ e ∂secantMeasure k) = ∫ u : ℝ in Ioi 0, u ^ e * density k u := by
  rw [secantMeasure, integral_withDensity_eq_integral_toReal_smul
    (density_measurable k).ennreal_ofReal (by simp)]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  rw [ENNReal.toReal_ofReal (density_pos k hu).le]
  simp only [smul_eq_mul, mul_comm]

/-- Every finite Hankel matrix of the actual accelerated density is positive
definite; polynomial independence follows from its nonatomic positive measure. -/
theorem momentMatrix_posDef (k h : ℕ) :
    (ManuscriptChain.Moments.momentMatrix (secantMeasure k) h).PosDef := by
  apply ManuscriptChain.Moments.momentMatrix_posDef (secantMeasure_nonzero k)
  intro i j
  exact integrable_monomial_secantMeasure k _

end LeanPaper.CentralFactorialMoments

#print axioms LeanPaper.CentralFactorialMoments.integrableOn_monomial_density
#print axioms LeanPaper.CentralFactorialMoments.integral_monomial_density_le
#print axioms LeanPaper.CentralFactorialMoments.momentMatrix_posDef
