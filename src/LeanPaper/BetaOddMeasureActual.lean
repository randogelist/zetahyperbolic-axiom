import LeanPaper.BeukersMomentSeries
import LeanPaper.OddBetaValues
import LeanPaper.BetaOneMoments
import Theorem_3_1_Positive_Moment_Realization

/-!
# Actual odd-beta measures at every nonnegative index

The measure is the printed logarithmic density on `(0,1)`. Its moments are
integrable, its even moments are the actual odd-beta tails (including beta(1)),
and the manuscript's Hankel matrix at the beta value is positive definite.
No moment identity or positivity hypothesis is supplied as an assumption.
Total positivity of unrelated mixed minors and the printed exterior
asymptotic are separate obligations.
-/

noncomputable section
open scoped BigOperators
open MeasureTheory Set Matrix

namespace LeanPaper.BetaOddMeasureActual
open ManuscriptChain.Beukers OddBetaValues

def density (k : ℕ) (u : ℝ) : ℝ :=
  (-Real.log u) ^ (2*k) / (((2*k).factorial : ℝ) * (1 + u^2))

theorem density_pos (k : ℕ) {u : ℝ} (hu : u ∈ Ioo 0 1) :
    0 < density k u := by
  have hl : 0 < -Real.log u := neg_pos.mpr (Real.log_neg hu.1 hu.2)
  unfold density
  positivity

theorem density_measurable (k : ℕ) : Measurable (density k) := by
  unfold density
  fun_prop

theorem monomial_density_integrable (k a : ℕ) :
    IntegrableOn (fun u : ℝ => u^a * density k u) (Ioo 0 1) := by
  apply (logMonomial_integrable a (2*k)).mono'
    ((measurable_id.pow_const a).mul (density_measurable k)).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
  have hn := logMonomial_nonneg a (2*k) hu
  have he : u^a * density k u = logMonomial a (2*k) u / (1+u^2) := by
    unfold density logMonomial
    ring
  rw [he, Real.norm_of_nonneg (div_nonneg hn (by positivity))]
  exact div_le_self hn (by nlinarith [sq_nonneg u])

def measure (k : ℕ) : Measure ℝ :=
  (volume.restrict (Ioo 0 1)).withDensity (fun u => ENNReal.ofReal (density k u))

instance measure_nullSingleton (k : ℕ) : NullSingletonClass (measure k) := by
  unfold measure
  infer_instance

theorem measure_nonzero (k : ℕ) : measure k ≠ 0 := by
  have hac : volume.restrict (Ioo (0 : ℝ) 1) ≪ measure k := by
    apply withDensity_absolutelyContinuous' (density_measurable k).ennreal_ofReal.aemeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
    exact ne_of_gt (ENNReal.ofReal_pos.mpr (density_pos k hu))
  intro hz
  rw [hz] at hac
  have h := Measure.absolutelyContinuous_zero_iff.mp hac
  have hu := congrArg (fun μ : Measure ℝ => μ Set.univ) h
  simp at hu

theorem integrable_monomial (k a : ℕ) :
    Integrable (fun u : ℝ => u^a) (measure k) := by
  rw [measure, integrable_withDensity_iff_integrable_smul'
    (density_measurable k).ennreal_ofReal (by simp)]
  apply (monomial_density_integrable k a).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
  rw [ENNReal.toReal_ofReal (density_pos k hu).le]
  simp only [smul_eq_mul, mul_comm]

theorem integral_monomial (k a : ℕ) :
    (∫ u : ℝ, u^a ∂measure k) = ∫ u : ℝ in Ioo 0 1, u^a*density k u := by
  rw [measure, integral_withDensity_eq_integral_toReal_smul
    (density_measurable k).ennreal_ofReal (by simp)]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
  rw [ENNReal.toReal_ofReal (density_pos k hu).le]
  simp only [smul_eq_mul, mul_comm]

def moment (k a : ℕ) : ℝ := ∫ u : ℝ in Ioo 0 1, u^a * density k u

/-- The actual two-step Mellin recurrence, with no series assumptions. -/
theorem moment_add_two (k a : ℕ) :
    moment k a + moment k (a+2) = 1 / ((a : ℝ)+1)^(2*k+1) := by
  rw [moment, moment, ← integral_add (monomial_density_integrable k a)
    (monomial_density_integrable k (a+2)), ← integral_logMonomial a (2*k)]
  apply integral_congr_ae
  filter_upwards [] with u
  have hd : (1+u^2 : ℝ) ≠ 0 := by positivity
  unfold density logMonomial
  rw [pow_add]
  field_simp [hd, show ((2*k).factorial : ℝ) ≠ 0 by positivity]
  <;> ring

def seriesTerm (k a n : ℕ) (u : ℝ) : ℝ :=
  (-1 : ℝ)^n * logMonomial (a+2*n) (2*k) u

theorem seriesTerm_integrable (k a n : ℕ) :
    IntegrableOn (seriesTerm k a n) (Ioo 0 1) :=
  (logMonomial_integrable (a+2*n) (2*k)).const_mul _

theorem integral_norm_seriesTerm (k a n : ℕ) :
    (∫ u : ℝ in Ioo 0 1, ‖seriesTerm k a n u‖) =
      1 / (((a+2*n : ℕ) : ℝ)+1)^(2*k+1) := by
  rw [← integral_logMonomial (a+2*n) (2*k)]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
  simp only [seriesTerm, norm_mul, norm_pow, norm_neg, norm_one, one_pow,
    one_mul, Real.norm_of_nonneg (logMonomial_nonneg _ _ hu)]

theorem summable_integral_norm_seriesTerm {k : ℕ} (hk : k ≠ 0) (a : ℕ) :
    Summable (fun n => ∫ u : ℝ in Ioo 0 1, ‖seriesTerm k a n u‖) := by
  apply Summable.of_nonneg_of_le (fun n => integral_nonneg (fun u => norm_nonneg _))
    (g := fun n : ℕ => 1 / ((n : ℝ)+1)^(2*k+1))
    (by simpa only [Nat.cast_add, Nat.cast_one] using
      (ManuscriptChain.Real.zeta_series_summable (s := 2*k+1) (by omega)))
  intro n
  rw [integral_norm_seriesTerm]
  apply one_div_le_one_div_of_le (by positivity)
  apply pow_le_pow_left₀ (by positivity)
  push_cast
  nlinarith [Nat.cast_nonneg a, Nat.cast_nonneg n]

theorem density_moment_eq_tsum (k a : ℕ) {u : ℝ} (hu : u ∈ Ioo 0 1) :
    u^a * density k u = ∑' n, seriesTerm k a n u := by
  have hnorm : ‖-(u^2)‖ < 1 := by
    rw [norm_neg, Real.norm_of_nonneg (sq_nonneg _)]
    nlinarith [hu.1, hu.2]
  have h := (hasSum_geometric_of_norm_lt_one hnorm).mul_left (logMonomial a (2*k) u)
  have ht : (fun n => seriesTerm k a n u) =
      (fun n => logMonomial a (2*k) u * (-(u^2))^n) := by
    funext n
    unfold seriesTerm logMonomial
    rw [show -(u^2) = (-1 : ℝ)*u^2 by ring, mul_pow, ← pow_mul, pow_add]
    ring
  rw [ht, h.tsum_eq]
  unfold density logMonomial
  simp only [sub_neg_eq_add]
  ring

theorem moment_series {k : ℕ} (hk : k ≠ 0) (a : ℕ) :
    moment k a = ∑' n : ℕ,
      (-1 : ℝ)^n / (((a+2*n : ℕ) : ℝ)+1)^(2*k+1) := by
  calc
    _ = ∫ u : ℝ in Ioo 0 1, ∑' n, seriesTerm k a n u := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
      exact density_moment_eq_tsum k a hu
    _ = ∑' n, ∫ u : ℝ in Ioo 0 1, seriesTerm k a n u :=
      (integral_tsum_of_summable_integral_norm (seriesTerm_integrable k a)
        (summable_integral_norm_seriesTerm hk a)).symm
    _ = _ := by simp_rw [seriesTerm, integral_const_mul, integral_logMonomial, mul_one_div]

/-- The zeroth moment is the actual ordered odd-beta value, including k=0. -/
theorem zeroth_moment (k : ℕ) : moment k 0 = betaOdd k := by
  by_cases hk : k = 0
  · subst k
    have h := BetaOneMoments.zeroth_moment
    rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
      ← MeasureTheory.integral_Ioo_eq_integral_Ioc] at h
    simpa [moment, density, betaOdd] using h
  · rw [moment_series hk]
    simp only [betaOdd, if_neg hk]
    congr 1
    funext n
    simp

def betaHarmonic (k r : ℕ) : ℚ :=
  ∑ n ∈ Finset.range r, (-1 : ℚ)^n / ((2*n+1 : ℕ) : ℚ)^(2*k+1)

/-- Exact even moments of the printed measure at every k, including k=0. -/
theorem even_moment (k r : ℕ) :
    moment k (2*r) = (-1 : ℝ)^r * (betaOdd k - (betaHarmonic k r : ℝ)) := by
  induction r with
  | zero => simp [zeroth_moment, betaHarmonic]
  | succ r ih =>
    have h := moment_add_two k (2*r)
    have he : 2*(r+1) = 2*r+2 := by omega
    rw [he]
    rw [ih] at h
    have hs : (-1 : ℝ)^r * (-1 : ℝ)^r = 1 := by
      rw [← mul_pow]
      norm_num
    have hh : (betaHarmonic k (r+1) : ℝ) = (betaHarmonic k r : ℝ) +
        (-1 : ℝ)^r / (2*(r : ℝ)+1)^(2*k+1) := by
      simp [betaHarmonic, Finset.sum_range_succ]
    have hs' : ((-1 : ℝ)^r * (-1 : ℝ)^r) / (2*(r : ℝ)+1)^(2*k+1) =
        1 / (2*(r : ℝ)+1)^(2*k+1) := by rw [hs]
    rw [hh, pow_succ]
    push_cast at h
    linear_combination h - hs'

/-- Positive definiteness for every finite matrix of the actual measure. -/
theorem momentMatrix_posDef (k d : ℕ) :
    (ManuscriptChain.Moments.momentMatrix (measure k) d).PosDef :=
  ManuscriptChain.Moments.momentMatrix_posDef (measure_nonzero k)
    (fun i j => integrable_monomial k _)

def pencil (k N h : ℕ) (x : ℝ) : Matrix (Fin h) (Fin h) ℝ :=
  fun i j => (-1 : ℝ)^(N+i.val+j.val) *
    (x - (betaHarmonic k (N+i.val+j.val) : ℝ))

theorem pencil_beta_entry (k N h : ℕ) (i j : Fin h) :
    pencil k N h (betaOdd k) i j =
      ∫ u : ℝ, u^(2*N+2*i.val+2*j.val) ∂measure k := by
  rw [integral_monomial]
  have he : 2*N+2*i.val+2*j.val = 2*(N+i.val+j.val) := by omega
  rw [he]
  exact (even_moment k _).symm

/-- The actual manuscript beta pencil is positive definite for all k,N,h. -/
theorem pencil_beta_posDef (k N h : ℕ) : (pencil k N h (betaOdd k)).PosDef := by
  let choose : Fin h → Fin (N+2*h+1) := fun i => ⟨N+2*i.val, by have := i.isLt; omega⟩
  have hc : Function.Injective choose := by
    intro i j hij
    have hv := congrArg Fin.val hij
    apply Fin.ext
    dsimp [choose] at hv
    omega
  have hp := (momentMatrix_posDef k (N+2*h+1)).submatrix hc
  convert hp using 1
  ext i j
  rw [pencil_beta_entry]
  simp only [Matrix.submatrix_apply, ManuscriptChain.Moments.momentMatrix, choose]
  congr 1
  funext u
  congr 1
  omega

end LeanPaper.BetaOddMeasureActual

#print axioms LeanPaper.BetaOddMeasureActual.zeroth_moment
#print axioms LeanPaper.BetaOddMeasureActual.even_moment
#print axioms LeanPaper.BetaOddMeasureActual.pencil_beta_posDef
