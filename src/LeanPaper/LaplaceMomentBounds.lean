import LeanPaper.LaplaceDensityDerivative
import Theorem_3_1_Hyperbolic_Moments

/-!
# Integrable moments of the scaled density and its derivative

Every positive scale is treated, including the odd exponent in the derivative
series. Exact term integrals reduce the absolute-integrability bound to the
convergent zeta series of exponent `2*e+2`.
-/

noncomputable section
open scoped BigOperators Topology
open MeasureTheory Set Polynomial

namespace LeanPaper.LaplaceDensityDerivative

def momentTerm (m e : ℕ) (τ : ℝ) (n : ℕ) (y : ℝ) : ℝ :=
  ((n + 1 : ℕ) : ℝ)^m * (y^(m + 2 * e + 1) *
    Real.exp (-((2 * Real.pi * τ * ((n + 1 : ℕ) : ℝ)) * y)))

def momentCoefficient (m e : ℕ) (τ : ℝ) : ℝ :=
  (Nat.factorial (m + 2 * e + 1) : ℝ) / (2 * Real.pi * τ)^(m + 2 * e + 2)

theorem momentTerm_integrable (m e n : ℕ) {τ : ℝ} (hτ : 0 < τ) :
    IntegrableOn (momentTerm m e τ n) (Ioi 0) := by
  unfold momentTerm
  exact (ManuscriptChain.Hyperbolic.integrableOn_pow_mul_exp _ (by positivity)).const_mul _

theorem integral_momentTerm (m e n : ℕ) {τ : ℝ} (hτ : 0 < τ) :
    (∫ y : ℝ in Ioi 0, momentTerm m e τ n y) =
      momentCoefficient m e τ * (1 / ((n + 1 : ℕ) : ℝ)^(2 * e + 2)) := by
  unfold momentTerm momentCoefficient
  rw [integral_const_mul, ManuscriptChain.Hyperbolic.integral_pow_mul_exp _ (by positivity)]
  have hn : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  have hc : (2 * Real.pi * τ : ℝ) ≠ 0 := by positivity
  have he : m + 2 * e + 1 + 1 = m + (2 * e + 2) := by omega
  rw [he, mul_pow, pow_add, pow_add]
  field_simp
  simp only [pow_add]

theorem summable_integral_norm_momentTerm (m e : ℕ) {τ : ℝ} (hτ : 0 < τ) :
    Summable (fun n => ∫ y : ℝ in Ioi 0, ‖momentTerm m e τ n y‖) := by
  have h (n : ℕ) : (∫ y : ℝ in Ioi 0, ‖momentTerm m e τ n y‖) =
      momentCoefficient m e τ * (1 / ((n + 1 : ℕ) : ℝ)^(2 * e + 2)) := by
    rw [← integral_momentTerm m e n hτ]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro y hy
    apply Real.norm_of_nonneg
    unfold momentTerm
    exact mul_nonneg (by positivity)
      (mul_nonneg (pow_nonneg (show 0 ≤ y from le_of_lt hy) _) (Real.exp_pos _).le)
  simp_rw [h]
  exact (ManuscriptChain.Real.zeta_series_summable (s := 2 * e + 2) (by omega)).mul_left _

theorem integral_tsum_momentTerm (m e : ℕ) {τ : ℝ} (hτ : 0 < τ) :
    (∫ y : ℝ in Ioi 0, ∑' n, momentTerm m e τ n y) =
      momentCoefficient m e τ * ManuscriptChain.Real.zeta (2 * e + 2) := by
  rw [← integral_tsum_of_summable_integral_norm
    (fun n => momentTerm_integrable m e n hτ)
    (summable_integral_norm_momentTerm m e hτ)]
  simp_rw [integral_momentTerm m e _ hτ]
  rw [tsum_mul_left]
  rfl

theorem integrableOn_tsum_momentTerm (m e : ℕ) {τ : ℝ} (hτ : 0 < τ) :
    IntegrableOn (fun y : ℝ => ∑' n, momentTerm m e τ n y) (Ioi 0) := by
  apply Integrable.of_integral_ne_zero
  rw [integral_tsum_momentTerm m e hτ]
  exact mul_ne_zero (ne_of_gt (by unfold momentCoefficient; positivity))
    (ne_of_gt (ManuscriptChain.Real.zeta_pos (by omega)))

theorem monomial_series_eq_tsum (m e : ℕ) (τ y : ℝ) :
    y^(2 * e) * (y^(m + 1) * exponentialSeries m (2 * Real.pi * y) τ) =
      ∑' n, momentTerm m e τ n y := by
  unfold exponentialSeries
  rw [← tsum_mul_left, ← tsum_mul_left]
  apply tsum_congr
  intro n
  unfold momentTerm
  have hexp : -((2 * Real.pi * y) * τ) * ((n + 1 : ℕ) : ℝ) =
      -((2 * Real.pi * τ * ((n + 1 : ℕ) : ℝ)) * y) := by ring
  rw [hexp]
  simp only [pow_add]
  ring

theorem integrableOn_series_moment (m e : ℕ) {τ : ℝ} (hτ : 0 < τ) :
    IntegrableOn (fun y : ℝ => y^(2 * e) *
      (y^(m + 1) * exponentialSeries m (2 * Real.pi * y) τ)) (Ioi 0) := by
  simp_rw [monomial_series_eq_tsum]
  exact integrableOn_tsum_momentTerm m e hτ

/-- All moments needed for the deformed Gram matrix are integrable. -/
theorem integrableOn_laplaceDensity_moment (k e : ℕ) {τ : ℝ} (hτ : 0 < τ) :
    IntegrableOn (fun y : ℝ => y^(2 * e) * laplaceDensity k τ y) (Ioi 0) := by
  have h := (integrableOn_series_moment (2 * k) e hτ).const_mul
    (2 * (2 * Real.pi)^(2 * k) / (Nat.factorial (2 * k) : ℝ))
  apply h.congr
  filter_upwards [] with y
  unfold laplaceDensity
  ring

def densityDerivative (k : ℕ) (τ y : ℝ) : ℝ :=
  (2 * (2 * Real.pi)^(2 * k) / (Nat.factorial (2 * k) : ℝ)) *
    y^(2 * k + 1) *
    (-(2 * Real.pi * y) * exponentialSeries (2 * k + 1) (2 * Real.pi * y) τ)

theorem densityDerivative_hasDerivAt (k : ℕ) {τ y : ℝ}
    (hτ : 0 < τ) (hy : 0 < y) :
    HasDerivAt (fun t => laplaceDensity k t y) (densityDerivative k τ y) τ :=
  laplaceDensity_hasDerivAt k hτ hy

/-- The derivative density has every required absolute moment as well. -/
theorem integrableOn_densityDerivative_moment (k e : ℕ) {τ : ℝ} (hτ : 0 < τ) :
    IntegrableOn (fun y : ℝ => y^(2 * e) * densityDerivative k τ y) (Ioi 0) := by
  have h := (integrableOn_series_moment (2 * k + 1) e hτ).const_mul
    (-(2 * Real.pi) * (2 * (2 * Real.pi)^(2 * k) / (Nat.factorial (2 * k) : ℝ)))
  apply h.congr
  filter_upwards [] with y
  unfold densityDerivative
  simp only [pow_succ]
  ring

theorem integrableOn_polynomial_laplaceDensity (k : ℕ) {τ : ℝ}
    (hτ : 0 < τ) (q : ℝ[X]) :
    IntegrableOn (fun y : ℝ => q.eval (y^2) * laplaceDensity k τ y) (Ioi 0) := by
  have h := integrable_finsetSum q.support (fun e _ =>
    (integrableOn_laplaceDensity_moment k e hτ).const_mul (q.coeff e))
  apply h.congr
  filter_upwards [] with y
  symm
  simp only [Polynomial.eval_eq_sum, Polynomial.sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro e _
  rw [← pow_mul]
  ring

theorem integrableOn_polynomial_densityDerivative (k : ℕ) {τ : ℝ}
    (hτ : 0 < τ) (q : ℝ[X]) :
    IntegrableOn (fun y : ℝ => q.eval (y^2) * densityDerivative k τ y) (Ioi 0) := by
  have h := integrable_finsetSum q.support (fun e _ =>
    (integrableOn_densityDerivative_moment k e hτ).const_mul (q.coeff e))
  apply h.congr
  filter_upwards [] with y
  symm
  simp only [Polynomial.eval_eq_sum, Polynomial.sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro e _
  rw [← pow_mul]
  ring

end LeanPaper.LaplaceDensityDerivative

#print axioms LeanPaper.LaplaceDensityDerivative.integrableOn_laplaceDensity_moment
#print axioms LeanPaper.LaplaceDensityDerivative.integrableOn_densityDerivative_moment
