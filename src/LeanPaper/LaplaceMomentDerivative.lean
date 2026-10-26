import LeanPaper.LaplaceMomentBounds
import LeanPaper.RebuildKernelBridge
import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# Theorem 3.8(2): differentiation of the actual rational-weight moments

The local majorant is the negative derivative density at half the current
positive scale. Its integrability is proved from the exact moment bounds;
neither differentiation under the integral nor a domination certificate is
assumed.
-/

noncomputable section
open scoped BigOperators Topology
open MeasureTheory Set Polynomial Filter

namespace LeanPaper.LaplaceDensityDerivative

theorem measurable_exponentialSeries (m : ℕ) (τ : ℝ) :
    Measurable (fun y : ℝ => exponentialSeries m (2 * Real.pi * y) τ) := by
  unfold exponentialSeries
  exact Measurable.tsum (fun n => by fun_prop)

theorem measurable_laplaceDensity (k : ℕ) (τ : ℝ) : Measurable (laplaceDensity k τ) := by
  unfold laplaceDensity
  exact (measurable_const.mul (measurable_id.pow_const _)).mul
    (measurable_exponentialSeries _ τ)

theorem measurable_densityDerivative (k : ℕ) (τ : ℝ) :
    Measurable (densityDerivative k τ) := by
  unfold densityDerivative
  exact (measurable_const.mul (measurable_id.pow_const _)).mul
    ((by fun_prop : Measurable (fun y : ℝ => -(2 * Real.pi * y))).mul
      (measurable_exponentialSeries _ τ))

theorem exponentialSeries_nonneg (m : ℕ) (c τ : ℝ) : 0 ≤ exponentialSeries m c τ := by
  unfold exponentialSeries
  exact tsum_nonneg (fun n => by positivity)

theorem exponentialSeries_antitone_scale (m : ℕ) {c a τ : ℝ}
    (hc : 0 < c) (ha : 0 < a) (haτ : a ≤ τ) :
    exponentialSeries m c τ ≤ exponentialSeries m c a := by
  apply tsum_le_tsum _ (summable_terms m hc (lt_of_lt_of_le ha haτ))
    (summable_terms m hc ha)
  intro n
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.exp_le_exp.mpr
  have h := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left haτ hc.le)
    (show (0 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) by positivity)
  linarith

theorem laplaceDensity_pos (k : ℕ) {τ y : ℝ} (hτ : 0 < τ) (hy : 0 < y) :
    0 < laplaceDensity k τ y := by
  have hs : 0 < exponentialSeries (2 * k) (2 * Real.pi * y) τ :=
    (summable_terms (2 * k) (by positivity : 0 < 2 * Real.pi * y) hτ).tsum_pos
      (fun n => by positivity) 0 (by positivity)
  unfold laplaceDensity
  exact mul_pos (by positivity) hs

theorem densityDerivative_nonpos (k : ℕ) (τ : ℝ) {y : ℝ} (hy : 0 < y) :
    densityDerivative k τ y ≤ 0 := by
  unfold densityDerivative
  apply mul_nonpos_of_nonneg_of_nonpos (by positivity)
  exact mul_nonpos_of_nonpos_of_nonneg (by positivity)
    (exponentialSeries_nonneg _ _ _)

theorem densityDerivative_norm_le (k : ℕ) {a τ y : ℝ}
    (ha : 0 < a) (haτ : a ≤ τ) (hy : 0 < y) :
    ‖densityDerivative k τ y‖ ≤ -densityDerivative k a y := by
  rw [Real.norm_eq_abs, abs_of_nonpos (densityDerivative_nonpos k τ hy)]
  have hs := exponentialSeries_antitone_scale (2 * k + 1)
    (by positivity : 0 < 2 * Real.pi * y) ha haτ
  have h := mul_le_mul_of_nonneg_left hs
    (show 0 ≤ (2 * (2 * Real.pi)^(2 * k) / (Nat.factorial (2 * k) : ℝ)) *
      y^(2 * k + 1) * (2 * Real.pi * y) by positivity)
  dsimp only [densityDerivative]
  nlinarith only [h]

end LeanPaper.LaplaceDensityDerivative

namespace LeanPaper.LaplaceMomentDerivative
open ManuscriptChain LaplaceDensityDerivative

def rationalWeight (p : Real.Parameters) (e : ℕ) (y : ℝ) : ℝ :=
  y^(2 * e) * (Zetahyperbolic.D_real p.N (y^2))^(2 * p.m) /
    Zetahyperbolic.D_real p.K (y^2)

def numeratorPolynomial (p : Real.Parameters) (e : ℕ) : ℝ[X] :=
  (∏ j ∈ Finset.Icc 1 p.N, (X + C ((j : ℝ)^2)))^(2 * p.m) * X^e

theorem numeratorPolynomial_eval (p : Real.Parameters) (e : ℕ) (y : ℝ) :
    (numeratorPolynomial p e).eval (y^2) =
      (Zetahyperbolic.D_real p.N (y^2))^(2 * p.m) * y^(2 * e) := by
  simp only [numeratorPolynomial, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_prod, Polynomial.eval_add, Polynomial.eval_X,
    Polynomial.eval_C, Zetahyperbolic.D_real, ← pow_mul]

theorem measurable_rationalWeight (p : Real.Parameters) (e : ℕ) :
    Measurable (rationalWeight p e) := by
  unfold rationalWeight Zetahyperbolic.D_real
  fun_prop

theorem rationalWeight_nonneg (p : Real.Parameters) (e : ℕ) {y : ℝ} (hy : 0 < y) :
    0 ≤ rationalWeight p e y := by
  unfold rationalWeight
  have hD := Zetahyperbolic.D_real_pos p.K (show 0 < y^2 by positivity)
  positivity

/-- Dividing by the positive denominator (at least one) preserves the already
proved polynomial-weighted integrability. -/
theorem integrableOn_rationalWeight_mul (p : Real.Parameters) (e : ℕ)
    {v : ℝ → ℝ} (hv : Measurable v)
    (hint : IntegrableOn (fun y : ℝ => (numeratorPolynomial p e).eval (y^2) * v y) (Ioi 0)) :
    IntegrableOn (fun y : ℝ => rationalWeight p e y * v y) (Ioi 0) := by
  apply hint.norm.mono' ((measurable_rationalWeight p e).mul hv).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
  have hD := Zetahyperbolic.D_real_pos p.K (show 0 < y^2 by positivity)
  have heq : rationalWeight p e y * v y =
      ((numeratorPolynomial p e).eval (y^2) * v y) / Zetahyperbolic.D_real p.K (y^2) := by
    rw [numeratorPolynomial_eval]
    unfold rationalWeight
    ring
  have hnormD : ‖Zetahyperbolic.D_real p.K (y^2)‖ =
      Zetahyperbolic.D_real p.K (y^2) := Real.norm_of_nonneg hD.le
  rw [heq, norm_div, hnormD]
  exact div_le_self (norm_nonneg _)
    (Zetahyperbolic.D_real_ge_one p.K (show 0 < y^2 by positivity))

theorem integrableOn_weightedDensity (p : Real.Parameters) (e : ℕ)
    {τ : ℝ} (hτ : 0 < τ) :
    IntegrableOn (fun y : ℝ => rationalWeight p e y * laplaceDensity p.k τ y) (Ioi 0) :=
  integrableOn_rationalWeight_mul p e (measurable_laplaceDensity p.k τ)
    (integrableOn_polynomial_laplaceDensity p.k hτ (numeratorPolynomial p e))

theorem integrableOn_weightedDerivative (p : Real.Parameters) (e : ℕ)
    {τ : ℝ} (hτ : 0 < τ) :
    IntegrableOn (fun y : ℝ => rationalWeight p e y * densityDerivative p.k τ y) (Ioi 0) :=
  integrableOn_rationalWeight_mul p e (measurable_densityDerivative p.k τ)
    (integrableOn_polynomial_densityDerivative p.k hτ (numeratorPolynomial p e))

/-- The actual weighted moment derivative, with the local majorant constructed. -/
theorem weightedMoment_hasDerivAt (p : Real.Parameters) (e : ℕ)
    {τ : ℝ} (hτ : 0 < τ) :
    HasDerivAt
      (fun t : ℝ => ∫ y : ℝ in Ioi 0, rationalWeight p e y * laplaceDensity p.k t y)
      (∫ y : ℝ in Ioi 0, rationalWeight p e y * densityDerivative p.k τ y) τ := by
  have hhalf : 0 < τ / 2 := half_pos hτ
  let bound : ℝ → ℝ := fun y => rationalWeight p e y * (-densityDerivative p.k (τ / 2) y)
  have hbound_int : Integrable bound (volume.restrict (Ioi 0)) := by
    simpa only [bound, mul_neg] using (integrableOn_weightedDerivative p e hhalf).neg
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioi (0 : ℝ)))
    (F := fun t y => rationalWeight p e y * laplaceDensity p.k t y)
    (F' := fun t y => rationalWeight p e y * densityDerivative p.k t y)
    (bound := bound) (s := Ioi (τ / 2)) (x₀ := τ)
    (Ioi_mem_nhds (by linarith : τ / 2 < τ))
    (Filter.Eventually.of_forall (fun t =>
      ((measurable_rationalWeight p e).mul (measurable_laplaceDensity p.k t)).aestronglyMeasurable))
    (integrableOn_weightedDensity p e hτ)
    ((measurable_rationalWeight p e).mul (measurable_densityDerivative p.k τ)).aestronglyMeasurable
    ?_ hbound_int ?_
  · exact h.2
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    intro t ht
    rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (rationalWeight_nonneg p e hy)]
    exact mul_le_mul_of_nonneg_left
      (densityDerivative_norm_le p.k hhalf (le_of_lt ht) hy) (rationalWeight_nonneg p e hy)
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    intro t ht
    exact (densityDerivative_hasDerivAt p.k (lt_trans hhalf ht) hy).const_mul _

end LeanPaper.LaplaceMomentDerivative

#print axioms LeanPaper.LaplaceMomentDerivative.weightedMoment_hasDerivAt
