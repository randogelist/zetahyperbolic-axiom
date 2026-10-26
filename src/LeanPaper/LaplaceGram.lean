import LeanPaper.LaplaceMomentDerivative
import LeanPaper.Section3OrthogonalKernel

/-! The actual positive Gram matrix for every positive Laplace scale. -/
noncomputable section
open scoped BigOperators
open MeasureTheory Set Polynomial

namespace LeanPaper.LaplaceGram
open ManuscriptChain LaplaceDensityDerivative LaplaceMomentDerivative

def weightedDensity (p : Real.Parameters) (τ y : ℝ) : ℝ :=
  rationalWeight p 0 y * laplaceDensity p.k τ y

theorem weightedDensity_pos (p : Real.Parameters) {τ y : ℝ}
    (hτ : 0 < τ) (hy : 0 < y) : 0 < weightedDensity p τ y := by
  unfold weightedDensity rationalWeight
  simpa only [Nat.mul_zero, pow_zero, one_mul] using
    mul_pos (Zetahyperbolic.D_real_ratio_pos p.N p.K p.m hy)
      (laplaceDensity_pos p.k hτ hy)

theorem measurable_weightedDensity (p : Real.Parameters) (τ : ℝ) :
    Measurable (weightedDensity p τ) :=
  (measurable_rationalWeight p 0).mul (measurable_laplaceDensity p.k τ)

def weightedMeasure (p : Real.Parameters) (τ : ℝ) : Measure ℝ :=
  (volume.restrict (Ioi 0)).withDensity
    (fun y => ENNReal.ofReal (weightedDensity p τ y))

instance weightedMeasure_nullSingleton (p : Real.Parameters) (τ : ℝ) :
    NullSingletonClass (weightedMeasure p τ) := by
  unfold weightedMeasure
  infer_instance

theorem weightedMeasure_nonzero (p : Real.Parameters) {τ : ℝ}
    (hτ : 0 < τ) : weightedMeasure p τ ≠ 0 := by
  have hac : volume.restrict (Ioi (0 : ℝ)) ≪ weightedMeasure p τ := by
    apply withDensity_absolutelyContinuous'
      (measurable_weightedDensity p τ).ennreal_ofReal.aemeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    exact ne_of_gt (ENNReal.ofReal_pos.mpr (weightedDensity_pos p hτ hy))
  intro hzero
  rw [hzero] at hac
  have h := Measure.absolutelyContinuous_zero_iff.mp hac
  have hu := congrArg (fun μ : Measure ℝ => μ Set.univ) h
  simp at hu

def momentMeasure (p : Real.Parameters) (τ : ℝ) : Measure ℝ :=
  (weightedMeasure p τ).map (fun y : ℝ => y^2)

theorem momentMeasure_nonzero (p : Real.Parameters) {τ : ℝ}
    (hτ : 0 < τ) : momentMeasure p τ ≠ 0 :=
  (Measure.map_ne_zero_iff (by fun_prop)).2 (weightedMeasure_nonzero p hτ)

instance momentMeasure_nullSingleton (p : Real.Parameters) (τ : ℝ) :
    NullSingletonClass (momentMeasure p τ) := by
  constructor
  intro t
  rw [momentMeasure, Measure.map_apply (by fun_prop) (measurableSet_singleton t)]
  have hq : (X^2 - C t : ℝ[X]) ≠ 0 := by
    intro h
    have hcoeff := congrArg (fun q : ℝ[X] => q.coeff 2) h
    norm_num at hcoeff
  have hz := (Polynomial.finite_setOfPred_isRoot hq).measure_zero (weightedMeasure p τ)
  have hs : (fun y : ℝ => y^2) ⁻¹' {t} =
      {y | Polynomial.IsRoot (X^2 - C t : ℝ[X]) y} := by
    ext y
    simp [Polynomial.IsRoot, sub_eq_zero]
  rw [hs]
  exact hz

theorem monomial_weightedDensity (p : Real.Parameters) (τ : ℝ) (e : ℕ) (y : ℝ) :
    y^(2 * e) * weightedDensity p τ y =
      rationalWeight p e y * laplaceDensity p.k τ y := by
  unfold weightedDensity rationalWeight
  simp only [Nat.mul_zero, pow_zero, one_mul]
  ring

theorem integral_momentMeasure (p : Real.Parameters) {τ : ℝ}
    (hτ : 0 < τ) (e : ℕ) :
    (∫ t, t^e ∂momentMeasure p τ) =
      ∫ y in Ioi (0 : ℝ), rationalWeight p e y * laplaceDensity p.k τ y := by
  rw [momentMeasure, integral_map (by fun_prop) (by fun_prop), weightedMeasure,
    integral_withDensity_eq_integral_toReal_smul
      (measurable_weightedDensity p τ).ennreal_ofReal (by simp)]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
  rw [ENNReal.toReal_ofReal (weightedDensity_pos p hτ hy).le]
  simp only [smul_eq_mul, ← pow_mul]
  rw [mul_comm, monomial_weightedDensity]

theorem integrable_moment (p : Real.Parameters) {τ : ℝ}
    (hτ : 0 < τ) (e : ℕ) :
    Integrable (fun t : ℝ => t^e) (momentMeasure p τ) := by
  rw [momentMeasure, integrable_map_measure (by fun_prop) (by fun_prop),
    weightedMeasure, integrable_withDensity_iff_integrable_smul'
      (measurable_weightedDensity p τ).ennreal_ofReal (by simp)]
  apply (integrableOn_weightedDensity p e hτ).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
  rw [ENNReal.toReal_ofReal (weightedDensity_pos p hτ hy).le]
  simp only [Function.comp_def, smul_eq_mul, ← pow_mul]
  rw [mul_comm (weightedDensity p τ y), monomial_weightedDensity]

/-- Literal deformed moments, including their definition away from positive scales. -/
def gram (p : Real.Parameters) (τ : ℝ) : Matrix (Fin p.h) (Fin p.h) ℝ :=
  fun i j => ∫ y in Ioi (0 : ℝ),
    rationalWeight p (i.val + j.val) y * laplaceDensity p.k τ y

theorem gram_eq_momentMatrix (p : Real.Parameters) {τ : ℝ} (hτ : 0 < τ) :
    gram p τ = Moments.momentMatrix (momentMeasure p τ) p.h := by
  ext i j
  exact (integral_momentMeasure p hτ _).symm

theorem gram_posDef (p : Real.Parameters) {τ : ℝ} (hτ : 0 < τ) :
    (gram p τ).PosDef := by
  rw [gram_eq_momentMatrix p hτ]
  exact Moments.momentMatrix_posDef (momentMeasure_nonzero p hτ)
    (fun i j => integrable_moment p hτ _)

/-- At every positive scale the constructed monic polynomials are orthogonal
for the actual deformed measure, with the stated positive squared norms. -/
theorem monicPolynomial_integral_pairing (p : Real.Parameters) {τ : ℝ}
    (hτ : 0 < τ) (i j : Fin p.h) :
    (∫ t, (Section3MonicOrthogonal.monicPolynomial (gram_posDef p hτ) i).eval t *
      (Section3MonicOrthogonal.monicPolynomial (gram_posDef p hτ) j).eval t
        ∂momentMeasure p τ) =
      if i = j then Section3MonicOrthogonal.squaredNorm (gram_posDef p hτ) i else 0 := by
  change (∫ t, (Polynomial.ofFn p.h
      (Section3MonicOrthogonal.orthogonalCoefficients (gram_posDef p hτ) i)).eval t *
      (Polynomial.ofFn p.h
      (Section3MonicOrthogonal.orthogonalCoefficients (gram_posDef p hτ) j)).eval t
        ∂momentMeasure p τ) = _
  rw [← Moments.bilinear_eq_integral_mul
    (fun a b => integrable_moment p hτ (a.val + b.val))]
  rw [← gram_eq_momentMatrix p hτ]
  exact Section3MonicOrthogonal.orthogonalCoefficients_pairing (gram_posDef p hτ) i j

theorem squaredNorm_eq_integral (p : Real.Parameters) {τ : ℝ}
    (hτ : 0 < τ) (i : Fin p.h) :
    Section3MonicOrthogonal.squaredNorm (gram_posDef p hτ) i =
      ∫ t, ((Section3MonicOrthogonal.monicPolynomial (gram_posDef p hτ) i).eval t)^2
        ∂momentMeasure p τ := by
  simpa [pow_two] using (monicPolynomial_integral_pairing p hτ i i).symm

theorem weightedDensity_one (p : Real.Parameters) (y : ℝ) :
    weightedDensity p 1 y = ConcreteMoment.weightedDensity p y := by
  simp only [weightedDensity, rationalWeight, Nat.mul_zero, pow_zero, one_mul,
    laplaceDensity_one, ConcreteMoment.weightedDensity]

/-- The deformed Gram family passes through the actual manuscript Gram matrix. -/
theorem gram_one (p : Real.Parameters) (hp : Real.Admissible p) :
    gram p 1 = Real.gram p (Real.zeta p.weight) := by
  ext i j
  rw [Hyperbolic.gram_eq_weighted_integral p hp
    (Hyperbolic.poleIntegralIdentity p.k hp.k_pos)]
  change (∫ y in Ioi (0 : ℝ),
      rationalWeight p (i.val + j.val) y * laplaceDensity p.k 1 y) = _
  simp_rw [← monomial_weightedDensity, weightedDensity_one]

def gramDerivative (p : Real.Parameters) (τ : ℝ) : Matrix (Fin p.h) (Fin p.h) ℝ :=
  fun i j => ∫ y in Ioi (0 : ℝ),
    rationalWeight p (i.val + j.val) y * densityDerivative p.k τ y

theorem gram_hasDerivAt (p : Real.Parameters) {τ : ℝ} (hτ : 0 < τ)
    (i j : Fin p.h) : HasDerivAt (fun t => gram p t i j) (gramDerivative p τ i j) τ :=
  weightedMoment_hasDerivAt p _ hτ

end LeanPaper.LaplaceGram

#print axioms LeanPaper.LaplaceGram.gram_posDef
#print axioms LeanPaper.LaplaceGram.monicPolynomial_integral_pairing
#print axioms LeanPaper.LaplaceGram.squaredNorm_eq_integral
#print axioms LeanPaper.LaplaceGram.gram_one
#print axioms LeanPaper.LaplaceGram.gram_hasDerivAt
