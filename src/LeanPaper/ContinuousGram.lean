import LeanPaper.ContinuousWeightMoments
import LeanPaper.ImportedSection3.ActualPoleKernel

/-! The corrected Proposition 3.2: actual positive measure, all moments,
positive definite Gram matrix and real-rooted continuous pencil. -/
noncomputable section
open scoped BigOperators
open MeasureTheory Set Polynomial
namespace LeanPaper.ContinuousGram
open ManuscriptChain ContinuousDensityNormalization ContinuousWeightMoments

def weightedDensity (p : Real.Parameters) (s : ℝ) (y : ℝ) : ℝ :=
  (Zetahyperbolic.D_real p.N (y ^ 2)) ^ (2 * p.m) /
    Zetahyperbolic.D_real p.K (y ^ 2) * correctedDensity s y

theorem weightedDensity_pos (p : Real.Parameters) (s : ℝ) (hs : 1 < s) {y : ℝ} (hy : 0 < y) :
    0 < weightedDensity p s y :=
  mul_pos (Zetahyperbolic.D_real_ratio_pos p.N p.K p.m hy)
    (correctedDensity_pos hs hy)

theorem measurable_weightedDensity (p : Real.Parameters) (s : ℝ) :
    Measurable (weightedDensity p s) := by
  unfold weightedDensity Zetahyperbolic.D_real
  apply Measurable.mul _ (measurable_correctedDensity s)
  fun_prop

def weightedMeasure (p : Real.Parameters) (s : ℝ) : Measure ℝ :=
  (volume.restrict (Ioi 0)).withDensity
    (fun y => ENNReal.ofReal (weightedDensity p s y))

instance weightedMeasure_nullSingleton (p : Real.Parameters) (s : ℝ) :
    NullSingletonClass (weightedMeasure p s) := by
  unfold weightedMeasure
  infer_instance

theorem weightedMeasure_nonzero (p : Real.Parameters) (s : ℝ) (hs : 1 < s) : weightedMeasure p s ≠ 0 := by
  have hac : volume.restrict (Ioi (0 : ℝ)) ≪ weightedMeasure p s := by
    apply withDensity_absolutelyContinuous'
      (measurable_weightedDensity p s).ennreal_ofReal.aemeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    exact ne_of_gt (ENNReal.ofReal_pos.mpr (weightedDensity_pos p s hs hy))
  intro hzero
  rw [hzero] at hac
  have h := Measure.absolutelyContinuous_zero_iff.mp hac
  have hu := congrArg (fun μ : Measure ℝ => μ Set.univ) h
  simp at hu

/-- The actual moment measure in the variable `t = y^2`. -/
def momentMeasure (p : Real.Parameters) (s : ℝ) : Measure ℝ :=
  (weightedMeasure p s).map (fun y : ℝ => y ^ 2)

theorem momentMeasure_nonzero (p : Real.Parameters) (s : ℝ) (hs : 1 < s) : momentMeasure p s ≠ 0 := by
  exact (Measure.map_ne_zero_iff (by fun_prop)).2 (weightedMeasure_nonzero p s hs)

instance momentMeasure_nullSingleton (p : Real.Parameters) (s : ℝ) :
    NullSingletonClass (momentMeasure p s) := by
  constructor
  intro t
  rw [momentMeasure, Measure.map_apply (by fun_prop) (measurableSet_singleton t)]
  have hq : (X ^ 2 - C t : ℝ[X]) ≠ 0 := by
    intro h
    have hcoeff := congrArg (fun q : ℝ[X] => q.coeff 2) h
    norm_num at hcoeff
  have hz := (Polynomial.finite_setOfPred_isRoot hq).measure_zero (weightedMeasure p s)
  have hs : (fun y : ℝ => y ^ 2) ⁻¹' {t} =
      {y | Polynomial.IsRoot (X ^ 2 - C t : ℝ[X]) y} := by
    ext y
    simp [Polynomial.IsRoot, sub_eq_zero]
  rw [hs]
  exact hz

/-- The pushforward moment equals the original positive-half-line integral. -/
theorem integral_momentMeasure (p : Real.Parameters) (s : ℝ) (hs : 1 < s) (e : ℕ) :
    (∫ t, t ^ e ∂momentMeasure p s) =
      ∫ y in Ioi (0 : ℝ), y ^ (2 * e) * weightedDensity p s y := by
  rw [momentMeasure, integral_map (by fun_prop) (by fun_prop), weightedMeasure,
    integral_withDensity_eq_integral_toReal_smul
      (measurable_weightedDensity p s).ennreal_ofReal (by simp)]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
  rw [ENNReal.toReal_ofReal (weightedDensity_pos p s hs hy).le]
  simp only [smul_eq_mul]
  rw [← pow_mul]
  ring

/-- Moment integrability in the two coordinates is equivalent. -/
theorem integrable_momentMeasure_iff (p : Real.Parameters) (s : ℝ) (hs : 1 < s) (e : ℕ) :
    Integrable (fun t : ℝ => t ^ e) (momentMeasure p s) ↔
      IntegrableOn (fun y : ℝ => y ^ (2 * e) * weightedDensity p s y) (Ioi 0) := by
  rw [momentMeasure, integrable_map_measure (by fun_prop) (by fun_prop),
    weightedMeasure, integrable_withDensity_iff_integrable_smul'
      (measurable_weightedDensity p s).ennreal_ofReal (by simp)]
  apply integrable_congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
  rw [ENNReal.toReal_ofReal (weightedDensity_pos p s hs hy).le]
  simp only [Function.comp_def, smul_eq_mul]
  rw [← pow_mul]
  ring

/-- Every polynomial in `y^2` is integrable against the base density. -/
theorem integrableOn_polynomial_density (s : ℝ) (hs : 1 < s) (q : ℝ[X]) :
    IntegrableOn (fun y : ℝ => q.eval (y ^ 2) * correctedDensity s y) (Ioi 0) := by
  have hi := integrable_finsetSum q.support (fun e _ =>
    (ContinuousWeightMoments.integrableOn_monomial_density hs e).const_mul (q.coeff e))
  apply hi.congr
  filter_upwards [] with y
  symm
  simp only [Polynomial.eval_eq_sum, Polynomial.sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro e _
  rw [← pow_mul]
  ring

/-- The denominator is at least one, so weighted moments are dominated by
polynomial moments of the already-integrable base density. -/
theorem integrableOn_weightedDensity_moment (p : Real.Parameters) (s : ℝ) (hs : 1 < s) (e : ℕ) :
    IntegrableOn (fun y : ℝ => y ^ (2 * e) * weightedDensity p s y) (Ioi 0) := by
  let q : ℝ[X] :=
    (∏ j ∈ Finset.Icc 1 p.N, (X + C ((j : ℝ) ^ 2))) ^ (2 * p.m) * X ^ e
  have heval (y : ℝ) : q.eval (y ^ 2) =
      (Zetahyperbolic.D_real p.N (y ^ 2)) ^ (2 * p.m) * y ^ (2 * e) := by
    simp only [q, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_prod,
      Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C,
      Zetahyperbolic.D_real, ← pow_mul]
  have hi := integrableOn_polynomial_density s hs q
  apply hi.mono' ((measurable_id.pow_const _).mul
    (measurable_weightedDensity p s)).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
  have hypos : 0 < y := hy
  rw [Real.norm_eq_abs, abs_of_nonneg (by
    exact mul_nonneg (pow_nonneg hypos.le _) (weightedDensity_pos p s hs hypos).le)]
  rw [heval]
  have hratio := div_le_self
    (pow_nonneg (Zetahyperbolic.D_real_pos p.N (show 0 < y ^ 2 by positivity)).le (2 * p.m))
    (Zetahyperbolic.D_real_ge_one p.K (show 0 < y ^ 2 by positivity))
  have hmul := mul_le_mul_of_nonneg_right hratio (correctedDensity_pos hs hypos).le
  have htotal := mul_le_mul_of_nonneg_left hmul (pow_nonneg hypos.le (2 * e))
  simpa [weightedDensity, mul_assoc, mul_left_comm, mul_comm] using htotal


def baseMatrix (p : Real.Parameters) (s : ℝ) : Matrix (Fin p.h) (Fin p.h) ℝ :=
  Moments.momentMatrix (momentMeasure p s) p.h

theorem baseMatrix_isSymm (p : Real.Parameters) (s : ℝ) : (baseMatrix p s).IsSymm := by
  ext i j
  simp [baseMatrix, Moments.momentMatrix, Nat.add_comm]

theorem baseMatrix_posDef (p : Real.Parameters) (s : ℝ) (hs : 1 < s) :
    (baseMatrix p s).PosDef := by
  apply Moments.momentMatrix_posDef (momentMeasure_nonzero p s hs)
  intro i j
  exact (integrable_momentMeasure_iff p s hs _).mpr
    (integrableOn_weightedDensity_moment p s hs _)

theorem baseMatrix_integral (p : Real.Parameters) (s : ℝ) (hs : 1 < s)
    (i j : Fin p.h) :
    baseMatrix p s i j =
      ∫ y : ℝ in Ioi 0, y ^ (2 * (i.val + j.val)) * weightedDensity p s y :=
  integral_momentMeasure p s hs _

/-- Literal positive integral of the corrected Proposition 3.2. -/
theorem baseMatrix_entry_exact (p : Real.Parameters) (s : ℝ) (hs : 1 < s)
    (i j : Fin p.h) :
    baseMatrix p s i j =
      ∫ y : ℝ in Ioi 0,
        (Zetahyperbolic.D_real p.N (y ^ 2) ^ (2 * p.m) * y ^ (2 * (i.val + j.val)) /
          Zetahyperbolic.D_real p.K (y ^ 2)) * correctedDensity s y := by
  rw [baseMatrix_integral p s hs]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro y _
  unfold weightedDensity
  ring

/-- The inherited real-exponent slope is the literal coefficient of 3.2. -/
theorem gamma_exact (p : Real.Parameters) (s : ℝ) (a : Fin p.h) :
    PaperAdvances.Proposition3_2.gamma p s a =
      (PoleDiagonalization.poleIndex p a : ℝ) ^ (s - 1) *
        (((Real.D p.N).eval (PoleDiagonalization.poleNode p a) : ℚ) : ℝ) ^
          (2 * p.m - 1) /
        (((Polynomial.derivative (Real.tailD p)).eval (PoleDiagonalization.poleNode p a) : ℚ) : ℝ) := by
  unfold PaperAdvances.Proposition3_2.gamma PaperAdvances.Proposition3_2.exponentScale
    PoleDiagonalization.poleWeight
  push_cast
  change (_ / _ * (PoleDiagonalization.poleIndex p a : ℝ) ^ (2 * p.k)) *
    ((PoleDiagonalization.poleIndex p a : ℝ) ^ (s - 1) /
      (PoleDiagonalization.poleIndex p a : ℝ) ^ (2 * p.k)) = _
  have ha : (PoleDiagonalization.poleIndex p a : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (PoleDiagonalization.poleIndex_pos p a))
  have hd : (((Polynomial.derivative (Real.tailD p)).eval
      (PoleDiagonalization.poleNode p a) : ℚ) : ℝ) ≠ 0 := by
    exact_mod_cast PoleDiagonalization.tailD_derivative_eval_ne_zero p _
      (PoleDiagonalization.poleIndex_mem p a)
  field_simp
  ring

def pencil (p : Real.Parameters) (s : ℝ) : Spectral.SymmetricAffinePencil p.h :=
  PaperAdvances.Proposition3_2.pencil p s (riemannZeta (s : ℂ)).re
    (baseMatrix p s) (baseMatrix_isSymm p s)

def factorization (p : Real.Parameters) (s : ℝ) (hs : 1 < s) :
    Spectral.RootFactorization (pencil p s) :=
  PaperAdvances.Proposition3_2.factorization p s _ _ (baseMatrix_isSymm p s)
    (baseMatrix_posDef p s hs)

theorem pencil_degree (p : Real.Parameters) (s : ℝ) (hs : 1 < s) :
    (pencil p s).detPolynomial.natDegree = p.h :=
  (factorization p s hs).natDegree_eq

theorem pencil_all_complex_roots_real (p : Real.Parameters) (s : ℝ) (hs : 1 < s)
    (z : ℂ) (hz : (pencil p s).detPolynomial.eval₂ (algebraMap ℝ ℂ) z = 0) :
    z.im = 0 :=
  (factorization p s hs).complex_root_im_zero z hz

theorem weightedDensity_odd (p : Real.Parameters) (y : ℝ) :
    weightedDensity p (p.weight : ℝ) y = ConcreteMoment.weightedDensity p y := by
  unfold weightedDensity ConcreteMoment.weightedDensity
  rw [show (p.weight : ℝ) = 2 * (p.k : ℝ) + 1 by
    simp [Real.Parameters.weight], correctedDensity_odd]

theorem baseMatrix_odd (p : Real.Parameters) (hp : Real.Admissible p) :
    baseMatrix p (p.weight : ℝ) = Real.gram p (Real.zeta p.weight) := by
  have hs : (1 : ℝ) < p.weight := by
    simp only [Real.Parameters.weight, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
    have hk : (0 : ℝ) < p.k := by exact_mod_cast hp.k_pos
    linarith
  ext i j
  rw [baseMatrix_integral p _ hs,
    Hyperbolic.gram_eq_weighted_integral p hp (Hyperbolic.poleIntegralIdentity p.k hp.k_pos)]
  simp_rw [weightedDensity_odd]

/-- The corrected continuous pencil coincides with the original one at every
admissible odd integer, with its original zeta center and its original slope. -/
theorem pencil_odd (p : Real.Parameters) (hp : Real.Admissible p) (x : ℝ) :
    (pencil p (p.weight : ℝ)).matrixAt x = Real.gram p x := by
  have hw : 1 < p.weight := by unfold Real.Parameters.weight; have := hp.k_pos; omega
  change baseMatrix p (p.weight : ℝ) +
    (x - (riemannZeta ((p.weight : ℝ) : ℂ)).re) • PaperAdvances.Proposition3_2.slope p (p.weight : ℝ) = _
  rw [Complex.ofReal_natCast, baseMatrix_odd p hp, ← Real.zeta_eq_riemannZeta_re hw,
    ← PaperAdvances.Theorem3_8_Actual.actual_derivative_eq_real_slope]
  ext i j
  simp only [Matrix.add_apply, Matrix.smul_apply, Real.gram, Real.evalQ,
    Real.realPolynomial, Real.pencil, Polynomial.eval_map, Polynomial.eval₂_add,
    Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_X, Real.derivativeMatrix,
    smul_eq_mul]
  ring

/-- The printed normalization is a fixed positive multiple of the corrected
one at every real weight, not only at odd integers. -/
theorem printedDensity_eq_scale_corrected (s y : ℝ) :
    printedDensity s y = (_root_.Real.pi / 2) * correctedDensity s y := by
  have hp : (0 : ℝ) < 2 * _root_.Real.pi := by positivity
  have hr : (2 * _root_.Real.pi) ^ s =
      (2 * _root_.Real.pi) ^ (s - 1) * (2 * _root_.Real.pi) := by
    simpa only [sub_add_cancel, _root_.Real.rpow_one] using
      (_root_.Real.rpow_add hp (s - 1) 1)
  unfold printedDensity correctedDensity
  rw [hr]
  ring

def printedBaseMatrix (p : Real.Parameters) (s : ℝ) : Matrix (Fin p.h) (Fin p.h) ℝ :=
  (_root_.Real.pi / 2) • baseMatrix p s

theorem printedBaseMatrix_entry (p : Real.Parameters) (s : ℝ) (hs : 1 < s)
    (i j : Fin p.h) :
    printedBaseMatrix p s i j = printedMoment p s i j := by
  change (_root_.Real.pi / 2) * baseMatrix p s i j = _
  rw [baseMatrix_entry_exact p s hs i j, ← integral_const_mul]
  unfold printedMoment
  simp_rw [printedDensity_eq_scale_corrected]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro y _
  ring

theorem printedBaseMatrix_posDef (p : Real.Parameters) (s : ℝ) (hs : 1 < s) :
    (printedBaseMatrix p s).PosDef :=
  (baseMatrix_posDef p s hs).smul (by positivity)

theorem printedBaseMatrix_isSymm (p : Real.Parameters) (s : ℝ) :
    (printedBaseMatrix p s).IsSymm := by
  ext i j
  simp [printedBaseMatrix, baseMatrix, Moments.momentMatrix, Nat.add_comm]

def printedPencil (p : Real.Parameters) (s : ℝ) : Spectral.SymmetricAffinePencil p.h :=
  PaperAdvances.Proposition3_2.pencil p s (riemannZeta (s : ℂ)).re
    (printedBaseMatrix p s) (printedBaseMatrix_isSymm p s)

/-- The spectral part of 3.2 remains valid even with its printed coefficient.
Only its claimed odd-weight coincidence requires the documented correction. -/
theorem printed_pencil_degree_and_real_roots (p : Real.Parameters) (s : ℝ) (hs : 1 < s) :
    (printedPencil p s).detPolynomial.natDegree = p.h ∧
      ∀ z : ℂ, (printedPencil p s).detPolynomial.eval₂ (algebraMap ℝ ℂ) z = 0 →
        z.im = 0 := by
  let f := PaperAdvances.Proposition3_2.factorization p s _ _
    (printedBaseMatrix_isSymm p s) (printedBaseMatrix_posDef p s hs)
  exact ⟨f.natDegree_eq, f.complex_root_im_zero⟩

end LeanPaper.ContinuousGram
