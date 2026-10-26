import LeanPaper.BeukersDensityActual
import LeanPaper.BeukersRationalityActual
import LeanPaper.BeukersKreinPolynomialActual
import LeanPaper.ImportedSection56.DualMoments
import Mathlib

/-!
# The actual Beukers measure and its polynomial dual pencil

The moment-series and harmonic formulas refer to a real density times
Lebesgue measure. This file constructs that measure, proves integrability,
and identifies its polynomial bilinear integrals with the rational affine
entries used by the spectral construction. No positivity of the bilinear
form, infinite Krein cone, or arithmetic approximation bound is assumed.
-/

noncomputable section
open scoped BigOperators
open MeasureTheory Set

namespace ManuscriptChain.Beukers

/-- The printed density is genuinely integrable. Its computed integral is
the strictly positive actual zeta value, so the integral is not a default
zero assigned to a nonintegrable function. -/
theorem density_integrable : Integrable density squareMeasure := by
  apply Integrable.of_integral_ne_zero
  have h : (∫ z, density z ∂squareMeasure) = Real.zeta 7 := by
    simpa [Real.harmonic] using diagonal_moment 0
  rw [h]
  exact ne_of_gt (Real.zeta_pos (by norm_num))

/-- Every monomial is bounded by one on the actual open square. -/
theorem density_monomial_integrable (r t : ℕ) :
    Integrable (fun z => z.1 ^ r * z.2 ^ t * density z) squareMeasure := by
  refine density_integrable.mono' ?_ ?_
  · exact (((measurable_fst.pow_const r).mul (measurable_snd.pow_const t)).mul
      density_measurable).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioo)]
      with z hz
    have hd := (density_strictly_positive_on_square z hz).le
    have hx : z.1 ^ r ≤ 1 := pow_le_one₀ hz.1.1.le hz.1.2.le
    have hy : z.2 ^ t ≤ 1 := pow_le_one₀ hz.2.1.le hz.2.2.le
    rw [Real.norm_of_nonneg (mul_nonneg
      (mul_nonneg (pow_nonneg hz.1.1.le _) (pow_nonneg hz.2.1.le _)) hd)]
    calc
      z.1 ^ r * z.2 ^ t * density z ≤ 1 * 1 * density z :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul hx hy (pow_nonneg hz.2.1.le _) (by norm_num)) hd
      _ = density z := by ring

/-- The measure printed in Theorem 5.1, on the actual open unit square. -/
def beukersMeasure : Measure (ℝ × ℝ) :=
  squareMeasure.withDensity (fun z => ENNReal.ofReal (density z))

theorem integral_beukersMeasure (f : ℝ × ℝ → ℝ) :
    (∫ z, f z ∂beukersMeasure) = ∫ z, f z * density z ∂squareMeasure := by
  rw [beukersMeasure, integral_withDensity_eq_integral_toReal_smul
    density_measurable.ennreal_ofReal (by simp)]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioo)]
    with z hz
  rw [ENNReal.toReal_ofReal (density_strictly_positive_on_square z hz).le]
  simp only [smul_eq_mul, mul_comm]

theorem monomial_integrable_beukersMeasure (r t : ℕ) :
    Integrable (fun z : ℝ × ℝ => z.1 ^ r * z.2 ^ t) beukersMeasure := by
  rw [beukersMeasure, integrable_withDensity_iff_integrable_smul'
    density_measurable.ennreal_ofReal (by simp)]
  apply (density_monomial_integrable r t).congr
  filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioo)]
    with z hz
  rw [ENNReal.toReal_ofReal (density_strictly_positive_on_square z hz).le]
  simp only [smul_eq_mul, mul_comm]

/-- The complete two-case moment formula for the actual weighted measure. -/
theorem theorem_5_1_actual_measure (r t : ℕ) :
    (∀ z ∈ square, 0 < density z) ∧
    Integrable (fun z : ℝ × ℝ => z.1 ^ r * z.2 ^ t) beukersMeasure ∧
    (∫ z, z.1 ^ r * z.2 ^ t ∂beukersMeasure) =
      (if r = t then Real.zeta 7 - (Real.harmonic 7 r : ℝ)
        else (offdiagonalRational r t : ℝ)) := by
  refine ⟨density_strictly_positive_on_square,
    monomial_integrable_beukersMeasure r t, ?_⟩
  rw [integral_beukersMeasure]
  by_cases h : r = t
  · subst t
    simpa using diagonal_moment r
  · simpa [h] using offdiagonal_moment_eq_rat r t h

/-- Evaluation of a rational polynomial presented by its finite coefficients. -/
def coefficientEval {K : ℕ} (c : Fin (K + 1) → ℚ) (x : ℝ) : ℝ :=
  ∑ r, (c r : ℝ) * x ^ r.val

private theorem polynomial_pair_expansion {K : ℕ}
    (c d : Fin (K + 1) → ℚ) (z : ℝ × ℝ) :
    coefficientEval c z.1 * coefficientEval d z.2 * density z =
      ∑ r : Fin (K + 1), ∑ t : Fin (K + 1),
        ((c r : ℝ) * (d t : ℝ)) * (z.1 ^ r.val * z.2 ^ t.val * density z) := by
  unfold coefficientEval
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r hr
  apply Finset.sum_congr rfl
  intro t ht
  ring

theorem polynomial_pair_integrable {K : ℕ} (c d : Fin (K + 1) → ℚ) :
    Integrable (fun z => coefficientEval c z.1 * coefficientEval d z.2 * density z)
      squareMeasure := by
  have hi : Integrable (fun z => ∑ r : Fin (K + 1), ∑ t : Fin (K + 1),
      ((c r : ℝ) * (d t : ℝ)) * (z.1 ^ r.val * z.2 ^ t.val * density z))
      squareMeasure := by
    apply integrable_finset_sum
    intro r hr
    apply integrable_finset_sum
    intro t ht
    exact (density_monomial_integrable r.val t.val).const_mul _
  apply hi.congr
  exact Filter.Eventually.of_forall (fun z => (polynomial_pair_expansion c d z).symm)

/-- The finite coefficient form is exactly the actual polynomial integral. -/
theorem integral_polynomial_pair {K : ℕ} (c d : Fin (K + 1) → ℚ) :
    (∫ z, coefficientEval c z.1 * coefficientEval d z.2 * density z ∂squareMeasure) =
      polynomialMomentForm c d := by
  simp_rw [polynomial_pair_expansion]
  rw [integral_finset_sum]
  · unfold polynomialMomentForm
    apply Finset.sum_congr rfl
    intro r hr
    rw [integral_finset_sum]
    · apply Finset.sum_congr rfl
      intro t ht
      exact integral_const_mul _ _
    · intro t ht
      exact (density_monomial_integrable r.val t.val).const_mul _
  · intro r hr
    apply integrable_finset_sum
    intro t ht
    exact (density_monomial_integrable r.val t.val).const_mul _

theorem moment_eq_dualConstant (r t : ℕ) :
    (∫ z, z.1 ^ r * z.2 ^ t * density z ∂squareMeasure) =
      (Real.dualConstant 7 r t : ℝ) + (if r = t then Real.zeta 7 else 0) := by
  rw [theorem_5_1_exact_moments]
  by_cases h : r = t
  · subst t
    simp [Real.dualConstant]
    ring
  · simp [Real.dualConstant, h]

/-- The coefficient form evaluates precisely the existing rational dual entry. -/
theorem polynomialMomentForm_eq_dualEntry {h K : ℕ}
    (c : Fin h → Fin (K + 1) → ℚ) (i j : Fin h) :
    polynomialMomentForm (c i) (c j) =
      Polynomial.eval₂ (Rat.castHom ℝ) (Real.zeta 7) (Real.dualEntry 7 c i j) := by
  have hdiag : (∑ r : Fin (K + 1), ∑ t : Fin (K + 1),
      ((c i r : ℝ) * (c j t : ℝ)) *
        (if r.val = t.val then Real.zeta 7 else 0)) =
      (∑ r : Fin (K + 1), (c i r : ℝ) * (c j r : ℝ)) * Real.zeta 7 := by
    simp [mul_ite, Fin.val_inj, Finset.sum_mul]
  simp only [polynomialMomentForm, moment_eq_dualConstant, mul_add,
    Finset.sum_add_distrib]
  rw [hdiag]
  simp only [Real.dualEntry, Polynomial.eval₂_add, Polynomial.eval₂_mul,
    Polynomial.eval₂_C, Polynomial.eval₂_X, Rat.coe_castHom]
  push_cast
  rfl

/-- Actual integral-to-pencil identification, without an assumed moment bridge. -/
theorem integral_polynomial_pair_eq_dualEntry {h K : ℕ}
    (c : Fin h → Fin (K + 1) → ℚ) (i j : Fin h) :
    (∫ z, coefficientEval (c i) z.1 * coefficientEval (c j) z.2 * density z
      ∂squareMeasure) =
      Polynomial.eval₂ (Rat.castHom ℝ) (Real.zeta 7) (Real.dualEntry 7 c i j) := by
  rw [integral_polynomial_pair, polynomialMomentForm_eq_dualEntry]

end ManuscriptChain.Beukers

#print axioms ManuscriptChain.Beukers.theorem_5_1_actual_measure
#print axioms ManuscriptChain.Beukers.integral_polynomial_pair_eq_dualEntry
