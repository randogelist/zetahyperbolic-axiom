import LeanPaper.BeukersIntegralPencil
import LeanPaper.Section5RationalIndependence

/-!
# The actual polynomial Beukers pencil and its finite spectrum

The entries below are defined by integrals of the actual rational polynomials
against the constructed Beukers measure. Their affine continuation is proved
equal to the rational dual pencil, rather than postulated as a moment bridge.
Rational polynomial independence then supplies the positive coefficient-Gram
slope, exact determinant degree and reality of all complex roots.

This is the finite polynomial construction. No infinite-dimensional Krein
decomposition, positive/negative cone, or irrationality estimate is asserted.
-/

noncomputable section
open scoped BigOperators
open MeasureTheory Polynomial Matrix

namespace ManuscriptChain.BeukersPolynomialSpectrum

open ManuscriptChain.Beukers
open LeanPaper.Section5RationalIndependence LeanPaper.Section5DualSpectrum
open PaperOrder.CoreAlgebra PaperOrder.PrincipalTheorems

/-- The truncated coefficient evaluation is the actual polynomial evaluation
when the cutoff includes the polynomial's degree. -/
theorem coefficientEval_polynomialCoefficients {h K : ℕ}
    (A : Fin h → ℚ[X]) (hdegree : ∀ i, (A i).natDegree ≤ K)
    (i : Fin h) (x : ℝ) :
    coefficientEval (polynomialCoefficients K A i) x =
      (A i).eval₂ (Rat.castHom ℝ) x := by
  rw [Polynomial.eval₂_eq_sum_range' (Rat.castHom ℝ)
    (Nat.lt_succ_of_le (hdegree i)) x]
  simp only [coefficientEval, polynomialCoefficients, Rat.coe_castHom]
  exact Fin.sum_univ_eq_sum_range
    (fun n => ((A i).coeff n : ℝ) * x^n) (K+1)

/-- The polynomial bilinear integrand is genuinely integrable for the actual
weighted measure, including when its integral vanishes. -/
theorem polynomial_integrable {h K : ℕ}
    (A : Fin h → ℚ[X]) (hdegree : ∀ i, (A i).natDegree ≤ K)
    (i j : Fin h) :
    Integrable (fun z : ℝ × ℝ =>
      (A i).eval₂ (Rat.castHom ℝ) z.1 * (A j).eval₂ (Rat.castHom ℝ) z.2)
      beukersMeasure := by
  rw [beukersMeasure, integrable_withDensity_iff_integrable_smul'
    density_measurable.ennreal_ofReal (by simp)]
  apply (polynomial_pair_integrable
    (polynomialCoefficients K A i) (polynomialCoefficients K A j)).congr
  filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioo)]
    with z hz
  rw [ENNReal.toReal_ofReal (density_strictly_positive_on_square z hz).le,
    coefficientEval_polynomialCoefficients A hdegree,
    coefficientEval_polynomialCoefficients A hdegree]
  simp only [smul_eq_mul]
  ring

/-- The actual polynomial integral matrix at the zeta center. -/
def polynomialIntegralMatrix {h : ℕ} (A : Fin h → ℚ[X]) :
    Matrix (Fin h) (Fin h) ℝ := fun i j =>
  ∫ z, (A i).eval₂ (Rat.castHom ℝ) z.1 *
    (A j).eval₂ (Rat.castHom ℝ) z.2 ∂beukersMeasure

/-- Identification at the center is proved from the actual measure's moments. -/
theorem polynomialIntegralMatrix_eq_dualEntry {h K : ℕ}
    (A : Fin h → ℚ[X]) (hdegree : ∀ i, (A i).natDegree ≤ K)
    (i j : Fin h) :
    polynomialIntegralMatrix A i j =
      (Real.dualEntry 7 (polynomialCoefficients K A) i j).eval₂
        (Rat.castHom ℝ) (Real.zeta 7) := by
  unfold polynomialIntegralMatrix
  rw [integral_beukersMeasure]
  simpa only [coefficientEval_polynomialCoefficients A hdegree] using
    integral_polynomial_pair_eq_dualEntry (polynomialCoefficients K A) i j

/-- The affine pencil defined by the actual integral at zeta(7) and the
coefficient-Gram slope. -/
def integralPolynomialPencil {h : ℕ} (K : ℕ) (A : Fin h → ℚ[X]) :
    Matrix (Fin h) (Fin h) ℝ[X] := fun i j =>
  C (polynomialIntegralMatrix A i j) +
    (X - C (Real.zeta 7)) *
      C (coefficientSlope (realCoefficients (polynomialCoefficients K A)) i j)

/-- The integral-defined pencil is precisely the existing rational pencil,
coefficientwise embedded into the real numbers. -/
theorem integralPolynomialPencil_eq_dualEntry {h K : ℕ}
    (A : Fin h → ℚ[X]) (hdegree : ∀ i, (A i).natDegree ≤ K) :
    integralPolynomialPencil K A = fun i j =>
      (Real.dualEntry 7 (polynomialCoefficients K A) i j).map (Rat.castHom ℝ) := by
  funext i j
  have hslope :
      coefficientSlope (realCoefficients (polynomialCoefficients K A)) i j =
        (dualSlopeMatrix (polynomialCoefficients K A) i j : ℝ) := by
    simp [coefficientSlope, realCoefficients, dualSlopeMatrix]
  change C (polynomialIntegralMatrix A i j) +
    (X - C (Real.zeta 7)) *
      C (coefficientSlope (realCoefficients (polynomialCoefficients K A)) i j) = _
  rw [polynomialIntegralMatrix_eq_dualEntry A hdegree, hslope]
  let c : Fin h → Fin (K+1) → ℚ := fun a r => (A a).coeff r.val
  change C ((Real.dualEntry 7 c i j).eval₂ (Rat.castHom ℝ) (Real.zeta 7)) +
    (X - C (Real.zeta 7)) * C (dualSlopeMatrix c i j : ℝ) =
      (Real.dualEntry 7 c i j).map (Rat.castHom ℝ)
  simp only [dualEntry_affine, Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_C,
    Polynomial.eval₂_X, Polynomial.map_add, Polynomial.map_mul,
    Polynomial.map_C, Polynomial.map_X, Rat.coe_castHom,
    Polynomial.C_add, Polynomial.C_mul]
  ring

/-- Differentiation of the integral-defined pencil gives exactly the
coefficient Gram matrix, without a measure-positivity hypothesis. -/
theorem integralPolynomialPencil_derivative {h : ℕ} (K : ℕ)
    (A : Fin h → ℚ[X]) :
    (fun i j => (integralPolynomialPencil K A i j).derivative) =
      (coefficientSlope (realCoefficients (polynomialCoefficients K A))).map C := by
  funext i j
  simp [integralPolynomialPencil]

/-- The actual rational polynomial independence proves strict positivity of
the slope over the reals; real independence is not an additional premise. -/
theorem polynomial_slope_posDef {h K : ℕ}
    (A : Fin h → ℚ[X]) (hA : LinearIndependent ℚ A)
    (hdegree : ∀ i, (A i).natDegree ≤ K) :
    (coefficientSlope (realCoefficients (polynomialCoefficients K A))).PosDef := by
  apply coefficientSlope_posDef
  apply real_rows_separate_of_rational_injective
  exact Matrix.vecMul_injective_iff.mpr (polynomialCoefficients_independent A hA hdegree)

/-- The determinant of the actual integral-defined affine pencil. -/
def integralPolynomialDeterminant {h : ℕ} (K : ℕ) (A : Fin h → ℚ[X]) : ℝ[X] :=
  Matrix.det (integralPolynomialPencil K A)

theorem integralPolynomialDeterminant_eq {h K : ℕ}
    (A : Fin h → ℚ[X]) (hdegree : ∀ i, (A i).natDegree ≤ K) :
    integralPolynomialDeterminant K A =
      (Real.dualDelta 7 (polynomialCoefficients K A)).map (Rat.castHom ℝ) := by
  unfold integralPolynomialDeterminant
  rw [integralPolynomialPencil_eq_dualEntry A hdegree]
  exact ((Polynomial.mapRingHom (Rat.castHom ℝ)).map_det
    (fun i j => Real.dualEntry 7 (polynomialCoefficients K A) i j)).symm

/-- Exact degree and real-rootedness now apply to the determinant defined
from the actual Beukers polynomial integrals. -/
theorem integral_polynomial_hyperbolicity {h K : ℕ}
    (A : Fin h → ℚ[X]) (hA : LinearIndependent ℚ A)
    (hdegree : ∀ i, (A i).natDegree ≤ K) :
    (integralPolynomialDeterminant K A).natDegree = h ∧
      ∀ z : ℂ, (integralPolynomialDeterminant K A).eval₂ (algebraMap ℝ ℂ) z = 0 →
        z.im = 0 := by
  have hs := theorem_5_2_polynomial_hyperbolicity A hA hdegree
  constructor
  · rw [integralPolynomialDeterminant_eq A hdegree, Polynomial.natDegree_map]
    exact hs.1
  · intro z hz
    rw [integralPolynomialDeterminant_eq A hdegree, Polynomial.eval₂_map] at hz
    rw [Subsingleton.elim ((algebraMap ℝ ℂ).comp (Rat.castHom ℝ))
      (algebraMap ℚ ℂ)] at hz
    exact hs.2 z hz

end ManuscriptChain.BeukersPolynomialSpectrum

#print axioms ManuscriptChain.BeukersPolynomialSpectrum.polynomial_integrable
#print axioms ManuscriptChain.BeukersPolynomialSpectrum.integralPolynomialPencil_eq_dualEntry
#print axioms ManuscriptChain.BeukersPolynomialSpectrum.polynomial_slope_posDef
#print axioms ManuscriptChain.BeukersPolynomialSpectrum.integral_polynomial_hyperbolicity
