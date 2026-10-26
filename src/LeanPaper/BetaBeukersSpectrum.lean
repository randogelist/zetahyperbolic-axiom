import LeanPaper.BetaBeukersMoments
import LeanPaper.BeukersPolynomialSpectrum

/-!
# Proposition 5.3: the actual beta(4) integral pencil

The family `A` consists of rational polynomials in `u`; the manuscript's
polynomials in `Q[x^4]` are their evaluations at `u=x^4`. Independence is
required over Q and is transported to real coefficient-Gram positivity.
The constant matrix is calculated from the actual beta moments, so neither
positivity of the integral form nor a moment-identification premise is used.
-/

noncomputable section
open scoped BigOperators
open MeasureTheory Polynomial Matrix

namespace ManuscriptChain.BetaBeukers
open Beukers BeukersPolynomialSpectrum
open LeanPaper.Section5RationalIndependence LeanPaper.Section5DualSpectrum
open PaperOrder.CoreAlgebra PaperOrder.PrincipalTheorems

def betaConstant (r t : ℕ) : ℚ :=
  if r = t then -betaHarmonic 4 (2*r)
  else (betaHarmonic 3 (2*r)-betaHarmonic 3 (2*t)) / (12*((r : ℚ)-(t : ℚ)))

theorem betaConstant_swap (r t : ℕ) : betaConstant r t = betaConstant t r := by
  unfold betaConstant
  by_cases h : r = t
  · subst t
    simp
  · have htr : t ≠ r := fun htr => h htr.symm
    simp only [if_neg h, if_neg htr]
    have hd : (t : ℚ)-(r : ℚ) = -((r : ℚ)-(t : ℚ)) := by ring
    rw [hd, mul_neg, div_neg]
    ring

theorem beta_moment_eq_constant (r t : ℕ) :
    (∫ z, z.1^(4*r)*z.2^(4*t)*betaDensity z ∂squareMeasure) =
      (betaConstant r t : ℝ) + (if r = t then betaValue 4 else 0) := by
  by_cases h : r = t
  · subst t
    rw [beta_diagonal_moment]
    simp [betaConstant] <;> ring
  · rw [beta_offdiagonal_moment r t h]
    simp [betaConstant, h]

def betaConstantMatrix {h K : ℕ} (c : Fin h → Fin (K+1) → ℚ) :
    Matrix (Fin h) (Fin h) ℚ := fun i j =>
  ∑ r, ∑ t, c i r * c j t * betaConstant r.val t.val

theorem betaConstantMatrix_symmetric {h K : ℕ}
    (c : Fin h → Fin (K+1) → ℚ) : (betaConstantMatrix c).IsSymm := by
  have hsym (i j : Fin h) : betaConstantMatrix c i j = betaConstantMatrix c j i := by
    unfold betaConstantMatrix
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro t ht
    apply Finset.sum_congr rfl
    intro r hr
    rw [betaConstant_swap r.val t.val]
    ring
  ext i j
  simpa only [Matrix.transpose_apply] using hsym j i

private theorem fourth_pair_expansion {K : ℕ}
    (c d : Fin (K+1) → ℚ) (z : ℝ × ℝ) :
    coefficientEval c (z.1^4) * coefficientEval d (z.2^4) * betaDensity z =
      ∑ r : Fin (K+1), ∑ t : Fin (K+1),
        ((c r : ℝ)*(d t : ℝ)) * (z.1^(4*r.val)*z.2^(4*t.val)*betaDensity z) := by
  unfold coefficientEval
  simp only [Finset.sum_mul, Finset.mul_sum, ← pow_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r hr
  apply Finset.sum_congr rfl
  intro t ht
  ring

theorem fourth_pair_integrable {K : ℕ} (c d : Fin (K+1) → ℚ) :
    Integrable (fun z => coefficientEval c (z.1^4) * coefficientEval d (z.2^4) *
      betaDensity z) squareMeasure := by
  have hi : Integrable (fun z => ∑ r : Fin (K+1), ∑ t : Fin (K+1),
      ((c r : ℝ)*(d t : ℝ)) * (z.1^(4*r.val)*z.2^(4*t.val)*betaDensity z))
      squareMeasure := by
    apply integrable_finset_sum
    intro r hr
    apply integrable_finset_sum
    intro t ht
    exact (beta_monomial_integrable (4*r.val) (4*t.val)).const_mul _
  apply hi.congr
  exact Filter.Eventually.of_forall (fun z => (fourth_pair_expansion c d z).symm)

theorem integral_fourth_pair {h K : ℕ}
    (c : Fin h → Fin (K+1) → ℚ) (i j : Fin h) :
    (∫ z, coefficientEval (c i) (z.1^4) * coefficientEval (c j) (z.2^4) *
      betaDensity z ∂squareMeasure) =
      (betaConstantMatrix c i j : ℝ) +
        betaValue 4 * coefficientSlope (realCoefficients c) i j := by
  have hexpand :
      (∫ z, coefficientEval (c i) (z.1^4) * coefficientEval (c j) (z.2^4) *
        betaDensity z ∂squareMeasure) =
      ∑ r : Fin (K+1), ∑ t : Fin (K+1),
        ((c i r : ℝ)*(c j t : ℝ)) *
          (∫ z, z.1^(4*r.val)*z.2^(4*t.val)*betaDensity z ∂squareMeasure) := by
    simp_rw [fourth_pair_expansion]
    rw [integral_finset_sum]
    · apply Finset.sum_congr rfl
      intro r hr
      rw [integral_finset_sum]
      · apply Finset.sum_congr rfl
        intro t ht
        exact integral_const_mul _ _
      · intro t ht
        exact (beta_monomial_integrable (4*r.val) (4*t.val)).const_mul _
    · intro r hr
      apply integrable_finset_sum
      intro t ht
      exact (beta_monomial_integrable (4*r.val) (4*t.val)).const_mul _
  rw [hexpand]
  simp only [beta_moment_eq_constant, mul_add, Finset.sum_add_distrib]
  simp [betaConstantMatrix, coefficientSlope, realCoefficients,
    mul_ite, Fin.val_inj, Finset.mul_sum, mul_comm, mul_left_comm, mul_assoc]

def betaIntegralMatrix {h : ℕ} (A : Fin h → ℚ[X]) : Matrix (Fin h) (Fin h) ℝ :=
  fun i j => ∫ z, (A i).eval₂ (Rat.castHom ℝ) (z.1^4) *
    (A j).eval₂ (Rat.castHom ℝ) (z.2^4) * betaDensity z ∂squareMeasure

theorem betaIntegralMatrix_eq {h K : ℕ} (A : Fin h → ℚ[X])
    (hdegree : ∀ i, (A i).natDegree ≤ K) (i j : Fin h) :
    betaIntegralMatrix A i j =
      (betaConstantMatrix (polynomialCoefficients K A) i j : ℝ) +
        betaValue 4 * coefficientSlope (realCoefficients (polynomialCoefficients K A)) i j := by
  unfold betaIntegralMatrix
  simpa only [coefficientEval_polynomialCoefficients A hdegree] using
    integral_fourth_pair (polynomialCoefficients K A) i j

def betaIntegralPencil {h : ℕ} (K : ℕ) (A : Fin h → ℚ[X]) :
    Matrix (Fin h) (Fin h) ℝ[X] := fun i j =>
  C (betaIntegralMatrix A i j) + (X-C (betaValue 4)) *
    C (coefficientSlope (realCoefficients (polynomialCoefficients K A)) i j)

def betaSpectralPencil {h K : ℕ} (A : Fin h → ℚ[X])
    (hA : LinearIndependent ℚ A) (hdegree : ∀ i, (A i).natDegree ≤ K) :
    PositiveSlopePencil h where
  constant := (betaConstantMatrix (polynomialCoefficients K A)).map (Rat.castHom ℝ)
  slope := coefficientSlope (realCoefficients (polynomialCoefficients K A))
  constant_symmetric := (betaConstantMatrix_symmetric _).map _
  slope_posDef := polynomial_slope_posDef A hA hdegree

theorem betaIntegralPencil_eq_spectral {h K : ℕ} (A : Fin h → ℚ[X])
    (hA : LinearIndependent ℚ A) (hdegree : ∀ i, (A i).natDegree ≤ K) :
    betaIntegralPencil K A = (betaSpectralPencil A hA hdegree).polynomialMatrix := by
  funext i j
  change C (betaIntegralMatrix A i j) + (X-C (betaValue 4)) *
      C (coefficientSlope (realCoefficients (polynomialCoefficients K A)) i j) =
    C ((betaConstantMatrix (polynomialCoefficients K A) i j : ℚ) : ℝ) +
      X*C (coefficientSlope (realCoefficients (polynomialCoefficients K A)) i j)
  rw [betaIntegralMatrix_eq A hdegree]
  let c : Fin h → Fin (K+1) → ℚ := fun a r => (A a).coeff r.val
  change C ((betaConstantMatrix c i j : ℝ) +
      betaValue 4 * coefficientSlope (realCoefficients c) i j) +
      (X-C (betaValue 4)) * C (coefficientSlope (realCoefficients c) i j) =
    C (betaConstantMatrix c i j : ℝ) + X*C (coefficientSlope (realCoefficients c) i j)
  simp only [Polynomial.C_add, Polynomial.C_mul]
  ring

theorem betaIntegralPencil_derivative {h : ℕ} (K : ℕ) (A : Fin h → ℚ[X]) :
    (fun i j => (betaIntegralPencil K A i j).derivative) =
      (coefficientSlope (realCoefficients (polynomialCoefficients K A))).map C := by
  funext i j
  simp [betaIntegralPencil]

/-- The exact finite spectral consequence of Proposition 5.3 for the actual
polynomials `A_i(x^4)` and their positive coefficient-Gram derivative. -/
theorem proposition_5_3_integral_polynomial_hyperbolicity {h K : ℕ}
    (A : Fin h → ℚ[X]) (hA : LinearIndependent ℚ A)
    (hdegree : ∀ i, (A i).natDegree ≤ K) :
    (coefficientSlope (realCoefficients (polynomialCoefficients K A))).PosDef ∧
    (Matrix.det (betaIntegralPencil K A)).natDegree = h ∧
    ∀ z : ℂ, (Matrix.det (betaIntegralPencil K A)).eval₂ (algebraMap ℝ ℂ) z = 0 →
      z.im = 0 := by
  refine ⟨polynomial_slope_posDef A hA hdegree, ?_, ?_⟩
  · rw [betaIntegralPencil_eq_spectral A hA hdegree]
    exact positiveSlopePencil_degree (betaSpectralPencil A hA hdegree)
  · intro z hz
    rw [betaIntegralPencil_eq_spectral A hA hdegree] at hz
    exact positiveSlopePencil_every_complex_root_real (betaSpectralPencil A hA hdegree) z hz

end ManuscriptChain.BetaBeukers

#print axioms ManuscriptChain.BetaBeukers.integral_fourth_pair
#print axioms ManuscriptChain.BetaBeukers.proposition_5_3_integral_polynomial_hyperbolicity
