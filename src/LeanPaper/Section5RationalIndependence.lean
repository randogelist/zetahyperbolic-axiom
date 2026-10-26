import LeanPaper.Section5DualSpectrum
import Mathlib.Tactic

/-!
# Theorem 5.2(1): the manuscript's rational polynomial independence hypothesis

Rational row independence proves a nonzero rational coefficient-Gram
determinant. Casting that determinant to the reals removes the former
real row-separation assumption. The final theorem accepts the manuscript's
linearly independent rational polynomials and their actual coefficients.
-/
noncomputable section
open Matrix Polynomial
open scoped BigOperators

namespace LeanPaper.Section5RationalIndependence
open ManuscriptChain PaperOrder.PrincipalTheorems LeanPaper.Section5DualSpectrum

/-- Rational row independence is preserved by coefficient embedding into R.
The proof uses the nonzero rational Gram determinant, not a scalar-extension
independence premise. -/
theorem real_rows_separate_of_rational_injective {h K : ℕ}
    (c : Matrix (Fin h) (Fin (K+1)) ℚ) (hc : Function.Injective c.vecMul) :
    coefficientRowsSeparate (realCoefficients c) := by
  have hqpd : (c * c.transpose).PosDef := by
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.PosDef.mul_conjTranspose_self c hc
  have hqdet : (c * c.transpose).det ≠ 0 :=
    ne_of_gt hqpd.det_pos
  have hmap : coefficientSlope (realCoefficients c) =
      (c * c.transpose).map (Rat.castHom ℝ) := by
    ext i j
    simp [coefficientSlope, realCoefficients, Matrix.mul_apply]
  have hGram : coefficientSlope (realCoefficients c) =
      (c.map (Rat.castHom ℝ)) * (c.map (Rat.castHom ℝ)).conjTranspose := by
    ext i j
    simp [coefficientSlope, realCoefficients, Matrix.mul_apply]
  have hps : (coefficientSlope (realCoefficients c)).PosSemidef := by
    rw [hGram]
    exact Matrix.posSemidef_self_mul_conjTranspose _
  have hrdet : (coefficientSlope (realCoefficients c)).det ≠ 0 := by
    rw [hmap, (Rat.castHom ℝ).map_det]
    exact_mod_cast hqdet
  have hpd := hps.posDef_iff_det_ne_zero.mpr hrdet
  intro v hv
  by_contra hnone
  push_neg at hnone
  have hdot := hpd.dotProduct_mulVec_pos hv
  have hid : star v ⬝ᵥ ((coefficientSlope (realCoefficients c)).mulVec v) =
      ∑ r : Fin (K+1), (∑ i : Fin h, v i * realCoefficients c i r)^2 := by
    rw [← coefficientSlope_quadratic_sos]
    simp [dotProduct, Matrix.mulVec, Pi.star_apply, star_trivial,
      Finset.mul_sum, mul_assoc]
  rw [hid] at hdot
  simp [hnone] at hdot

/-- Literal rational coefficient independence suffices for exact dual degree
and reality of every complex root. -/
theorem rational_independent_dual_hyperbolicity {h K : ℕ} (s : ℕ)
    (c : Matrix (Fin h) (Fin (K+1)) ℚ) (hc : LinearIndependent ℚ c.row) :
    (Real.dualDelta s c).natDegree = h ∧
      ∀ z : ℂ, Polynomial.eval₂ (algebraMap ℚ ℂ) z (Real.dualDelta s c) = 0 →
        z.im = 0 := by
  have hsep := real_rows_separate_of_rational_injective c
    (Matrix.vecMul_injective_iff.mpr hc)
  exact ⟨actual_dual_degree s c hsep, actual_dual_zeros_real s c hsep⟩

/-- The actual truncated coefficient matrix of rational polynomials. -/
def polynomialCoefficients {h : ℕ} (K : ℕ) (A : Fin h → ℚ[X]) :
    Matrix (Fin h) (Fin (K+1)) ℚ := fun i r => (A i).coeff r.val

theorem polynomialCoefficients_independent {h K : ℕ}
    (A : Fin h → ℚ[X]) (hA : LinearIndependent ℚ A)
    (hdegree : ∀ i, (A i).natDegree ≤ K) :
    LinearIndependent ℚ (polynomialCoefficients K A).row := by
  rw [Fintype.linearIndependent_iff]
  intro v hv i
  apply (Fintype.linearIndependent_iff.mp hA) v _ i
  apply Polynomial.ext
  intro r
  simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_smul, smul_eq_mul,
    Polynomial.coeff_zero]
  by_cases hr : r ≤ K
  · have he := congrFun hv (⟨r, by omega⟩ : Fin (K+1))
    simpa [polynomialCoefficients, Matrix.row, Pi.smul_apply, Finset.sum_apply,
      smul_eq_mul] using he
  · have hz : ∀ j, (A j).coeff r = 0 := fun j =>
      Polynomial.coeff_eq_zero_of_natDegree_lt ((hdegree j).trans_lt (lt_of_not_ge hr))
    simp [hz]

/-- The finite-dimensional assertion of Theorem 5.2(1), for exactly the
linearly independent polynomial family and degree cutoff in the manuscript. -/
theorem theorem_5_2_polynomial_hyperbolicity {h K : ℕ}
    (A : Fin h → ℚ[X]) (hA : LinearIndependent ℚ A)
    (hdegree : ∀ i, (A i).natDegree ≤ K) :
    (Real.dualDelta 7 (polynomialCoefficients K A)).natDegree = h ∧
      ∀ z : ℂ, Polynomial.eval₂ (algebraMap ℚ ℂ) z
        (Real.dualDelta 7 (polynomialCoefficients K A)) = 0 → z.im = 0 :=
  rational_independent_dual_hyperbolicity 7 (polynomialCoefficients K A)
    (polynomialCoefficients_independent A hA hdegree)

end LeanPaper.Section5RationalIndependence

#print axioms LeanPaper.Section5RationalIndependence.theorem_5_2_polynomial_hyperbolicity
