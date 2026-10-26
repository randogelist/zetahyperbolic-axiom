import LeanPaper.Section3MonicOrthogonal
import LeanPaper.ShiftedSolidMinors
import LeanPaper.SymmetricPoleSpectrum

/-!
# Theorem 3.8(1): the actual orthogonal-polynomial kernel

The previously constructed monic polynomials are proved orthogonal for the
actual manuscript moment measure. Their squared norms are the integral norms,
and their finite sum kernel is exactly the inverse-Gram kernel, including at
the actual negative-square pole nodes. The resulting pole operator has the
same characteristic polynomial as the symmetric normalized manuscript pencil.

No orthogonality, moment identity, or root certificate is added as an input.
The independent Laplace-parameter differentiation clause of 3.8(2) is not
asserted by this module.
-/

noncomputable section
open scoped BigOperators MatrixOrder
open Matrix Polynomial MeasureTheory

namespace LeanPaper.Section3MonicOrthogonal

variable {n : ℕ} {G : Matrix (Fin n) (Fin n) ℝ}

/-- The monomial evaluation vector, in increasing degree. -/
def monomialVector (n : ℕ) (x : ℝ) : Fin n → ℝ := fun i => x ^ i.val

theorem monicPolynomial_eval (hG : G.PosDef) (i : Fin n) (x : ℝ) :
    (monicPolynomial hG i).eval x =
      ((LDL.lowerInv hG) *ᵥ monomialVector n x) i / LDL.lowerInv hG i i := by
  rw [monicPolynomial, ManuscriptChain.Moments.eval_ofFn_eq_sum]
  simp only [orthogonalCoefficients, mulVec, dotProduct, monomialVector, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- LDL gives the inverse Gram matrix, not merely a formal candidate inverse. -/
theorem gram_inverse_ldl (hG : G.PosDef) :
    G⁻¹ = (LDL.lowerInv hG)ᵀ * (LDL.diag hG)⁻¹ * LDL.lowerInv hG := by
  calc
    G⁻¹ = (LDL.lower hG * LDL.diag hG * (LDL.lower hG)ᴴ)⁻¹ :=
      congrArg Inv.inv (LDL.lower_conj_diag hG).symm
    _ = (LDL.lowerInv hG)ᵀ * (LDL.diag hG)⁻¹ * LDL.lowerInv hG := by
      rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, ← Matrix.conjTranspose_nonsing_inv]
      simp only [LDL.lower, Matrix.inv_inv_of_invertible,
        Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.mul_assoc]

theorem diag_inverse (hG : G.PosDef) :
    (LDL.diag hG)⁻¹ = Matrix.diagonal (fun i => (LDL.diagEntries hG i)⁻¹) := by
  apply Matrix.inv_eq_right_inv
  ext i j
  by_cases hij : i = j
  · subst j
    simp [LDL.diag, Matrix.diagonal_mul_diagonal,
      ne_of_gt (diagonal_positive hG i)]
  · simp [LDL.diag, Matrix.diagonal_mul_diagonal, hij]

/-- The finite monic orthogonal-polynomial sum is the inverse-Gram pairing. -/
theorem kernel_eq_inverseGram (hG : G.PosDef) (t u : ℝ) :
    kernel hG t u = monomialVector n t ⬝ᵥ (G⁻¹ *ᵥ monomialVector n u) := by
  unfold kernel
  simp_rw [monicPolynomial_eval]
  rw [gram_inverse_ldl hG, diag_inverse hG]
  simp only [Matrix.mul_assoc, ← Matrix.mulVec_mulVec]
  rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
  simp only [dotProduct, Matrix.mulVec_diagonal]
  apply Finset.sum_congr rfl
  intro i _
  dsimp only [squaredNorm]
  field_simp [lower_diagonal_ne_zero hG i, ne_of_gt (diagonal_positive hG i)]
  <;> ring

theorem lower_row_pairing (hG : G.PosDef) (i j : Fin n) :
    LDL.lowerInv hG i ⬝ᵥ (G *ᵥ LDL.lowerInv hG j) =
      if i = j then LDL.diagEntries hG i else 0 := by
  have h := congrArg (fun A : Matrix (Fin n) (Fin n) ℝ => A i j)
    (LDL.diag_eq_lowerInv_conj hG)
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.mul_mul_apply,
    Matrix.transpose_transpose, LDL.diag, Matrix.diagonal_apply] using h.symm

/-- The constructed normalized coefficient rows are orthogonal in the Gram form. -/
theorem orthogonalCoefficients_pairing (hG : G.PosDef) (i j : Fin n) :
    orthogonalCoefficients hG i ⬝ᵥ (G *ᵥ orthogonalCoefficients hG j) =
      if i = j then squaredNorm hG i else 0 := by
  have hs :
      orthogonalCoefficients hG i ⬝ᵥ (G *ᵥ orthogonalCoefficients hG j) =
        (LDL.lowerInv hG i ⬝ᵥ (G *ᵥ LDL.lowerInv hG j)) /
          (LDL.lowerInv hG i i * LDL.lowerInv hG j j) := by
    simp only [orthogonalCoefficients, dotProduct, mulVec, Finset.mul_sum,
      Finset.sum_div]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    field_simp [lower_diagonal_ne_zero hG i, lower_diagonal_ne_zero hG j]
    <;> ring
  rw [hs, lower_row_pairing]
  by_cases hij : i = j
  · subst j
    simp [squaredNorm, pow_two]
  · simp [hij]

end LeanPaper.Section3MonicOrthogonal

namespace ManuscriptChain.Moments

theorem eval_ofFn_mul_eq_sum {n : ℕ} (c d : Fin n → ℝ) (x : ℝ) :
    (Polynomial.ofFn n c).eval x * (Polynomial.ofFn n d).eval x =
      ∑ i, ∑ j, (c i * d j) * x ^ (i.val + j.val) := by
  rw [eval_ofFn_eq_sum, eval_ofFn_eq_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [pow_add]
  ring

/-- The actual bilinear moment integral; no product-integrability premise is needed. -/
theorem bilinear_eq_integral_mul {μ : Measure ℝ} {n : ℕ}
    (hm : ∀ i j : Fin n, Integrable (fun x : ℝ => x ^ (i.val + j.val)) μ)
    (c d : Fin n → ℝ) :
    c ⬝ᵥ (momentMatrix μ n *ᵥ d) =
      ∫ x, (Polynomial.ofFn n c).eval x * (Polynomial.ofFn n d).eval x ∂μ := by
  simp_rw [eval_ofFn_mul_eq_sum]
  rw [integral_finsetSum _ (fun i _ =>
    integrable_finsetSum _ (fun j _ => (hm i j).const_mul (c i * d j)))]
  simp only [dotProduct, mulVec, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum _ (fun j _ => (hm i j).const_mul (c i * d j))]
  apply Finset.sum_congr rfl
  intro j _
  rw [integral_const_mul]
  simp only [momentMatrix]
  ring

end ManuscriptChain.Moments

namespace LeanPaper.Section3MonicOrthogonal

open ManuscriptChain

theorem actualGram_eq_momentMatrix (p : Real.Parameters) (hp : Real.Admissible p) :
    Real.gram p (Real.zeta p.weight) =
      Moments.momentMatrix (ConcreteMoment.momentMeasure p) p.h := by
  ext i j
  exact gram_eq_moment p hp i j

/-- Orthogonality and the precise squared norms for the actual manuscript measure. -/
theorem actualMonicPolynomial_integral_pairing
    (p : Real.Parameters) (hp : Real.Admissible p) (i j : Fin p.h) :
    (∫ t, (actualMonicPolynomial p hp i).eval t *
      (actualMonicPolynomial p hp j).eval t ∂ConcreteMoment.momentMeasure p) =
      if i = j then actualSquaredNorm p hp i else 0 := by
  change (∫ t, (Polynomial.ofFn p.h
      (orthogonalCoefficients (actualGram_posDef p hp) i)).eval t *
      (Polynomial.ofFn p.h
      (orthogonalCoefficients (actualGram_posDef p hp) j)).eval t
      ∂ConcreteMoment.momentMeasure p) = _
  rw [← Moments.bilinear_eq_integral_mul
    (fun a b => ConcreteMoment.integrable_moment p (a.val + b.val))]
  rw [← actualGram_eq_momentMatrix p hp]
  exact orthogonalCoefficients_pairing (actualGram_posDef p hp) i j

theorem actualSquaredNorm_eq_integral (p : Real.Parameters)
    (hp : Real.Admissible p) (i : Fin p.h) :
    actualSquaredNorm p hp i =
      ∫ t, ((actualMonicPolynomial p hp i).eval t)^2
        ∂ConcreteMoment.momentMeasure p := by
  simpa [pow_two] using
    (actualMonicPolynomial_integral_pairing p hp i i).symm

/-- Evaluation at the actual negative-square poles gives the previously constructed
pole kernel, with the monic orthogonal polynomials now explicitly identified. -/
theorem actualPoleKernel_entry_eq_kernel (p : Real.Parameters)
    (hp : Real.Admissible p) (a b : Fin p.h) :
    PaperAdvances.Theorem3_8_Actual.actualPoleKernel p a b =
      kernel (actualGram_posDef p hp)
        (PoleDiagonalization.poleNode p a : ℝ)
        (PoleDiagonalization.poleNode p b : ℝ) := by
  rw [kernel_eq_inverseGram]
  simp only [PaperAdvances.Theorem3_8_Actual.actualPoleKernel,
    PaperAdvances.Theorem3_8_Kernel.kernelMatrix_entry,
    Matrix.dot_mulVec_eq_sum_sum,
    PaperAdvances.Theorem3_8_Actual.actualV,
    PaperAdvances.Proposition3_2.vandermonde,
    PoleDiagonalization.poleVandermonde, Matrix.map_apply, Rat.coe_castHom, Rat.cast_pow,
    monomialVector, PaperAdvances.Theorem3_8_Actual.actualGram]

/-- The exact manuscript symmetric spectrum equals the signed orthogonal-polynomial
pole-kernel spectrum, as entire characteristic polynomials (with multiplicities). -/
theorem actual_symmetric_charpoly_eq_orthogonal_kernel
    (p : Real.Parameters) (hp : Real.Admissible p) :
    (OperatorNormDisk.whitened (Real.manuscriptPencil p)).charpoly =
      Matrix.charpoly (fun a b : Fin p.h => PaperAdvances.Theorem3_8_Actual.actualGamma p a *
        kernel (actualGram_posDef p hp)
          (PoleDiagonalization.poleNode p a : ℝ)
          (PoleDiagonalization.poleNode p b : ℝ)) := by
  rw [SymmetricPoleSpectrum.actual_symmetric_charpoly_eq_pole p hp]
  congr 1
  ext a b
  simp only [PaperAdvances.Theorem3_8_Kernel.poleOperator, Matrix.diagonal_mul]
  change PaperAdvances.Theorem3_8_Actual.actualGamma p a *
      PaperAdvances.Theorem3_8_Actual.actualPoleKernel p a b = _
  rw [actualPoleKernel_entry_eq_kernel p hp a b]

end LeanPaper.Section3MonicOrthogonal

#print axioms LeanPaper.Section3MonicOrthogonal.kernel_eq_inverseGram
#print axioms LeanPaper.Section3MonicOrthogonal.actualMonicPolynomial_integral_pairing
#print axioms LeanPaper.Section3MonicOrthogonal.actualSquaredNorm_eq_integral
#print axioms LeanPaper.Section3MonicOrthogonal.actual_symmetric_charpoly_eq_orthogonal_kernel
