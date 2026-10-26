import LeanPaper.LaplaceGram
import LeanPaper.MatrixCurveJacobi

/-!
# The actual Laplace Gram determinant derivative in Theorem 3.8(2)

The derivative under each moment integral is established analytically in the
preceding modules. Positivity supplies invertibility, Jacobi differentiates the
determinant, and the constructed monic orthogonal kernel identifies the trace.
-/
noncomputable section
open scoped BigOperators
open MeasureTheory Set Matrix

namespace LeanPaper.LaplaceKernelJacobi
open ManuscriptChain LaplaceDensityDerivative LaplaceMomentDerivative LaplaceGram
open Section3MonicOrthogonal

theorem traceDerivative_eq_integral (p : Real.Parameters) {τ : ℝ} (hτ : 0 < τ) :
    ((gram p τ)⁻¹ * gramDerivative p τ).trace =
      ∫ y in Ioi (0 : ℝ), kernel (gram_posDef p hτ) (y^2) (y^2) *
        rationalWeight p 0 y * densityDerivative p.k τ y := by
  have hi (i j : Fin p.h) :
      IntegrableOn (fun y => (gram p τ)⁻¹ i j *
        (rationalWeight p (i.val + j.val) y * densityDerivative p.k τ y)) (Ioi 0) :=
    (integrableOn_weightedDerivative p _ hτ).const_mul _
  calc
    ((gram p τ)⁻¹ * gramDerivative p τ).trace =
        ∑ i, ∑ j, ∫ y in Ioi (0 : ℝ), (gram p τ)⁻¹ i j *
          (rationalWeight p (i.val + j.val) y * densityDerivative p.k τ y) := by
      simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
        gramDerivative, integral_const_mul, Nat.add_comm]
    _ = ∫ y in Ioi (0 : ℝ), ∑ i, ∑ j, (gram p τ)⁻¹ i j *
          (rationalWeight p (i.val + j.val) y * densityDerivative p.k τ y) := by
      rw [integral_finsetSum _ (fun i _ =>
        integrable_finsetSum _ (fun j _ => hi i j))]
      apply Finset.sum_congr rfl
      intro i _
      rw [integral_finsetSum _ (fun j _ => hi i j)]
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with y
      rw [kernel_eq_inverseGram]
      simp only [monomialVector, dotProduct, Matrix.mulVec,
        Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      simp only [rationalWeight, Nat.mul_zero, pow_zero, one_mul, Nat.mul_add,
        pow_add, ← pow_mul]
      ring

/-- The printed Laplace parameter formula, with its actual density and the
actual monic orthogonal-polynomial kernel, holds at every positive scale. -/
theorem laplace_logDet_hasDerivAt (p : Real.Parameters) {τ : ℝ} (hτ : 0 < τ) :
    HasDerivAt (fun t : ℝ => _root_.Real.log ((gram p t).det))
      (∫ y in Ioi (0 : ℝ), kernel (gram_posDef p hτ) (y^2) (y^2) *
        rationalWeight p 0 y * densityDerivative p.k τ y) τ := by
  have h := MatrixCurveJacobi.generic_logDet_hasDerivAt
    (gram_hasDerivAt p hτ) (ne_of_gt (gram_posDef p hτ).det_pos)
  rwa [traceDerivative_eq_integral p hτ] at h

/-- At scale one the curve is based at the original manuscript matrix. -/
theorem actual_gram_laplace_logDet (p : Real.Parameters) (hp : Real.Admissible p) :
    gram p 1 = Real.gram p (Real.zeta p.weight) ∧
    HasDerivAt (fun t : ℝ => _root_.Real.log ((gram p t).det))
      (∫ y in Ioi (0 : ℝ), kernel (gram_posDef p (by norm_num : (0 : ℝ) < 1))
        (y^2) (y^2) * rationalWeight p 0 y * densityDerivative p.k 1 y) 1 :=
  ⟨gram_one p hp, laplace_logDet_hasDerivAt p (by norm_num)⟩

end LeanPaper.LaplaceKernelJacobi

#print axioms LeanPaper.LaplaceKernelJacobi.laplace_logDet_hasDerivAt
#print axioms LeanPaper.LaplaceKernelJacobi.actual_gram_laplace_logDet
