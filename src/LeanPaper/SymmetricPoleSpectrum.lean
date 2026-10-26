import LeanPaper.OperatorNormDisk
import LeanPaper.ImportedSection3.ActualPoleKernel
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic

/-! # Theorem 3.8(1): actual symmetric normalization versus pole kernel
The earlier bridge compared G^{-1} M with the pole matrix. This module
identifies the characteristic polynomial of the actual symmetric matrix
G^{-1/2} M G^{-1/2}, so eigenvalue multiplicities are preserved as well.
The separate monic orthogonal-polynomial construction and Laplace integral
derivative are not assumed or inferred. -/
noncomputable section
open Matrix
open scoped MatrixOrder
namespace LeanPaper.SymmetricPoleSpectrum
open ManuscriptChain ManuscriptChain.Spectral

lemma whitened_charpoly_eq_relative {n : ℕ} (p : SymmetricAffinePencil n)
    (hp : p.base.PosDef) :
    (OperatorNormDisk.whitened p).charpoly = (p.base⁻¹ * p.direction).charpoly := by
  let S := CFC.sqrt p.base
  have hs : S * S = p.base := by
    simpa [S, sq] using CFC.sq_sqrt p.base hp.posSemidef.nonneg
  have hi : S⁻¹ * S⁻¹ = p.base⁻¹ := by
    rw [← Matrix.mul_inv_rev, hs]
  change (S⁻¹ * p.direction * S⁻¹).charpoly = _
  rw [Matrix.charpoly_mul_comm (S⁻¹ * p.direction) S⁻¹,
    ← Matrix.mul_assoc, hi]

/-- Equality of characteristic polynomials for the exact manuscript B and
signed inverse-Gram pole kernel, with all hypotheses discharged by admissibility. -/
theorem actual_symmetric_charpoly_eq_pole (p : Real.Parameters) (hp : Real.Admissible p) :
    (OperatorNormDisk.whitened (Real.manuscriptPencil p)).charpoly =
      (PaperAdvances.Theorem3_8_Kernel.poleOperator
        (PaperAdvances.Theorem3_8_Actual.actualGram p)
        (PaperAdvances.Theorem3_8_Actual.actualV p)
        (PaperAdvances.Theorem3_8_Actual.actualGamma p)).charpoly := by
  rw [whitened_charpoly_eq_relative (Real.manuscriptPencil p) (GRAM_POSITIVE p hp)]
  exact PaperAdvances.Theorem3_8_Actual.actual_relative_charpoly_eq_pole p

/-- The real eigenvalue multisets, not merely their support sets, agree. -/
theorem actual_symmetric_roots_eq_pole (p : Real.Parameters) (hp : Real.Admissible p) :
    (OperatorNormDisk.whitened (Real.manuscriptPencil p)).charpoly.roots =
      (PaperAdvances.Theorem3_8_Kernel.poleOperator
        (PaperAdvances.Theorem3_8_Actual.actualGram p)
        (PaperAdvances.Theorem3_8_Actual.actualV p)
        (PaperAdvances.Theorem3_8_Actual.actualGamma p)).charpoly.roots :=
  congrArg Polynomial.roots (actual_symmetric_charpoly_eq_pole p hp)

end LeanPaper.SymmetricPoleSpectrum
#print axioms LeanPaper.SymmetricPoleSpectrum.actual_symmetric_charpoly_eq_pole
