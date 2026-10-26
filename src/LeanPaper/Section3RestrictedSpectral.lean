import LeanPaper.SlopeSignature
import LeanPaper.PrincipalMinorRealRoots

/-!
# The pre-existing restricted alternative 3.3.alt

This assembles exactly the alternative already listed in the README: actual
Gram and all principal-minor positivity, the residue-product leading coefficient
and its sign, and intrinsic positive/negative signature. No arbitrary mixed-minor
positivity or Stieltjes determinacy is asserted. Those clauses of original 3.3
remain separate targets; this is not a redefinition of the printed theorem.
-/

noncomputable section
open scoped BigOperators MatrixOrder
open Matrix Polynomial SignType QuadraticForm

namespace LeanPaper.Section3RestrictedSpectral
open ManuscriptChain PoleDiagonalization

/-- Complete assembly of the approved restricted target, on the actual family,
with only the manuscript's structural admissibility conditions. -/
theorem theorem_3_3_alt (p : Real.Parameters) (hp : Real.Admissible p) :
    (Real.gram p (Real.zeta p.weight)).PosDef ∧
    (∀ (r : ℕ) (index : Fin r ↪ Fin p.h),
      0 < Real.evalQ (PrincipalMinors.determinant p index) (Real.zeta p.weight)) ∧
    (Real.delta p).leadingCoeff =
      (poleVandermonde p).det ^ 2 * (∏ a : Fin p.h, poleWeight p a) ∧
    sign (Real.delta p).leadingCoeff =
      (-1 : SignType) ^ (p.N * p.h + p.h * (p.h - 1) / 2) ∧
    sigPos (OperatorNormDisk.whitened (Real.manuscriptPencil p)).toQuadraticForm' =
      (if Even p.N then (p.h + 1) / 2 else p.h / 2) ∧
    sigNeg (OperatorNormDisk.whitened (Real.manuscriptPencil p)).toQuadraticForm' =
      (if Even p.N then p.h / 2 else (p.h + 1) / 2) := by
  refine ⟨GRAM_POSITIVE p hp,
    fun _ index => PrincipalMinors.determinant_center_pos p hp index, ?_,
    PoleWeightSigns.determinant_leading_sign p hp.m_pos, ?_⟩
  · rw [delta_leadingCoeff, rationalDerivativeMatrix_det]
  · exact SlopeSignature.actual_normalized_signature_counts p hp

end LeanPaper.Section3RestrictedSpectral

#print axioms LeanPaper.Section3RestrictedSpectral.theorem_3_3_alt
