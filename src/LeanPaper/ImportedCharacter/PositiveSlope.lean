import LeanPaper.ImportedCharacter.CharacterPositive
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic

/-!
# Theorem 3.9 / 6.4 -- full-dimensional positivity of the pole slope

With distinct real poles and strictly positive diagonal residue weights,
the *entire* arbitrary-dimensional real-symmetric derivative matrix
V diag(gamma) V^T is positive definite. This is proved by positive
congruence and Vandermonde non-singularity, not by finite experiments.

In the character--Vandermonde beta branch, the character and interpolation
signs cancel (earlier module). Once the actual beta residue magnitudes
are identified with strictly positive values, this theorem supplies a
positive definite slope in every dimension.

No unproved integral identity or zeta5 witness is imported.
-/

noncomputable section
open Matrix
namespace PaperAdvances.Theorem3_9_PositiveSlope

open PaperAdvances.Theorem3_9_ShiftedPole

/-- A noncolliding weighted Vandermonde slope with positive weights is
    positive definite in **every finite dimension**. -/
theorem poleM_posDef {n : ℕ} (nodes gamma : Fin n → ℝ)
    (hn : Function.Injective nodes) (hgamma : ∀ a, 0 < gamma a) :
    (poleM nodes gamma).PosDef := by
  have hdiag : (Matrix.diagonal gamma).PosDef :=
    Matrix.posDef_diagonal_iff.mpr hgamma
  have hdet : IsUnit (poleV nodes).det :=
    isUnit_iff_ne_zero.mpr (poleV_det_ne_zero nodes hn)
  have hmatrix : IsUnit (poleV nodes) :=
    (Matrix.isUnit_iff_isUnit_det (poleV nodes)).2 hdet
  have hvec : Function.Injective (poleV nodes).vecMul :=
    Matrix.vecMul_injective_iff_isUnit.2 hmatrix
  have hc := hdiag.mul_mul_conjTranspose_same hvec
  unfold poleM
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hc

/-- Positive base residues remain positive under every real-exponent
    shifted-pole power scaling, not just odd integer exponents. -/
theorem shiftedGamma_pos {n : ℕ} (N : ℕ) (theta s : ℝ)
    (htheta : 0 < theta) (residue : Fin n → ℝ)
    (hres : ∀ a, 0 < residue a) (a : Fin n) :
    0 < shiftedGamma N theta s residue a := by
  unfold shiftedGamma
  exact mul_pos (hres a)
    (Real.rpow_pos_of_pos (shiftedPositiveNode_pos N theta htheta a) _)

/-- Universal shifted-pole positive derivative theorem. -/
theorem shiftedSlope_posDef {n : ℕ} (N : ℕ) (theta s : ℝ)
    (htheta : 0 < theta) (residue : Fin n → ℝ)
    (hres : ∀ a, 0 < residue a) :
    (poleM (shiftedSquareNode (n := n) N theta)
      (shiftedGamma N theta s residue)).PosDef := by
  apply poleM_posDef
  · exact shiftedSquareNode_injective N theta htheta
  · exact shiftedGamma_pos N theta s htheta residue hres

end PaperAdvances.Theorem3_9_PositiveSlope

#print axioms PaperAdvances.Theorem3_9_PositiveSlope.poleM_posDef
#print axioms PaperAdvances.Theorem3_9_PositiveSlope.shiftedSlope_posDef
