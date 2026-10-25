import ProofAdvances.Corollary_3_6
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.Tactic

/-!
# Corrected Corollary 3.6 -- arbitrary finite atomic Hankel Gram

The signed reciprocal-root power sums of a real-rooted polynomial give
**finite** atomic moments. Their Hankel matrices are positive semidefinite
at every truncation size, but cannot be strictly positive definite above
the number of distinct atoms.

For h pairwise distinct atoms, the full h-by-h Hankel matrix is positive
definite and has determinant equal to the square of the Vandermonde
determinant. No analytic hypothesis is used.

The printed manuscript's assertion of strict positivity for every order
must therefore be corrected; we do not formalize that false assertion.
-/

noncomputable section
open Matrix
namespace PaperAdvances.Corollary3_6_FullGram

open PaperAdvances.Corollary3_6

/-- Positive semidefiniteness for every finite set of atoms, with no
    distinctness or size restrictions. -/
theorem finite_hankel_posSemidef {h : ℕ}
    (u : Fin h → ℝ) (n : ℕ) :
    (finiteHankel u n).PosSemidef := by
  rw [finite_hankel_gram]
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
    Matrix.posSemidef_self_mul_conjTranspose (finiteVandermonde u n)

/-- Row independence suffices for strict positivity, regardless of shape. -/
theorem finite_hankel_posDef_of_injective {h : ℕ}
    (u : Fin h → ℝ) (n : ℕ)
    (hv : Function.Injective (finiteVandermonde u n).vecMul) :
    (finiteHankel u n).PosDef := by
  rw [finite_hankel_gram]
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
    Matrix.PosDef.mul_conjTranspose_self (finiteVandermonde u n) hv

/-- For an equal-size Vandermonde, the determinant of the
    finite Hankel Gram is the Vandermonde determinant squared. -/
theorem finite_hankel_square_det {h : ℕ} (u : Fin h → ℝ) :
    (finiteHankel u h).det =
      (finiteVandermonde u h).det ^ 2 := by
  rw [finite_hankel_gram, Matrix.det_mul, Matrix.det_transpose]
  ring

/-- Pairwise distinct atoms make the square Vandermonde invertible. -/
theorem finite_vandermonde_det_ne_zero {h : ℕ} (u : Fin h → ℝ)
    (hu : Function.Injective u) :
    (finiteVandermonde u h).det ≠ 0 := by
  have heq : finiteVandermonde u h =
      (Matrix.vandermonde u).transpose := by
    ext i j
    rfl
  rw [heq, Matrix.det_transpose]
  exact Matrix.det_vandermonde_ne_zero_iff.mpr hu

/-- The full-order finite Hankel determinant is strictly positive for
    pairwise distinct real atoms. -/
theorem finite_hankel_full_det_pos {h : ℕ} (u : Fin h → ℝ)
    (hu : Function.Injective u) :
    0 < (finiteHankel u h).det := by
  rw [finite_hankel_square_det]
  exact sq_pos_of_ne_zero (finite_vandermonde_det_ne_zero u hu)

/-- Strict positive definiteness in the distinct-atom full-order case. -/
theorem finite_hankel_full_posDef {h : ℕ} (u : Fin h → ℝ)
    (hu : Function.Injective u) :
    (finiteHankel u h).PosDef := by
  -- Use the same explicit matrix-first iff application as the native
  -- compiler-PASS `Theorem_3_9_PositiveSlope.poleM_posDef` proof.
  have hVdet : IsUnit (finiteVandermonde u h).det :=
    isUnit_iff_ne_zero.mpr (finite_vandermonde_det_ne_zero u hu)
  have hVunit : IsUnit (finiteVandermonde u h) :=
    (Matrix.isUnit_iff_isUnit_det (finiteVandermonde u h)).2 hVdet
  have hVinj : Function.Injective (finiteVandermonde u h).vecMul :=
    Matrix.vecMul_injective_iff_isUnit.2 hVunit
  exact finite_hankel_posDef_of_injective u h hVinj

end PaperAdvances.Corollary3_6_FullGram

#print axioms PaperAdvances.Corollary3_6_FullGram.finite_hankel_posSemidef
#print axioms PaperAdvances.Corollary3_6_FullGram.finite_hankel_full_det_pos
#print axioms PaperAdvances.Corollary3_6_FullGram.finite_hankel_full_posDef
