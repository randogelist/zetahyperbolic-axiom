import ProofAdvances.Corollary_3_6_FullGram
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Tactic

/-!
# Corollary 3.6: exact finite Stieltjes hierarchy after necessary correction

The printed assertion of strictly positive Hankel determinants at *all* orders
for finitely many atomic roots is false. This module proves the valid strong
replacement: arbitrary real atoms with nonnegative masses have positive
semidefinite Hankel matrices of *every* order. If the masses are positive and
the atoms are pairwise distinct, the full atomic-order determinant and matrix
are strictly positive. Every larger square Hankel determinant is exactly zero.

This result is unconditional and contains no arithmetic Witness.
-/

noncomputable section
open scoped BigOperators
open Matrix

namespace PaperAdvances.Corollary3_6_WeightedCorrected

open PaperAdvances.Corollary3_6
open PaperAdvances.Corollary3_6_FullGram

/-- The order-n moment Hankel matrix for a finite real atomic measure with
masses `w`; no distinctness or sign assumptions are built into the definition. -/
def weightedHankel {h : ℕ} (u w : Fin h → ℝ) (n : ℕ) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun i j => ∑ k : Fin h, w k * u k ^ (i.val + j.val)

/-- An exact finite weighted Vandermonde Gram factorization. -/
theorem weighted_hankel_gram {h : ℕ} (u w : Fin h → ℝ) (n : ℕ) :
    weightedHankel u w n =
      finiteVandermonde u n * Matrix.diagonal w *
        (finiteVandermonde u n)ᵀ := by
  classical
  ext i j
  unfold weightedHankel
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply, finiteVandermonde]
  apply Finset.sum_congr rfl
  intro k hk
  rw [pow_add]
  ring

/-- Every truncation of any finite nonnegative atomic moment measure
is positive semidefinite, including truncation orders larger than the
number of atoms. -/
theorem weighted_hankel_posSemidef {h : ℕ} (u w : Fin h → ℝ) (n : ℕ)
    (hw : ∀ k, 0 ≤ w k) :
    (weightedHankel u w n).PosSemidef := by
  rw [weighted_hankel_gram]
  have hd : (Matrix.diagonal w : Matrix (Fin h) (Fin h) ℝ).PosSemidef :=
    Matrix.posSemidef_diagonal_iff.mpr hw
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
    hd.mul_mul_conjTranspose_same (finiteVandermonde u n)

/-- At exactly the number of atoms, all strictly positive masses and
pairwise distinct atoms make the weighted Hankel matrix positive definite. -/
theorem weighted_hankel_full_posDef {h : ℕ} (u w : Fin h → ℝ)
    (hu : Function.Injective u) (hw : ∀ k, 0 < w k) :
    (weightedHankel u w h).PosDef := by
  rw [weighted_hankel_gram]
  have hd : (Matrix.diagonal w : Matrix (Fin h) (Fin h) ℝ).PosDef :=
    Matrix.posDef_diagonal_iff.mpr hw
  have hVunit : IsUnit (finiteVandermonde u h) :=
    (Matrix.isUnit_iff_isUnit_det (finiteVandermonde u h)).2
      (isUnit_iff_ne_zero.mpr (finite_vandermonde_det_ne_zero u hu))
  have hVinj : Function.Injective (finiteVandermonde u h).vecMul :=
    Matrix.vecMul_injective_iff_isUnit.2 hVunit
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
    hd.mul_mul_conjTranspose_same (B := finiteVandermonde u h) hVinj

/-- Exact *rank obstruction*: once the Hankel order exceeds the number
of atoms, its determinant is zero, even without any assumption on masses.
This repairs the overstrong strict-Hankel claim in the PDF. -/
theorem weighted_hankel_det_zero_above_support {h : ℕ} (u w : Fin h → ℝ)
    (n : ℕ) (hn : h < n) : (weightedHankel u w n).det = 0 := by
  classical
  by_contra hne
  have hmat : IsUnit (weightedHankel u w n) :=
    (Matrix.isUnit_iff_isUnit_det (weightedHankel u w n)).2
      (isUnit_iff_ne_zero.mpr hne)
  have hfull : (weightedHankel u w n).rank = n := by
    simpa using Matrix.rank_of_isUnit (weightedHankel u w n) hmat
  have hbound : (weightedHankel u w n).rank ≤ h := by
    rw [weighted_hankel_gram]
    exact ((Matrix.rank_mul_le_left _ _).trans
      (Matrix.rank_mul_le_left _ _)).trans
        (Matrix.rank_le_width (finiteVandermonde u n))
  omega

/-- Unweighted special case: every Hankel determinant of order exceeding
its finite atomic support is exactly zero. -/
theorem finite_hankel_det_zero_above_support {h : ℕ} (u : Fin h → ℝ)
    (n : ℕ) (hn : h < n) : (finiteHankel u n).det = 0 := by
  have hsame : weightedHankel u (fun _ => 1) n = finiteHankel u n := by
    ext i j
    simp [weightedHankel, finiteHankel]
  rw [← hsame]
  exact weighted_hankel_det_zero_above_support u (fun _ => 1) n hn

end PaperAdvances.Corollary3_6_WeightedCorrected

#print axioms PaperAdvances.Corollary3_6_WeightedCorrected.weighted_hankel_gram
#print axioms PaperAdvances.Corollary3_6_WeightedCorrected.weighted_hankel_posSemidef
#print axioms PaperAdvances.Corollary3_6_WeightedCorrected.weighted_hankel_full_posDef
#print axioms PaperAdvances.Corollary3_6_WeightedCorrected.weighted_hankel_det_zero_above_support
