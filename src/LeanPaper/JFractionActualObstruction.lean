import MAIN_CHAIN_ASSEMBLED
import LeanPaper.OperatorNormDisk
import Mathlib.Tactic

/-! # Corollary 3.5: a counterexample from the actual manuscript family
For k=m=N=1, K=2, the matrix has order one, slope -12, and a positive
Gram center. Its normalized scalar slope is therefore negative. At X=zeta(3)
the printed continued fraction has negative value 1/a1, whereas the actual
principal-minor ratio is positive. This is an actual admissible-family
counterexample, not merely an arbitrary symmetric-matrix diagnostic.

The corrected rank-one ratio is (1/G)/(1+(X-zeta(3))*a1).
-/
noncomputable section
open scoped BigOperators MatrixOrder
open Polynomial
namespace LeanPaper.JFractionActualObstruction
set_option backward.isDefEq.respectTransparency false
open ManuscriptChain

abbrev parameters : Real.Parameters := ⟨1, 1, 1, 2⟩
local instance : NeZero parameters.h := ⟨by norm_num [parameters, Real.Parameters.h]⟩
local instance : Unique (Fin parameters.h) := by
  change Unique (Fin 1)
  infer_instance
theorem admissible : Real.Admissible parameters := by
  constructor <;> norm_num [parameters]

def center : ℝ := Real.zeta parameters.weight
def base : ℝ := Real.gram parameters center 0 0
def slope : ℝ := Real.derivativeMatrix parameters 0 0
/-- The unique coefficient of the normalized scalar pencil I+tB. -/
def a1 : ℝ := slope / base

theorem slope_eq : slope = -12 := by
  have hI : Finset.Icc 2 2 = ({2} : Finset ℕ) := by decide
  norm_num [slope, Real.derivativeMatrix, Real.entryM, Real.residue,
    Real.numerator, Real.D, Real.tailD, parameters, hI, Finset.prod_range_succ,
    Polynomial.derivative_mul]

theorem base_pos : 0 < base := by
  have h := (GRAM_POSITIVE parameters admissible).det_pos
  rw [Matrix.det_fin_one] at h
  exact h

lemma actual_determinant (x : ℝ) :
    Real.evalQ (Real.delta parameters) x = base + (x-center)*slope := by
  rw [Real.delta_eval_eq_det_gram, Matrix.det_fin_one]
  have h := congrArg (fun M => M 0 0) (Real.manuscriptPencil_matrixAt parameters x)
  change base + (x-center)*slope = Real.gram parameters x 0 0 at h
  exact h.symm

lemma actual_determinant_center : Real.evalQ (Real.delta parameters) center = base := by
  rw [actual_determinant]
  ring

theorem normalized_pencil (x : ℝ) :
    Real.evalQ (Real.delta parameters) x = base * (1+(x-center)*a1) := by
  rw [actual_determinant, a1]
  field_simp [ne_of_gt base_pos] <;> ring

/-- In order one the normalized coefficient is literally the manuscript's
positive-square-root normalized matrix entry. -/
theorem a1_eq_whitened_entry :
    a1 = (OperatorNormDisk.whitened (Real.manuscriptPencil parameters)) 0 0 := by
  have hdefault : (default : Fin parameters.h) = 0 := Subsingleton.elim _ _
  let S : Matrix (Fin parameters.h) (Fin parameters.h) ℝ := CFC.sqrt (Real.gram parameters center)
  have hs : S*S = Real.gram parameters center := by
    simpa only [S, sq] using CFC.sq_sqrt (Real.gram parameters center)
      (GRAM_POSITIVE parameters admissible).posSemidef.nonneg
  have h00 : S 0 0 * S 0 0 = base := by
    have h := congrArg (fun M : Matrix (Fin 1) (Fin 1) ℝ => M 0 0) hs
    simpa only [Matrix.mul_apply, Finset.univ_unique, Finset.sum_singleton, hdefault, base] using h
  have hne : S 0 0 ≠ 0 := by
    intro hz
    rw [hz, zero_mul] at h00
    exact (ne_of_gt base_pos) h00.symm
  have hi : S⁻¹ 0 0 = (S 0 0)⁻¹ := by
    rw [Matrix.inv_subsingleton]
    simp only [Matrix.det_unique, Matrix.diagonal_apply_eq, Ring.inverse_eq_inv']
  change slope / base = (S⁻¹ * Real.derivativeMatrix parameters * S⁻¹) 0 0
  simp only [Matrix.mul_apply, Finset.univ_unique, Finset.sum_singleton, hdefault]
  rw [hi, ← h00]
  change slope / (S 0 0 * S 0 0) = (S 0 0)⁻¹ * slope * (S 0 0)⁻¹
  field_simp [hne] <;> ring

theorem normalized_slope_negative : a1 < 0 := by
  unfold a1
  rw [slope_eq]
  exact div_neg_of_neg_of_pos (by norm_num) base_pos

/-- The printed (3.6) is false at its stated fixed center even in order one. -/
theorem printed_fraction_fails_at_center :
    (1 / Real.evalQ (Real.delta parameters) center : ℝ) ≠
      1 / (a1 + (center-center)) := by
  rw [actual_determinant_center]
  have hl : 0 < (1 / base : ℝ) := one_div_pos.mpr base_pos
  have hr : (1 / (a1+(center-center)) : ℝ) < 0 := by
    simpa using one_div_neg.mpr normalized_slope_negative
  exact ne_of_gt (lt_trans hr hl)

/-- The correctly normalized ratio, with both missing factors restored. -/
theorem corrected_rank_one_fraction (x : ℝ) :
    (1 / Real.evalQ (Real.delta parameters) x : ℝ) =
      (1 / base) / (1+(x-center)*a1) := by
  rw [normalized_pencil, div_div]

end LeanPaper.JFractionActualObstruction
#print axioms LeanPaper.JFractionActualObstruction.printed_fraction_fails_at_center
#print axioms LeanPaper.JFractionActualObstruction.corrected_rank_one_fraction
