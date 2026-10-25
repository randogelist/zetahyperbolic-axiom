import MAIN_CHAIN_ASSEMBLED
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
open scoped BigOperators
open Polynomial
namespace LeanPaper.JFractionActualObstruction
open ManuscriptChain

def parameters : Real.Parameters := ⟨1, 1, 1, 2⟩
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
  field_simp [ne_of_gt base_pos]

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
