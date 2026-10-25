import LeanPaper.ImportedSection56.KreinIdentity
import LeanPaper.ImportedSection56.DualMoments
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Principal Theorem 5.2(3): a concrete rational one-dimensional witness

For the ACTUAL rational two-variable Beukers pencil, take the polynomial
A(x) = 1-6x, i.e. the coefficient row (1,-6). We calculate its genuine
pencil determinant to be 37*X-38. Its real root is precisely 38/37.

Thus, if the elementary analytic zeta bound zeta(7)<38/37 is supplied,
then this is an explicit rational one-dimensional negative-Krein witness.
The scalar inequality and extensions to arbitrary h are not silently
assumed to have been formalized here.
-/

noncomputable section
open scoped BigOperators
open Polynomial
namespace PaperOrder.PrincipalTheorems
open ManuscriptChain.Real

/-- The coefficient row of the actual rational polynomial 1-6x. -/
def negativeWeightSevenRow : Fin 1 → Fin 2 → ℚ :=
  fun _ r => if r.val = 0 then 1 else -6

/-- The coefficient row of the constant polynomial 1. -/
def positiveWeightSevenRow : Fin 1 → Fin 2 → ℚ :=
  fun _ r => if r.val = 0 then 1 else 0

private theorem weightSeven_harmonic_zero : ManuscriptChain.Real.harmonic 7 0 = 0 := by
  simp [ManuscriptChain.Real.harmonic]

private theorem weightSeven_harmonic_one : ManuscriptChain.Real.harmonic 7 1 = 1 := by
  norm_num [ManuscriptChain.Real.harmonic, Finset.sum_range_succ]

private theorem weightSix_harmonic_zero : ManuscriptChain.Real.harmonic 6 0 = 0 := by
  simp [ManuscriptChain.Real.harmonic]

private theorem weightSix_harmonic_one : ManuscriptChain.Real.harmonic 6 1 = 1 := by
  norm_num [ManuscriptChain.Real.harmonic, Finset.sum_range_succ]

private theorem weightSeven_constant00 : dualConstant 7 0 0 = 0 := by
  norm_num [dualConstant, weightSeven_harmonic_zero]

private theorem weightSeven_constant11 : dualConstant 7 1 1 = -1 := by
  norm_num [dualConstant, weightSeven_harmonic_one]

private theorem weightSeven_constant01 : dualConstant 7 0 1 = 1 / 6 := by
  norm_num [dualConstant, weightSix_harmonic_zero, weightSix_harmonic_one]

private theorem weightSeven_constant10 : dualConstant 7 1 0 = 1 / 6 := by
  rw [PaperOrder.CoreAlgebra.dualConstant_swap]
  exact weightSeven_constant01

/-! ### Explicit scalar reduction of the genuine 1-by-1 dual moments -/

/-- The finite rational constant channel for A(x)=1-6x. -/
private theorem negativeWeightSeven_constant_scalar :
    (∑ r : Fin 2, ∑ t : Fin 2,
      negativeWeightSevenRow 0 r * negativeWeightSevenRow 0 t *
        dualConstant 7 r.val t.val) = (-38 : ℚ) := by
  norm_num [negativeWeightSevenRow, Fin.sum_univ_succ,
    Fin.sum_univ_zero, weightSeven_constant00, weightSeven_constant01,
    weightSeven_constant10, weightSeven_constant11] <;> ring

/-- The coefficient Gram slope for A(x)=1-6x is 1²+(-6)²=37. -/
private theorem negativeWeightSeven_slope_scalar :
    (∑ r : Fin 2,
      negativeWeightSevenRow 0 r * negativeWeightSevenRow 0 r) = (37 : ℚ) := by
  norm_num [negativeWeightSevenRow, Fin.sum_univ_succ,
    Fin.sum_univ_zero] <;> ring

/-- The constant channel for the coefficient row of A(x)=1. -/
private theorem positiveWeightSeven_constant_scalar :
    (∑ r : Fin 2, ∑ t : Fin 2,
      positiveWeightSevenRow 0 r * positiveWeightSevenRow 0 t *
        dualConstant 7 r.val t.val) = (0 : ℚ) := by
  norm_num [positiveWeightSevenRow, Fin.sum_univ_succ,
    Fin.sum_univ_zero, weightSeven_constant00, weightSeven_constant01,
    weightSeven_constant10, weightSeven_constant11] <;> ring

/-- The coefficient Gram slope for A(x)=1 is exactly one. -/
private theorem positiveWeightSeven_slope_scalar :
    (∑ r : Fin 2,
      positiveWeightSevenRow 0 r * positiveWeightSevenRow 0 r) = (1 : ℚ) := by
  norm_num [positiveWeightSevenRow, Fin.sum_univ_succ,
    Fin.sum_univ_zero] <;> ring

/-- Fully evaluated 1-by-1 rational Beukers pencil: 37X-38.
    The one-dimensional determinant is rewritten through an explicitly
    typed `Matrix.det_fin_one` rather than a binder-unfolding simp pass. -/
theorem negativeWeightSeven_actual_pencil :
    dualDelta 7 negativeWeightSevenRow =
      C (37 : ℚ) * X - C (38 : ℚ) := by
  classical
  calc
    dualDelta 7 negativeWeightSevenRow =
        dualEntry 7 negativeWeightSevenRow (0 : Fin 1) (0 : Fin 1) := by
      exact Matrix.det_fin_one
        (fun i j : Fin 1 => dualEntry 7 negativeWeightSevenRow i j)
    _ = C (37 : ℚ) * X - C (38 : ℚ) := by
      unfold dualEntry
      rw [negativeWeightSeven_constant_scalar, negativeWeightSeven_slope_scalar]
      norm_num <;> ring

/-- The paper's exact dual determinant has an explicitly rational root. -/
theorem negativeWeightSeven_rational_root :
    (dualDelta 7 negativeWeightSevenRow).eval (38 / 37 : ℚ) = 0 := by
  rw [negativeWeightSeven_actual_pencil]
  norm_num

/-- The real polynomial evaluation has the same affine formula. -/
theorem negativeWeightSeven_real_value (x : ℝ) :
    evalQ (dualDelta 7 negativeWeightSevenRow) x = 37 * x - 38 := by
  rw [negativeWeightSeven_actual_pencil]
  simp [evalQ, realPolynomial]

/-- The precise remaining scalar bound for an unconditional negative
one-dimensional Krein witness. -/
theorem negativeWeightSeven_below_zero_at_zeta
    (hzeta : zeta 7 < (38 / 37 : ℝ)) :
    evalQ (dualDelta 7 negativeWeightSevenRow) (zeta 7) < 0 := by
  rw [negativeWeightSeven_real_value]
  linarith

/-- The constant polynomial yields a positive one-dimensional family. -/
theorem positiveWeightSeven_actual_pencil :
    dualDelta 7 positiveWeightSevenRow = X := by
  classical
  calc
    dualDelta 7 positiveWeightSevenRow =
        dualEntry 7 positiveWeightSevenRow (0 : Fin 1) (0 : Fin 1) := by
      exact Matrix.det_fin_one
        (fun i j : Fin 1 => dualEntry 7 positiveWeightSevenRow i j)
    _ = X := by
      unfold dualEntry
      rw [positiveWeightSeven_constant_scalar, positiveWeightSeven_slope_scalar]
      simp

/-- The positive rational witness is unconditional at zeta(7). -/
theorem positiveWeightSeven_at_zeta :
    0 < evalQ (dualDelta 7 positiveWeightSevenRow) (zeta 7) := by
  rw [positiveWeightSeven_actual_pencil]
  simpa [evalQ, realPolynomial] using
    (zeta_pos (s := 7) (by norm_num))

end PaperOrder.PrincipalTheorems

#print axioms PaperOrder.PrincipalTheorems.negativeWeightSeven_actual_pencil
#print axioms PaperOrder.PrincipalTheorems.negativeWeightSeven_rational_root
#print axioms PaperOrder.PrincipalTheorems.negativeWeightSeven_below_zero_at_zeta
#print axioms PaperOrder.PrincipalTheorems.positiveWeightSeven_at_zeta
