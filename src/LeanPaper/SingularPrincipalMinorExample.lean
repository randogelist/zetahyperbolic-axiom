import PaperChain.Stage04PrincipalMinorCenter

/-!
# A constant leading minor of the actual manuscript pencil

Source candidate, native Windows Lean 4.33 compilation and axiom audit pending.
The parameters are k = 2, m = 1, N = 1, K = 6.  The five-term arithmetic
example was recorded in the pinned principal-theorems archive's
`PaperAudit/Theorem_3_4_Principal_Minor_Counterexample.lean`.  Here the terms
are computed from `ManuscriptChain.Real.residue` itself, and the conclusion
is tied to the actual leading determinant.  No residue equality or Gram
positivity is assumed as a new hypothesis.

This refutes the implicit full-degree/root-enumeration clause of printed
Theorem 3.4.  It does not refute the weaker claim that every existing root
of a principal determinant is real.
-/

noncomputable section
open scoped BigOperators
open Polynomial

namespace LeanPaper.SingularPrincipalMinorExample

open ManuscriptChain

def parameters : Real.Parameters := ⟨2, 1, 1, 6⟩

theorem parameters_admissible : Real.Admissible parameters := by
  constructor <;> norm_num [parameters]

/-- The five numbers are evaluated from the manuscript's original residue
formula, including the derivative of its actual denominator polynomial. -/
theorem weighted_residue_table :
    Real.residue parameters 0 0 2 * (2 : ℚ) ^ 4 = -1 / 840 ∧
    Real.residue parameters 0 0 3 * (3 : ℚ) ^ 4 = 3 / 70 ∧
    Real.residue parameters 0 0 4 * (4 : ℚ) ^ 4 = -16 / 63 ∧
    Real.residue parameters 0 0 5 * (5 : ℚ) ^ 4 = 625 / 1386 ∧
    Real.residue parameters 0 0 6 * (6 : ℚ) ^ 4 = -21 / 88 := by
  have hI : Finset.Icc 2 6 = ({2, 3, 4, 5, 6} : Finset ℕ) := by decide
  norm_num [Real.residue, Real.numerator, Real.D, Real.tailD,
    parameters, hI, Finset.prod_range_succ, Polynomial.derivative_mul]

/-- The actual upper-left entry of the slope matrix vanishes. -/
theorem first_slope_zero : Real.entryM parameters 0 0 = 0 := by
  have hI : Finset.Icc 2 6 = ({2, 3, 4, 5, 6} : Finset ℕ) := by decide
  rcases weighted_residue_table with ⟨h2, h3, h4, h5, h6⟩
  change (∑ a ∈ Finset.Icc 2 6,
    Real.residue parameters 0 0 a * (a : ℚ) ^ 4) = 0
  rw [hI]
  norm_num at h2 h3 h4 h5 h6 ⊢
  linarith

def firstIndex : Fin 1 ↪ Fin parameters.h :=
  PrincipalMinors.leadingIndex parameters 1 (by norm_num [parameters, Real.Parameters.h])

/-- The genuine leading principal determinant of order one is constant. -/
theorem first_minor_eq_constant :
    PrincipalMinors.determinant parameters firstIndex =
      C (Real.entryA parameters 0 0) := by
  unfold PrincipalMinors.determinant
  rw [Matrix.det_fin_one]
  change C (Real.entryA parameters 0 0) +
    C (Real.entryM parameters 0 0) * X = C (Real.entryA parameters 0 0)
  rw [first_slope_zero]
  simp

/-- The constant is strictly positive, by the original analytic Gram
construction already present in the active branch. -/
theorem first_constant_pos : 0 < (Real.entryA parameters 0 0 : ℝ) := by
  have hpos := PrincipalMinors.determinant_center_pos
    parameters parameters_admissible firstIndex
  rw [first_minor_eq_constant] at hpos
  simpa [Real.evalQ, Real.realPolynomial] using hpos

theorem first_minor_eval_pos (x : ℝ) :
    0 < Real.evalQ (PrincipalMinors.determinant parameters firstIndex) x := by
  rw [first_minor_eq_constant]
  simpa [Real.evalQ, Real.realPolynomial] using first_constant_pos

theorem first_minor_no_real_zero (x : ℝ) :
    Real.evalQ (PrincipalMinors.determinant parameters firstIndex) x ≠ 0 :=
  ne_of_gt (first_minor_eval_pos x)

theorem first_minor_natDegree_zero :
    (PrincipalMinors.determinant parameters firstIndex).natDegree = 0 := by
  rw [first_minor_eq_constant]
  simp

end LeanPaper.SingularPrincipalMinorExample

#print axioms LeanPaper.SingularPrincipalMinorExample.weighted_residue_table
#print axioms LeanPaper.SingularPrincipalMinorExample.first_slope_zero
#print axioms LeanPaper.SingularPrincipalMinorExample.first_minor_eq_constant
#print axioms LeanPaper.SingularPrincipalMinorExample.first_constant_pos
#print axioms LeanPaper.SingularPrincipalMinorExample.first_minor_no_real_zero
#print axioms LeanPaper.SingularPrincipalMinorExample.first_minor_natDegree_zero
