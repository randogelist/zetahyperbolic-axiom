import Mathlib.Tactic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Theorem 3.7 — Cubic Newton inequalities

The previous module handled a quadratic special case.  Here we establish
both normalized Newton inequalities for arbitrary real cubic roots, by
explicit sums of squares.  This is a degree-three instance of the paper's
all-degree assertion; the latter remains an open Lean frontier.
-/

namespace LeanPaper.Section3Newton

/-- The first three elementary symmetric coefficients of three roots. -/
def cubicSym1 (a b c : ℝ) : ℝ := a + b + c
def cubicSym2 (a b c : ℝ) : ℝ := a*b + b*c + c*a
def cubicSym3 (a b c : ℝ) : ℝ := a*b*c

/-- Newton's first cubic defect is a nonnegative sum of squares. -/
theorem cubic_newton_first_sos (a b c : ℝ) :
    (cubicSym1 a b c)^2 - 3*cubicSym2 a b c =
      ((a-b)^2 + (b-c)^2 + (c-a)^2) / 2 := by
  unfold cubicSym1 cubicSym2
  ring

/-- Newton's second cubic defect is a nonnegative sum of squares. -/
theorem cubic_newton_second_sos (a b c : ℝ) :
    (cubicSym2 a b c)^2 - 3*cubicSym1 a b c * cubicSym3 a b c =
      ((a*b-b*c)^2 + (b*c-c*a)^2 + (c*a-a*b)^2) / 2 := by
  unfold cubicSym1 cubicSym2 cubicSym3
  ring

/-- First normalized cubic Newton inequality (valid regardless of root signs). -/
theorem cubic_newton_first (a b c : ℝ) :
    3*cubicSym2 a b c ≤ (cubicSym1 a b c)^2 := by
  have h : 0 ≤ (cubicSym1 a b c)^2 - 3*cubicSym2 a b c := by
    rw [cubic_newton_first_sos]
    positivity
  linarith

/-- Second normalized cubic Newton inequality. -/
theorem cubic_newton_second (a b c : ℝ) :
    3*cubicSym1 a b c * cubicSym3 a b c ≤ (cubicSym2 a b c)^2 := by
  have h : 0 ≤ (cubicSym2 a b c)^2 -
      3*cubicSym1 a b c*cubicSym3 a b c := by
    rw [cubic_newton_second_sos]
    positivity
  linarith

/-- The first Newton inequality is strict whenever two roots differ. -/
theorem cubic_newton_first_strict_of_ne (a b c : ℝ) (hab : a ≠ b) :
    3*cubicSym2 a b c < (cubicSym1 a b c)^2 := by
  have habpos : 0 < (a-b)^2 := sq_pos_of_ne_zero (sub_ne_zero.mpr hab)
  have hbc : 0 ≤ (b-c)^2 := sq_nonneg _
  have hca : 0 ≤ (c-a)^2 := sq_nonneg _
  have h := cubic_newton_first_sos a b c
  linarith

end LeanPaper.Section3Newton

#print axioms LeanPaper.Section3Newton.cubic_newton_first
#print axioms LeanPaper.Section3Newton.cubic_newton_second
