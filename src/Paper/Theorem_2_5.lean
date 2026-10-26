import Paper.Theorem_2_4
import Theorem_2_5_Lagrange_Pole_Diagonalization

/-!
# Theorem 2.5 — Lagrange pole diagonalization
PDF: the exact numbered assertion from the supplied 52-page manuscript.
STATUS: PROVED_CORE
REMAINING / EVIDENCE: Theorem_2_5_Lagrange_Pole_Diagonalization.lean

Only the explicit `theorem` declarations below constitute kernel proof objects.
An imported `#check` is a pointer to a previously proved lemma or conditional
interface; it does NOT claim this entire printed result is formalized.
-/

noncomputable section
open scoped BigOperators
open Polynomial

namespace PaperChronology

/-- The actual derivative determinant is nonsingular for the rational pencil. -/
theorem derivative_nonsingular (p : ManuscriptChain.Real.Parameters) :
    (ManuscriptChain.Real.derivativeMatrix p).det ≠ 0 :=
  ManuscriptChain.PoleDiagonalization.derivativeMatrix_det_ne_zero p

#check ManuscriptChain.PoleDiagonalization.theorem_2_5_lagrange_pole_diagonalization

end PaperChronology
