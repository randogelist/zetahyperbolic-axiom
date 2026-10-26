import Definition_2_1_Order_s_Rational_Moment_Functional

/-!
# Definition 2.1 — Order-s rational moment functional
PDF: the exact numbered assertion from the supplied 52-page manuscript.
STATUS: FOUNDATION
REMAINING / EVIDENCE: Definition_2_1_Order_s_Rational_Moment_Functional.lean

Only the explicit `theorem` declarations below constitute kernel proof objects.
An imported `#check` is a pointer to a previously proved lemma or conditional
interface; it does NOT claim this entire printed result is formalized.
-/

noncomputable section
open scoped BigOperators
open Polynomial

namespace PaperChronology

/-- The paper's order-(2k+1) moment model uses the actual convergent zeta. -/
theorem zeta_identification (k : ℕ) (hk : 0 < k) :
    ManuscriptChain.Real.zeta (2 * k + 1) =
      (riemannZeta ((2 * k + 1 : ℕ) : ℂ)).re := by
  apply ManuscriptChain.Real.zeta_eq_riemannZeta_re
  omega

#check ManuscriptChain.Real.monomialMoment
#check ManuscriptChain.Real.poleConstant
#check ManuscriptChain.Real.pencil
#check ManuscriptChain.Real.delta

end PaperChronology
