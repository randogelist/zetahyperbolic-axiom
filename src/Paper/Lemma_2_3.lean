import Paper.Lemma_2_2
import Zetahyperbolic.Section2Checked

/-!
# Lemma 2.3 — Reflection and difference identities for tau_X
PDF: the exact numbered assertion from the supplied 52-page manuscript.
STATUS: PROVED_GENERATORS
REMAINING / EVIDENCE: Monomial and simple-pole generator identities are kernel proved in Zetahyperbolic.Section2Checked; assemble the whole functional by Q-linearity.

Only the explicit `theorem` declarations below constitute kernel proof objects.
An imported `#check` is a pointer to a previously proved lemma or conditional
interface; it does NOT claim this entire printed result is formalized.
-/

noncomputable section
open scoped BigOperators
open Polynomial

namespace PaperChronology

/-- Reflection of pole labels is proved for every integer. -/
theorem poleLabel_reflection (r : ℤ) :
    Zetahyperbolic.dIndex (-1 - r) = Zetahyperbolic.dIndex r :=
  Zetahyperbolic.dIndex_reflect r

/-- The Bernoulli polynomial reflection, not merely the pole case. -/
theorem tau_reflection_monomial (k d : ℕ) (hk : 1 ≤ k) :
    (-1 : ℚ) ^ d *
      (∑ i ∈ Finset.range (d + 1),
        (Nat.choose d i : ℚ) * Zetahyperbolic.tauMonomial k i) =
      -Zetahyperbolic.tauMonomial k d :=
  Zetahyperbolic.tau_reflection_monomial k d hk

#check Zetahyperbolic.tau_reflection_pole
#check Zetahyperbolic.tau_difference_pole

end PaperChronology
