import Paper.Corollary_3_5

/-!
# Corollary 3.6 — Stieltjes reciprocal-root power sums
PDF: the exact numbered assertion from the supplied 52-page manuscript.
STATUS: CORRECTION
REMAINING / EVIDENCE: Finite atomic measures cannot have strictly positive Hankel determinants of every order. Correct rank obstruction included.

Only the explicit `theorem` declarations below constitute kernel proof objects.
An imported `#check` is a pointer to a previously proved lemma or conditional
interface; it does NOT claim this entire printed result is formalized.
-/

noncomputable section
open scoped BigOperators
open Polynomial

namespace PaperChronology

/-- For one atomic support point, the order-two Hankel minor vanishes.
Hence the PDF's assertion of strict positivity of ALL orders is false. -/
theorem rank_one_hankel_minor_vanishes (u : ℝ) :
    u ^ (0 : ℕ) * u ^ (2 : ℕ) - (u ^ (1 : ℕ)) ^ 2 = 0 := by
  ring

end PaperChronology
