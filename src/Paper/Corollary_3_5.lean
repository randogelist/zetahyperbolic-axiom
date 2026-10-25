import Paper.Theorem_3_4

/-!
# Corollary 3.5 — Stieltjes J-fraction from interlacing roots
PDF: the exact numbered assertion from the supplied 52-page manuscript.
STATUS: CORRECTION
REMAINING / EVIDENCE: As printed (3.6) misses Gram normalization and misuses the spectral parameter. Correct scalar resolvent lemma included.

Only the explicit `theorem` declarations below constitute kernel proof objects.
An imported `#check` is a pointer to a previously proved lemma or conditional
interface; it does NOT claim this entire printed result is formalized.
-/

noncomputable section
open scoped BigOperators
open Polynomial

namespace PaperChronology

/-- The missing Gram prefactor in printed (3.6) is already visible in size 1.
This is the corrected resolvent scaling, not an unproved full J-fraction. -/
theorem corrected_scalar_resolvent (g m delta : ℝ) (hg : g ≠ 0) :
    (g + delta * m)⁻¹ =
      g⁻¹ * (1 + delta * (g⁻¹ * m))⁻¹ := by
  have hfactor : g + delta * m = g * (1 + delta * (g⁻¹ * m)) := by
    field_simp [hg]
  rw [hfactor, mul_inv_rev]
  ring

end PaperChronology
