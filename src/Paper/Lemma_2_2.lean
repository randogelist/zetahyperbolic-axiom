import Paper.Definition_2_1
import Zetahyperbolic.Section2Checked

/-!
# Lemma 2.2 — Pullback identity
PDF: the exact numbered assertion from the supplied 52-page manuscript.
STATUS: PROVED_GENERATORS
REMAINING / EVIDENCE: Monomial and simple-pole generator identities are kernel proved in Zetahyperbolic.Section2Checked; assemble the whole functional by Q-linearity.

Only the explicit `theorem` declarations below constitute kernel proof objects.
This file imports the existing Section 2 proof objects without postulating
new mathematical facts.
-/

noncomputable section
open scoped BigOperators
open Polynomial

namespace PaperChronology

/-- The existing source closes the monomial case of formula (2.5). -/
theorem pullback_monomial (k e : ℕ) (hk : 1 ≤ k) :
    Zetahyperbolic.muMonomial k e =
      (-1 : ℚ) ^ e * Zetahyperbolic.tauMonomial k (2 * e + 2 * k + 1) :=
  Zetahyperbolic.pullback_identity_monomial k e hk

/-- The exact simple-pole generator identity from Lemma 2.2, reusing the
    existing kernel proof in `Zetahyperbolic.Section2Checked`. -/
theorem pullback_pole (k j : ℕ) (hk : 1 ≤ k) (hj : 1 ≤ j) :
    Zetahyperbolic.muPolePoly k j =
      Polynomial.C (-Zetahyperbolic.tauMonomial k (2 * k - 1)) -
        Polynomial.C ((j : ℚ) ^ (2 * k) / 2) *
          (Zetahyperbolic.tauPolePoly k (j : ℤ) +
            Zetahyperbolic.tauPolePoly k (-(j : ℤ))) :=
  Zetahyperbolic.pullback_identity_pole k j hk hj

/-- An elementary harmonic increment for later paper chapters. -/
theorem harmonic_succ (s n : ℕ) :
    ManuscriptChain.Real.harmonic s (n + 1) =
      ManuscriptChain.Real.harmonic s n +
        1 / (((n + 1 : ℕ) : ℚ) ^ s) := by
  simp [ManuscriptChain.Real.harmonic, Finset.sum_range_succ]

end PaperChronology
