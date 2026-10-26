import LeanPaper.ImportedSection56.CoefficientGram
import LeanPaper.ImportedSection56.KreinIdentity

/-!
# Principal Theorem 5.2(3): rigorous finite-channel Krein cones

For ANY finite real plus/minus coefficient family, a signed Gram form
is strictly positive (respectively negative) when ALL negative
(respectively positive) channels vanish and the surviving channels
separate nonzero coefficient vectors.

This is not the paper's infinite-dimensional polynomial cone claim.
The infinite-tail annihilation / quantitative bound remains open.
-/

noncomputable section
open scoped BigOperators
namespace PaperOrder.PrincipalTheorems

/-- A finite signed Gram matrix for actual plus and minus channels. -/
def finiteKreinGram {h K : ℕ}
    (plus minus : Fin h → Fin (K + 1) → ℝ) :
    Matrix (Fin h) (Fin h) ℝ :=
  coefficientSlope plus - coefficientSlope minus

/-- Vanishing of all negative channels removes the negative Gram matrix. -/
theorem finiteKreinGram_positive_reduction {h K : ℕ}
    (plus minus : Fin h → Fin (K + 1) → ℝ)
    (hminus : ∀ i r, minus i r = 0) :
    finiteKreinGram plus minus = coefficientSlope plus := by
  have hz : coefficientSlope minus = 0 := by
    ext i j
    simp [coefficientSlope, hminus]
  simp [finiteKreinGram, hz]

/-- The finite strict positive cone needs no separate definiteness axiom. -/
theorem finiteKreinGram_posDef {h K : ℕ}
    (plus minus : Fin h → Fin (K + 1) → ℝ)
    (hminus : ∀ i r, minus i r = 0)
    (hplus : coefficientRowsSeparate plus) :
    (finiteKreinGram plus minus).PosDef := by
  rw [finiteKreinGram_positive_reduction plus minus hminus]
  exact coefficientSlope_posDef plus hplus

/-- Vanishing positive channels leaves the negative of a positive Gram. -/
theorem finiteKreinGram_negative_reduction {h K : ℕ}
    (plus minus : Fin h → Fin (K + 1) → ℝ)
    (hplus : ∀ i r, plus i r = 0) :
    finiteKreinGram plus minus = -(coefficientSlope minus) := by
  have hz : coefficientSlope plus = 0 := by
    ext i j
    simp [coefficientSlope, hplus]
  simp [finiteKreinGram, hz]

/-- Strict negativity: equivalently, the opposite matrix is positive. -/
theorem finiteKreinGram_neg_posDef {h K : ℕ}
    (plus minus : Fin h → Fin (K + 1) → ℝ)
    (hplus : ∀ i r, plus i r = 0)
    (hminus : coefficientRowsSeparate minus) :
    (-finiteKreinGram plus minus).PosDef := by
  rw [finiteKreinGram_negative_reduction plus minus hplus]
  simpa using coefficientSlope_posDef minus hminus

end PaperOrder.PrincipalTheorems

#print axioms PaperOrder.PrincipalTheorems.finiteKreinGram_posDef
#print axioms PaperOrder.PrincipalTheorems.finiteKreinGram_neg_posDef
