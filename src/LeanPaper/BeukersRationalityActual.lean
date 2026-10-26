import LeanPaper.BeukersOffDiagonalActual

/-!
# Paper Theorem 5.1: rationality of the off-diagonal Beukers moments

The exact two-variable integral and its off-diagonal harmonic divided-difference
formula have already been proved in BeukersOffDiagonal. This module exposes the
corresponding *actual rational number*, not just a real-valued expression with
rational constants.

For r ≠ t, the integral is exactly the image of a rational under the
canonical ℚ → ℝ embedding. No claim about irrationality of ζ(7) follows.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace ManuscriptChain.Beukers

/-- The explicitly rational harmonic divided difference from Theorem 5.1. -/
def offdiagonalRational (r t : ℕ) : ℚ :=
  (Real.harmonic 6 r - Real.harmonic 6 t) / (6 * ((r : ℚ) - (t : ℚ)))

/-- The literal double integral equals the cast of its rational moment. -/
theorem offdiagonal_moment_eq_rat (r t : ℕ) (hrt : r ≠ t) :
    (∫ z, z.1 ^ r * z.2 ^ t * density z ∂squareMeasure) =
      (offdiagonalRational r t : ℝ) := by
  rw [offdiagonal_moment r t hrt]
  unfold offdiagonalRational
  push_cast
  rfl

/-- Theorem 5.1 explicitly certifies rationality of all off-diagonal moments. -/
theorem offdiagonal_moment_is_rational (r t : ℕ) (hrt : r ≠ t) :
    ∃ q : ℚ,
      (∫ z, z.1 ^ r * z.2 ^ t * density z ∂squareMeasure) = (q : ℝ) :=
  ⟨offdiagonalRational r t, offdiagonal_moment_eq_rat r t hrt⟩

end ManuscriptChain.Beukers
