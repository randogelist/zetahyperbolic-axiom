import PaperChain.Stage06

/-!
Stage 7: Coupled odd-zeta pencils. Algebra of the coefficient-aligned
Z = a * X + b * Y shift is checked separately from missing positive-weight
Loewner bounds and p-adic cancellation.
-/

namespace PaperChain

/-- Algebraic invariance of the aligned linear combination under a shift
in the zeta(3) direction, for actual real coefficients. -/
theorem stage07_coupled_shift (a b X Y d : ℝ) :
    (a * (X + d) + b * Y) - (a * X + b * Y) = a * d := by
  ring

/-- Exact pointwise Loewner-type scalar sandwich obligation in the paper's
positivity cone. It is not supplied automatically by linearity. -/
def WeightSandwich (base coupled : ℝ → ℝ) (c₁ c₂ : ℝ) : Prop :=
  0 < c₁ ∧ c₁ ≤ c₂ ∧ ∀ y, 0 < y →
    c₁ * base y ≤ coupled y ∧ coupled y ≤ c₂ * base y

/-- The paper's positivity-cone threshold for bζ(5)+aζ(3). -/
def Zeta3Zeta5PositivityCone (a b : ℝ) : Prop :=
  0 < b ∧ a < (Real.pi ^ 2 / 3) * b

end PaperChain
