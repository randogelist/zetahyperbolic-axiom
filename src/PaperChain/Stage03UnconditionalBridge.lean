import MAIN_CHAIN_ASSEMBLED
import PaperChain.Stage03

/-!
## Stage 03: unconditional original-pencil analytic bridge

This module uses the original manuscript-aligned analytic input archive,
including the proved hyperbolic simple-pole identity, not an assumed
`GramPositive` term. It closes the original-pencil positive-definite Gram
obligation and transfers the exact-root spectral theorem to the actual
`Delta_poly` determinant. It does not assert the additional strict total
positivity, root signature counts, quantitative spectral bounds, arithmetic
estimates, or any odd-zeta irrationality conclusion from the paper.

The archived dependency modules are copied byte-for-byte and are independently
recompiled on the recipient's native Lean 4.33.0 environment.
-/

noncomputable section

namespace PaperChain

/-- The actual original rational moment pencil is positive definite at the
true odd-zeta center, for every admissible original Hankel parameter. -/
theorem stage03_original_gram_unconditional
    (p : Zetahyperbolic.HankelParams) (k : ℕ) (hk : 1 ≤ k) :
    Zetahyperbolic.GramPositiveOriginal p k :=
  Zetahyperbolic.GRAM_POSITIVE_ORIGINAL p k hk

/-- Exact manuscript pencil: all complex zeros are real, have positive
distance from the actual center, and at least one root attains the radius.
The radius is asserted existentially, not estimated exponentially. -/
theorem stage03_original_exact_zero_free_disk
    (p : Zetahyperbolic.HankelParams) (k : ℕ) (hk : 1 ≤ k) :
    ∃ radius : ℝ, 0 < radius ∧
      (∀ z : ℂ, (Zetahyperbolic.Delta_poly p k).eval₂ (algebraMap ℚ ℂ) z = 0 →
        z.im = 0 ∧
        z ≠ (ManuscriptChain.Real.zeta (2 * k + 1) : ℂ) ∧
        radius ≤ ‖z - (ManuscriptChain.Real.zeta (2 * k + 1) : ℂ)‖) ∧
      (∃ z : ℂ, (Zetahyperbolic.Delta_poly p k).eval₂ (algebraMap ℚ ℂ) z = 0 ∧
        ‖z - (ManuscriptChain.Real.zeta (2 * k + 1) : ℂ)‖ = radius) :=
  Zetahyperbolic.ORIGINAL_EXACT_ZERO_FREE_DISK p k hk

/-- The actual Section 3 hyperbolicity theorem, including full degree,
nonsingular slope, true center and finite spectral factorization. -/
theorem stage03_unconditional_general_statement
    (p : Zetahyperbolic.HankelParams) (k : ℕ) (hk : 1 ≤ k) :
    ManuscriptChain.General.GeneralStatement
      (Zetahyperbolic.ManuscriptCompatibility.toParameters p k) :=
  Zetahyperbolic.MAIN_CHAIN_UNCONDITIONAL p k hk

end PaperChain
