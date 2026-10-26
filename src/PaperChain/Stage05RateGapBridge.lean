import PaperChain.Stage05PrimitiveBridge
import Theorem_4_1_Leading_Coefficient_Gap

/-!
# Stage 05: original primitive polynomial = leading height times Gram/derivative ratio

All conclusions are attached to the ORIGINAL rational-moment pencil through the
certified manuscript-compatibility map.  There is no free normalization constant.
The evaluation and leading-height lower bound are unconditional; eventual strict
rate separation is an EXPLICIT UNPROVED HYPOTHESIS.  No proof of irrationality
of zeta(5) is claimed without that rate separation.
-/

noncomputable section

namespace PaperChain

open ManuscriptChain

/-- Exact arithmetic/analytic balance for the ORIGINAL primitive determinant. -/
theorem stage05_original_primitive_gap_identity
    (p : Zetahyperbolic.HankelParams) (k : ℕ) :
    RealTransfer.evalReal (stage05_original_integer_primitive p k)
      (Real.zeta (2 * k + 1)) =
        LeadingCoefficientGap.leadingSize
          (Zetahyperbolic.ManuscriptCompatibility.toParameters p k) *
        LeadingCoefficientGap.determinantRatio
          (Zetahyperbolic.ManuscriptCompatibility.toParameters p k) := by
  simpa only [stage05_original_integer_primitive,
    Zetahyperbolic.ManuscriptCompatibility.toParameters,
    Real.Parameters.weight] using
    (LeadingCoefficientGap.primitivePolynomial_eval_eq
      (Zetahyperbolic.ManuscriptCompatibility.toParameters p k))

/-- No zero leading coefficient is possible after primitive normalization. -/
theorem stage05_original_leading_height_ge_one
    (p : Zetahyperbolic.HankelParams) (k : ℕ) :
    (1 : ℝ) ≤ LeadingCoefficientGap.leadingSize
      (Zetahyperbolic.ManuscriptCompatibility.toParameters p k) :=
  LeadingCoefficientGap.leadingSize_ge_one _

/-- Unconditional positivity of the *actual* determinant ratio. -/
theorem stage05_original_determinant_ratio_pos
    (p : Zetahyperbolic.HankelParams) (k : ℕ) (hk : 1 ≤ k) :
    0 < LeadingCoefficientGap.determinantRatio
      (Zetahyperbolic.ManuscriptCompatibility.toParameters p k) :=
  LeadingCoefficientGap.determinantRatio_pos _
    (Zetahyperbolic.ManuscriptCompatibility.toParameters_admissible p k hk)

/-- Explicit rate-gap endpoint for the concrete affine zeta(5) family.
The bounds `leading` and `ratio` are required, never manufactured. -/
theorem stage05_zeta5_irrational_if_leading_ratio_gap
    (A B : ℝ) (hAB : A < B) (n₀ : ℕ)
    (leading : ∀ n, n₀ ≤ n →
      LeadingCoefficientGap.leadingSize
        (GeneralIrrationality.affineFamily 2 n) ≤
          _root_.Real.exp (A * ((GeneralIrrationality.affineFamily 2 n).K : ℝ) ^ 2))
    (ratio : ∀ n, n₀ ≤ n →
      LeadingCoefficientGap.determinantRatio
        (GeneralIrrationality.affineFamily 2 n) ≤
          _root_.Real.exp (-B * ((GeneralIrrationality.affineFamily 2 n).K : ℝ) ^ 2)) :
    Irrational (Real.zeta 5) := by
  apply stage05_zeta5_irrational_if_normalized_quadratic_decay
  exact LeadingCoefficientGap.normalizedQuadraticDecay_of_gap
    (GeneralIrrationality.affineFamily 2) A B hAB n₀ leading ratio

end PaperChain
