import Theorem_4_1_Content_Gram_Cancellation
import PaperChain.Stage08PoleProductBridge

/-!
# Original manuscript Section 4/8 — primitive-content/Gram transfer

The primitive integer polynomial is exactly the one obtained from the original
rational moment functional. The slope determinant cancels from its evaluation.
The final zeta(5) endpoint is CONDITIONAL on two explicitly stated uniform
K^2 log estimates and their negative sum. No numerical rate is asserted.
-/

noncomputable section

namespace PaperChain

open ManuscriptChain

/-- Original, unmodified manuscript Hankel geometry and analytic Gram. -/
theorem stage08_original_exact_content_gram_value
    (p : Zetahyperbolic.HankelParams) (k : ℕ) (hk : 1 ≤ k) :
    let P := Zetahyperbolic.ManuscriptCompatibility.toParameters p k
    FiniteEnergy.valueDecayLog P =
      -(ContentGramCancellation.contentLog P + FiniteEnergy.gramLog P) := by
  dsimp
  exact ContentGramCancellation.valueDecayLog_eq_neg_content_sub_gram _
    (Zetahyperbolic.ManuscriptCompatibility.toParameters_admissible p k hk)

/-- Exact finite-K cancellation: no independent slope-rate input is needed. -/
theorem stage08_original_content_gram_energy_identity
    (p : Zetahyperbolic.HankelParams) (k : ℕ) (hk : 1 ≤ k) :
    let P := Zetahyperbolic.ManuscriptCompatibility.toParameters p k
    ContentGramCancellation.contentLog P + FiniteEnergy.gramLog P =
      FiniteEnergy.leadingLog P - FiniteEnergy.determinantEnergy P := by
  dsimp
  exact ContentGramCancellation.content_add_gram_eq_height_sub_energy _
    (Zetahyperbolic.ManuscriptCompatibility.toParameters_admissible p k hk)

/-- CONDITIONAL endpoint on the ACTUAL k=2 affine family. The open inputs
are an upper log rate for rational primitive content and one for the positive
Bose-Einstein Gram, with sum < 0. -/
theorem stage05_zeta5_irrational_if_content_gram_log_rates
    (A B : ℝ) (hAB : A + B < 0) (n₀ : ℕ)
    (hcontent : ∀ n, n₀ ≤ n →
      ContentGramCancellation.contentLog (GeneralIrrationality.affineFamily 2 n) ≤
        A * ((GeneralIrrationality.affineFamily 2 n).K : ℝ) ^ 2)
    (hgram : ∀ n, n₀ ≤ n →
      FiniteEnergy.gramLog (GeneralIrrationality.affineFamily 2 n) ≤
        B * ((GeneralIrrationality.affineFamily 2 n).K : ℝ) ^ 2) :
    Irrational (Real.zeta 5) := by
  apply stage05_zeta5_irrational_if_normalized_quadratic_decay
  exact ContentGramCancellation.normalizedQuadraticDecay_of_content_gram_rates
    (GeneralIrrationality.affineFamily 2)
    (fun n => GeneralIrrationality.affineFamily_admissible
      2 (by norm_num) n)
    A B hAB n₀ hcontent hgram

end PaperChain
