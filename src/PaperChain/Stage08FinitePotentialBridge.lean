import Theorem_4_1_Determinant_Log_Energy
import PaperChain.Stage05RateGapBridge

/-!
# Stage 08 + 05: conservation law on original manuscript parameters

The previous stages certified the original functional and its positive Gram
matrix. This file therefore uses the actual manuscript pencil and primitive
integer polynomial. All statements are FINITE-K identities or transfers
conditional on real uniform determinant/height estimates.

It does not assume, assert, or prove the paper's claimed K^2 determinant
limits, eigenvalue clustering, strict asymptotic rate gap or zeta(5)
irrationality.
-/

noncomputable section

namespace PaperChain

open ManuscriptChain

/-- Exact conservation on the original manuscript's actual finite pencil. -/
theorem stage08_original_finite_potential_conservation
    (p : Zetahyperbolic.HankelParams) (k : ℕ) (hk : 1 ≤ k) :
    FiniteEnergy.leadingLog
        (Zetahyperbolic.ManuscriptCompatibility.toParameters p k) +
      FiniteEnergy.valueDecayLog
        (Zetahyperbolic.ManuscriptCompatibility.toParameters p k) =
      FiniteEnergy.determinantEnergy
        (Zetahyperbolic.ManuscriptCompatibility.toParameters p k) :=
  FiniteEnergy.finite_potential_conservation _
    (Zetahyperbolic.ManuscriptCompatibility.toParameters_admissible p k hk)

/-- Stronger than a mere formal asymptotic equality: the K²-normalized
  conservation identity holds for each admissible finite K individually. -/
theorem stage08_original_finite_potential_conservation_per_K_sq
    (p : Zetahyperbolic.HankelParams) (k : ℕ) (hk : 1 ≤ k) :
    let P := Zetahyperbolic.ManuscriptCompatibility.toParameters p k
    FiniteEnergy.leadingLog P / ((P.K : ℝ) ^ 2) +
      FiniteEnergy.valueDecayLog P / ((P.K : ℝ) ^ 2) =
      FiniteEnergy.determinantEnergy P / ((P.K : ℝ) ^ 2) := by
  dsimp
  exact FiniteEnergy.finite_potential_conservation_per_K_sq _
    (Zetahyperbolic.ManuscriptCompatibility.toParameters_admissible p k hk)

/-- Exact equivalence for the concrete K = 30(n+1), N = 3(n+1) family:
  zeta(5) irrationality follows if the FINITE energy/primitive height gap
  is eventually positive at a quadratic rate. The inequality is not proved. -/
theorem stage05_zeta5_irrational_if_finite_energy_gap
    (c : ℝ) (hc : 0 < c) (n₀ : ℕ)
    (hgap : ∀ n, n₀ ≤ n →
      FiniteEnergy.leadingLog (GeneralIrrationality.affineFamily 2 n) -
        FiniteEnergy.determinantEnergy (GeneralIrrationality.affineFamily 2 n) ≤
          -c * ((GeneralIrrationality.affineFamily 2 n).K : ℝ) ^ 2) :
    Irrational (Real.zeta 5) := by
  apply stage05_zeta5_irrational_if_normalized_quadratic_decay
  apply (FiniteEnergy.normalizedQuadraticDecay_iff_energy_gap
    (GeneralIrrationality.affineFamily 2)
    (fun n => GeneralIrrationality.affineFamily_admissible
      2 (by norm_num) n)).2
  exact ⟨c, hc, n₀, hgap⟩

/-- An independent three-input variant displaying exactly which estimates
  must come from the paper's Section 4/8: primitive height, Gram det, slope
  determinant. Nothing is filled with an arbitrary proxy. -/
theorem stage05_zeta5_irrational_if_three_log_rates
    (A B C : ℝ) (hABC : A + B < C) (n₀ : ℕ)
    (hleading : ∀ n, n₀ ≤ n →
      FiniteEnergy.leadingLog (GeneralIrrationality.affineFamily 2 n) ≤
        A * ((GeneralIrrationality.affineFamily 2 n).K : ℝ) ^ 2)
    (hgram : ∀ n, n₀ ≤ n →
      FiniteEnergy.gramLog (GeneralIrrationality.affineFamily 2 n) ≤
        B * ((GeneralIrrationality.affineFamily 2 n).K : ℝ) ^ 2)
    (hderivative : ∀ n, n₀ ≤ n →
      C * ((GeneralIrrationality.affineFamily 2 n).K : ℝ) ^ 2 ≤
        FiniteEnergy.derivativeLog (GeneralIrrationality.affineFamily 2 n)) :
    Irrational (Real.zeta 5) := by
  apply stage05_zeta5_irrational_if_normalized_quadratic_decay
  exact FiniteEnergy.normalizedQuadraticDecay_of_three_log_rates
    (GeneralIrrationality.affineFamily 2)
    (fun n => GeneralIrrationality.affineFamily_admissible
      2 (by norm_num) n)
    A B C hABC n₀ hleading hgram hderivative

end PaperChain
