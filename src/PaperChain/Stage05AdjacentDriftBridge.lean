import Theorem_4_1_Adjacent_Log_Increment
import PaperChain.Stage05ContentGramBridge

/-!
# Stage 05 — actual zeta(5) adjacent-energy contraction frontier

The new premise is a strictly negative LINEAR-in-n incremental log rate,
not a previously unproved global K^2 rate. The finite first evaluation is
unrestricted. Telescoping gives a global quadratic rate and plugs into the
already native-passed conditional irrationality transfer.

No adjacent contraction estimate is presently established for the manuscript
pencil. Zeta(5) irrationality is still conditional.
-/

noncomputable section

namespace PaperChain

open ManuscriptChain

/-- Exact finite consecutive original primitive value/log ratio. -/
theorem stage05_affine_original_adjacent_log_ratio (k n : ℕ) (hk : 0 < k) :
    AdjacentLogIncrement.affineEnergy k (n + 1) -
      AdjacentLogIncrement.affineEnergy k n =
        _root_.Real.log
          (AdjacentLogIncrement.primitiveValue k (n + 1) /
            AdjacentLogIncrement.primitiveValue k n) :=
  AdjacentLogIncrement.affineEnergy_increment_eq_log_ratio k n hk

/-- CONDITIONAL: one certified uniform adjacent negative log drift suffices
for the original fixed zeta(5) irrationality endpoint. -/
theorem stage05_zeta5_irrational_if_adjacent_energy_drift
    (c : ℝ) (hc : 0 < c)
    (hstep : ∀ n : ℕ,
      AdjacentLogIncrement.affineEnergy 2 (n + 1) ≤
        AdjacentLogIncrement.affineEnergy 2 n -
          c * (2 * (n : ℝ) + 3)) :
    Irrational (Real.zeta 5) := by
  apply stage05_zeta5_irrational_if_normalized_quadratic_decay
  exact AdjacentLogIncrement.normalizedQuadraticDecay_of_adjacent_energy_drift
    2 (by norm_num) c hc hstep

/-- CONDITIONAL: two independent adjacent content / Gram bounds with
strictly negative combined rate imply the real zeta(5) endpoint. -/
theorem stage05_zeta5_irrational_if_adjacent_content_gram_rates
    (A B : ℝ) (hAB : A + B < 0)
    (hcontent : ∀ n : ℕ,
      ContentGramCancellation.contentLog (GeneralIrrationality.affineFamily 2 (n + 1)) -
        ContentGramCancellation.contentLog (GeneralIrrationality.affineFamily 2 n) ≤
          A * (2 * (n : ℝ) + 3))
    (hgram : ∀ n : ℕ,
      FiniteEnergy.gramLog (GeneralIrrationality.affineFamily 2 (n + 1)) -
        FiniteEnergy.gramLog (GeneralIrrationality.affineFamily 2 n) ≤
          B * (2 * (n : ℝ) + 3)) :
    Irrational (Real.zeta 5) := by
  apply stage05_zeta5_irrational_if_normalized_quadratic_decay
  exact AdjacentLogIncrement.normalizedQuadraticDecay_of_two_adjacent_log_rates
    2 (by norm_num) A B hAB hcontent hgram

/-- CONDITIONAL: finite ratio checks at each adjacent stage with uniform
exponential contraction are sufficient for the same manuscript polynomial. -/
theorem stage05_zeta5_irrational_if_adjacent_primitive_ratio
    (c : ℝ) (hc : 0 < c)
    (hratio : ∀ n : ℕ,
      AdjacentLogIncrement.primitiveValue 2 (n + 1) ≤
        _root_.Real.exp (-c * (2 * (n : ℝ) + 3)) *
          AdjacentLogIncrement.primitiveValue 2 n) :
    Irrational (Real.zeta 5) := by
  apply stage05_zeta5_irrational_if_normalized_quadratic_decay
  exact AdjacentLogIncrement.normalizedQuadraticDecay_of_adjacent_primitive_ratio
    2 (by norm_num) c hc hratio

end PaperChain
