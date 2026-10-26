import Theorem_4_1_Pole_Log_Slope
import PaperChain.Stage08FinitePotentialBridge

/-!
# Original manuscript Stage 08: exact finite pole logarithmic conservation

No replacement functional or surrogate moment matrix. The parameter map is
that of the original manuscript. Any consequence for zeta(5) uses explicit
positive quadratic rate inequalities on genuine primitive/Gram/pole products.
-/

noncomputable section

namespace PaperChain

open ManuscriptChain

/-- The original pencil has the exact finite pole-energy decomposition.
This is unconditional for each admissible finite geometry/weight. -/
theorem stage08_original_finite_pole_energy
    (p : Zetahyperbolic.HankelParams) (k : ℕ) (hk : 1 ≤ k) :
    let P := Zetahyperbolic.ManuscriptCompatibility.toParameters p k
    FiniteEnergy.leadingLog P + FiniteEnergy.valueDecayLog P =
      (2 * _root_.Real.log (PoleLogSlope.vandermondeSize P) +
        _root_.Real.log (PoleLogSlope.poleProductSize P)) -
          FiniteEnergy.gramLog P := by
  dsimp
  exact PoleLogSlope.finite_energy_pole_product _
    (Zetahyperbolic.ManuscriptCompatibility.toParameters_admissible p k hk)

/-- CONDITIONAL zeta(5) endpoint whose slope input consists of actual
finite Vandermonde and residue-weight products. The four log-rate bounds
and their strict separation are the unresolved asymptotic frontier. -/
theorem stage05_zeta5_irrational_if_pole_log_rates
    (A B C D : ℝ) (hgap : A + B < 2 * C + D) (n₀ : ℕ)
    (hleading : ∀ n, n₀ ≤ n →
      FiniteEnergy.leadingLog (GeneralIrrationality.affineFamily 2 n) ≤
        A * ((GeneralIrrationality.affineFamily 2 n).K : ℝ) ^ 2)
    (hgram : ∀ n, n₀ ≤ n →
      FiniteEnergy.gramLog (GeneralIrrationality.affineFamily 2 n) ≤
        B * ((GeneralIrrationality.affineFamily 2 n).K : ℝ) ^ 2)
    (hvandermonde : ∀ n, n₀ ≤ n →
      C * ((GeneralIrrationality.affineFamily 2 n).K : ℝ) ^ 2 ≤
        _root_.Real.log (PoleLogSlope.vandermondeSize
          (GeneralIrrationality.affineFamily 2 n)))
    (hpoles : ∀ n, n₀ ≤ n →
      D * ((GeneralIrrationality.affineFamily 2 n).K : ℝ) ^ 2 ≤
        _root_.Real.log (PoleLogSlope.poleProductSize
          (GeneralIrrationality.affineFamily 2 n))) :
    Irrational (Real.zeta 5) := by
  apply stage05_zeta5_irrational_if_normalized_quadratic_decay
  exact PoleLogSlope.normalizedQuadraticDecay_of_pole_log_rates
    (GeneralIrrationality.affineFamily 2)
    (fun n => GeneralIrrationality.affineFamily_admissible 2 (by norm_num) n)
    A B C D hgap n₀ hleading hgram hvandermonde hpoles

end PaperChain
