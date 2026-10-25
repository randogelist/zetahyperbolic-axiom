import MAIN_CHAIN_IRRATIONALITY
import MAIN_CHAIN_ARITHMETIC
import PaperChain.Stage03UnconditionalBridge

/-!
# Stage 05: actual primitive integer determinant and odd-zeta transfer

This bridge connects the native-proved unconditional original Gram theorem
(Stage 03) to the actual primitive INTEGER polynomial attached to the
original pencil. Its value at the genuine odd-zeta center is strictly positive
at every admissible finite K, and its exact degree is K-N.

The odd-zeta irrationality statements below remain **conditional** on
QUADRATIC DECAY OF THE PRIMITIVE INTEGER POLYNOMIAL**. The analytic Stage 03
proof establishes NONVANISHING, not that decay. This package does NOT prove
irrationality of zeta(5), the printed 11.407 spectral exponent, a quantitative
irrationality measure, or the exact principal-minor rank law.
-/

noncomputable section
open Polynomial

namespace PaperChain

/-- The primitive integer polynomial of the genuinely original determinant,
transported through the already-proved rational pencil compatibility map. -/
def stage05_original_integer_primitive
    (p : Zetahyperbolic.HankelParams) (k : ℕ) : ℤ[X] :=
  ManuscriptChain.GeneralIrrationality.primitivePolynomial
    (Zetahyperbolic.ManuscriptCompatibility.toParameters p k)

/-- Unconditional exact degree of the original normalized integer determinant. -/
theorem stage05_original_integer_primitive_degree
    (p : Zetahyperbolic.HankelParams) (k : ℕ) :
    (stage05_original_integer_primitive p k).natDegree = p.h := by
  simpa only [stage05_original_integer_primitive,
    Zetahyperbolic.ManuscriptCompatibility.toParameters_h] using
    (ManuscriptChain.GeneralIrrationality.primitivePolynomial_natDegree
      (Zetahyperbolic.ManuscriptCompatibility.toParameters p k))

/-- Unconditional strict positivity of the actual primitive integer polynomial
at the real odd zeta. No hypothesis on algebraic irrationality or decay. -/
theorem stage05_original_integer_primitive_center_pos
    (p : Zetahyperbolic.HankelParams) (k : ℕ) (hk : 1 ≤ k) :
    0 < ManuscriptChain.RealTransfer.evalReal
      (stage05_original_integer_primitive p k)
      (ManuscriptChain.Real.zeta (2 * k + 1)) := by
  simpa only [stage05_original_integer_primitive,
    Zetahyperbolic.ManuscriptCompatibility.toParameters,
    ManuscriptChain.Real.Parameters.weight] using
    (ManuscriptChain.GeneralIrrationality.primitivePolynomial_eval_pos
      (Zetahyperbolic.ManuscriptCompatibility.toParameters p k)
      (Zetahyperbolic.ManuscriptCompatibility.toParameters_admissible p k hk))

/-- All fixed odd zeta values follow from the single remaining normalized
quadratic-decay family hypothesis. Nothing asserts that hypothesis. -/
theorem stage05_fixed_odd_zeta_irrational_if_affine_decay
    (k : ℕ) (hk : 0 < k)
    (hdecay : ManuscriptChain.GeneralIrrationality.AffineFamilyDecay k) :
    Irrational (ManuscriptChain.Real.zeta (2 * k + 1)) :=
  ManuscriptChain.GeneralIrrationality.irrational_odd_zeta k
    (ManuscriptChain.GeneralIrrationality.oddWeightDecayHypothesis_of_affineFamilyDecay
      k hk hdecay)

/-- A clearly conditional statement about the actual zeta(5) series. -/
theorem stage05_zeta5_irrational_if_normalized_quadratic_decay
    (hdecay : ManuscriptChain.GeneralIrrationality.AffineFamilyDecay 2) :
    Irrational (ManuscriptChain.Real.zeta 5) := by
  simpa using stage05_fixed_odd_zeta_irrational_if_affine_decay
    2 (by norm_num) hdecay

/-- Concrete proportional odd-weight families have the same one-premise
primitive-decay endpoint after analytic positivity is discharged. -/
theorem stage05_linear_family_irrational_if_decay
    (k m a b : ℕ) (hk : 0 < k) (hm : 0 < m)
    (ha : 0 < a) (hab : a < b)
    (hdecay : ManuscriptChain.GeneralArithmetic.EventualQuadraticDecay
      (ManuscriptChain.GeneralArithmetic.linearFamily k m a b hk hm ha hab)) :
    Irrational (ManuscriptChain.Real.zeta (2 * k + 1)) :=
  ManuscriptChain.LINEAR_FAMILY_IRRATIONALITY
    k m a b hk hm ha hab hdecay

end PaperChain
