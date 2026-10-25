import Theorem_2_5_Weight_Change
import Zetahyperbolic.ManuscriptCompatibility

/-!
# Stage 07: weight-shift transfer for the original simple-pole derivative

At FIXED m,N,K, increasing the odd-zeta weight from 2k+1 to 2(k+d)+1
multiplies the rational derivative determinant by the positive product
of even powers of the original pole indices.  These are exact finite
algebraic identities, not the open differential-shift Loewner sandwich.
-/

noncomputable section

namespace PaperChain

/-- Exact derivative determinant scaling for the original parameter map. -/
theorem stage07_original_derivative_det_reweight
    (p : Zetahyperbolic.HankelParams) (k step : ℕ) :
    (ManuscriptChain.PoleDiagonalization.rationalDerivativeMatrix
      (Zetahyperbolic.ManuscriptCompatibility.toParameters p (k + step))).det =
      (ManuscriptChain.PoleDiagonalization.rationalDerivativeMatrix
        (Zetahyperbolic.ManuscriptCompatibility.toParameters p k)).det *
        ∏ a : Fin p.h,
          (ManuscriptChain.PoleDiagonalization.poleIndex
            (Zetahyperbolic.ManuscriptCompatibility.toParameters p k) a : ℚ) ^
            (2 * step) := by
  -- `change` exposes the exact statement of the already compiled
  -- determinant-reweight theorem without rewriting the dependent Fin indices.
  -- This avoids the spurious simplifier/type mismatch at the original bridge.
  change
    (ManuscriptChain.PoleDiagonalization.rationalDerivativeMatrix
      (ManuscriptChain.PoleDiagonalization.reweight
        (Zetahyperbolic.ManuscriptCompatibility.toParameters p k) (k + step))).det =
      (ManuscriptChain.PoleDiagonalization.rationalDerivativeMatrix
        (ManuscriptChain.PoleDiagonalization.reweight
          (Zetahyperbolic.ManuscriptCompatibility.toParameters p k) k)).det *
        ∏ a : Fin (Zetahyperbolic.ManuscriptCompatibility.toParameters p k).h,
          (ManuscriptChain.PoleDiagonalization.poleIndex
            (Zetahyperbolic.ManuscriptCompatibility.toParameters p k) a : ℚ) ^
            (2 * step)
  exact ManuscriptChain.PoleDiagonalization.rationalDerivativeMatrix_det_reweight_add
    (Zetahyperbolic.ManuscriptCompatibility.toParameters p k) k step

/-- The determinant scaling factor is strictly positive, even at step zero. -/
theorem stage07_original_reweight_factor_pos
    (p : Zetahyperbolic.HankelParams) (k step : ℕ) :
    (0 : ℚ) < ∏ a : Fin p.h,
      (ManuscriptChain.PoleDiagonalization.poleIndex
        (Zetahyperbolic.ManuscriptCompatibility.toParameters p k) a : ℚ) ^
        (2 * step) := by
  exact ManuscriptChain.PoleDiagonalization.reweight_factor_pos
    (Zetahyperbolic.ManuscriptCompatibility.toParameters p k) step

end PaperChain
