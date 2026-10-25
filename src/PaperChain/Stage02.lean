import PaperChain.Stage01
import Theorem_2_5_Lagrange_Pole_Diagonalization

/-!
Stage 2: re-export the exact concrete derivative Vandermonde factorization
and basis determinant transformation from frozen Section 2 proofs.
The parity-sign count is not smuggled in as a new theorem.
-/

namespace PaperChain
open Polynomial

/-- Actual finite moment-pencil slope is Vandermonde-diagonal-conjugate. -/
theorem stage02_derivative_factorization
    (p : Zetahyperbolic.HankelParams) (k : ℕ) :
    Zetahyperbolic.M_deriv p k =
      Zetahyperbolic.V_pole p *
        Matrix.diagonal (Zetahyperbolic.gammaWeight p k) *
          (Zetahyperbolic.V_pole p).transpose :=
  Zetahyperbolic.M_deriv_factorization p k

/-- Nonzero derivative determinant, using actual negative-square-pole data. -/
theorem stage02_derivative_nonsingular
    (p : Zetahyperbolic.HankelParams) (k : ℕ) :
    (Zetahyperbolic.M_deriv p k).det ≠ 0 :=
  Zetahyperbolic.M_deriv_det_ne_zero p k

/-- The *other* manuscript-input realization also has exact full degree. -/
theorem stage02_raw_rational_pencil_exact_degree
    (p : ManuscriptChain.Real.Parameters) :
    (ManuscriptChain.Real.delta p).natDegree = p.h :=
  ManuscriptChain.PoleDiagonalization.delta_natDegree p

end PaperChain
