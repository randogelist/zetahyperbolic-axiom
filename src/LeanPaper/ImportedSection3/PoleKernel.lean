import LeanPaper.ImportedSection3.CubicTuran
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic

/-!
# Theorem 3.8(1) — finite Christoffel–Darboux pole-kernel spectral identity

For arbitrary real square matrices G,V and a diagonal weight matrix D,
  charpoly(G^-1 * (V*D*V^T)) = charpoly(D * (V^T*G^-1*V)).

This equality is proved for every dimension, not merely for a 2x2 or 3x3
truncation. It uses the AB/BA characteristic-polynomial identity. The analogous
trace identity is the finite-dimensional algebra behind the Jacobi derivative
formula. These statements do not assume that G is invertible or positive;
those conditions matter only for identifying G as the paper's Gram matrix.

The integral representation of G, orthogonal-polynomial basis, and
parameter differentiation under the integral remain separate analytic tasks.
-/

noncomputable section
open scoped BigOperators
open Matrix

namespace PaperAdvances.Theorem3_8_Kernel

/-- The pole-kernel matrix of the negative-lattice evaluation vectors. -/
def kernelMatrix {n : ℕ} (G V : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  V.transpose * G⁻¹ * V

/-- General spectral operator in the pole (Christoffel–Darboux) basis. -/
def poleOperator {n : ℕ} (G V : Matrix (Fin n) (Fin n) ℝ)
    (γ : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.diagonal γ * kernelMatrix G V

/-- Entire characteristic polynomial, with multiplicities, agrees in all dimensions. -/
theorem charpoly_relative_eq_pole {n : ℕ}
    (G V : Matrix (Fin n) (Fin n) ℝ) (γ : Fin n → ℝ) :
    (G⁻¹ * (V * Matrix.diagonal γ * V.transpose)).charpoly =
      (poleOperator G V γ).charpoly := by
  simpa only [poleOperator, kernelMatrix, Matrix.mul_assoc] using
    (Matrix.charpoly_mul_comm (G⁻¹ * V) (Matrix.diagonal γ * V.transpose))

/-- The first spectral power sum / relative trace is unchanged at the poles. -/
theorem trace_relative_eq_pole {n : ℕ}
    (G V : Matrix (Fin n) (Fin n) ℝ) (γ : Fin n → ℝ) :
    (G⁻¹ * (V * Matrix.diagonal γ * V.transpose)).trace =
      (poleOperator G V γ).trace := by
  simpa only [poleOperator, kernelMatrix, Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (G⁻¹ * V) (Matrix.diagonal γ * V.transpose))

/-- The pole-kernel matrix is literally the inverse-Gram evaluation pairing. -/
theorem kernelMatrix_entry {n : ℕ}
    (G V : Matrix (Fin n) (Fin n) ℝ) (a b : Fin n) :
    kernelMatrix G V a b =
      ∑ j : Fin n, ∑ i : Fin n, V i a * (G⁻¹) i j * V j b := by
  simp [kernelMatrix, Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]

end PaperAdvances.Theorem3_8_Kernel

#print axioms PaperAdvances.Theorem3_8_Kernel.charpoly_relative_eq_pole
#print axioms PaperAdvances.Theorem3_8_Kernel.trace_relative_eq_pole
#print axioms PaperAdvances.Theorem3_8_Kernel.kernelMatrix_entry
