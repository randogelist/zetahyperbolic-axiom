import LeanPaper.ImportedSection3.PoleKernel
import LeanPaper.ImportedSection3.RealExponent
import LeanPaper.ImportedSection3.SlopeSign
import Mathlib.Tactic

/-!
# Theorem 3.8 — connection to the actual odd-zeta Hankel pencil

This file connects the generic full-characteristic-polynomial theorem to the
RATIONAL pole residues and ACTUAL zeta Gram matrix already constructed in the
verified manuscript chain. The characteristic polynomial of G^-1 M is exactly
that of the signed Christoffel–Darboux kernel pole operator.

The paper defines a symmetric relative matrix G^-1/2 M G^-1/2. The additional
identification with that symmetric realization and the derivative-under-the-
integral Jacobi identity are not claimed here. No witness is added.
-/

noncomputable section
open scoped BigOperators
open Matrix

namespace PaperAdvances.Theorem3_8_Actual

open ManuscriptChain

/-- The actual finite Gram matrix evaluated at the corresponding odd zeta. -/
def actualGram (p : Real.Parameters) : Matrix (Fin p.h) (Fin p.h) ℝ :=
  Real.gram p (Real.zeta p.weight)

/-- Columns are monomial evaluations at the paper's negative-square poles. -/
def actualV (p : Real.Parameters) : Matrix (Fin p.h) (Fin p.h) ℝ :=
  Proposition3_2.vandermonde p

/-- Inherited real-exponent coefficient at its original odd value. -/
def actualGamma (p : Real.Parameters) (a : Fin p.h) : ℝ :=
  Proposition3_2.gamma p (p.weight : ℝ) a

/-- The paper's pole coefficients are recovered exactly, not up to scaling. -/
theorem actualGamma_eq (p : Real.Parameters) (a : Fin p.h) :
    actualGamma p a = (PoleDiagonalization.poleWeight p a : ℝ) :=
  Proposition3_2.gamma_odd p a

/-- Connect the actual rational residue matrix to the previously proved
    real-exponent Vandermonde slope, at s = 2k+1. -/
theorem actual_derivative_eq_real_slope (p : Real.Parameters) :
    Real.derivativeMatrix p = Proposition3_2.slope p (p.weight : ℝ) := by
  ext i j
  rw [Proposition3_2.slope_entry]
  simp only [Proposition3_2.gamma_odd]
  change ((Real.entryM p i.val j.val : ℚ) : ℝ) =
    ∑ a : Fin p.h,
      ((PoleDiagonalization.poleVandermonde p i a : ℚ) : ℝ) *
        ((PoleDiagonalization.poleWeight p a : ℚ) : ℝ) *
        ((PoleDiagonalization.poleVandermonde p j a : ℚ) : ℝ)
  exact_mod_cast (PoleDiagonalization.entryM_eq_sum_poleWeight p i j)

/-- The actual derivative matrix, not a symbolic stand-in, factors over poles. -/
theorem actual_derivative_factorization (p : Real.Parameters) :
    Real.derivativeMatrix p =
      actualV p * Matrix.diagonal (actualGamma p) * (actualV p).transpose := by
  -- Both aliases are transparent definitions of the already proved real-s slope.
  -- No `simpa` or rewrite of higher-order functions is required.
  change Real.derivativeMatrix p = Proposition3_2.slope p (p.weight : ℝ)
  exact actual_derivative_eq_real_slope p

/-- The actual rational odd-zeta pencil's Christoffel–Darboux pole matrix. -/
def actualPoleKernel (p : Real.Parameters) : Matrix (Fin p.h) (Fin p.h) ℝ :=
  Theorem3_8_Kernel.kernelMatrix (actualGram p) (actualV p)

/-- Exact spectral equivalence as characteristic polynomials, all matrix sizes. -/
theorem actual_relative_charpoly_eq_pole (p : Real.Parameters) :
    ((actualGram p)⁻¹ * Real.derivativeMatrix p).charpoly =
      (Theorem3_8_Kernel.poleOperator (actualGram p) (actualV p)
        (actualGamma p)).charpoly := by
  rw [actual_derivative_factorization]
  exact Theorem3_8_Kernel.charpoly_relative_eq_pole
    (actualGram p) (actualV p) (actualGamma p)

/-- Equality of the first spectral power sums of the actual matrices. -/
theorem actual_relative_trace_eq_pole (p : Real.Parameters) :
    ((actualGram p)⁻¹ * Real.derivativeMatrix p).trace =
      (Theorem3_8_Kernel.poleOperator (actualGram p) (actualV p)
        (actualGamma p)).trace := by
  rw [actual_derivative_factorization]
  exact Theorem3_8_Kernel.trace_relative_eq_pole
    (actualGram p) (actualV p) (actualGamma p)

end PaperAdvances.Theorem3_8_Actual

#print axioms PaperAdvances.Theorem3_8_Actual.actual_derivative_eq_real_slope
#print axioms PaperAdvances.Theorem3_8_Actual.actual_relative_charpoly_eq_pole
#print axioms PaperAdvances.Theorem3_8_Actual.actual_relative_trace_eq_pole
