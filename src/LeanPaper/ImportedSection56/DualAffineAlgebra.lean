import Mathlib.Tactic
import LeanPaper.ImportedSection56.DualMoments

/-!
# Theorem 5.1 — dual Beukers moment algebra (all finite dimensions)

The paper's off-diagonal divided differences are symmetric in r,t.
For an arbitrary rational polynomial coefficient family c, the associated
pencil has symmetric constant and slope matrices; the slope is independent
of the odd zeta value and is exactly a coefficient Gram matrix.

These are finite rational identities, separate from the integral realization
of the two-variable Beukers measure.
-/

noncomputable section
open scoped BigOperators
open Polynomial
namespace PaperOrder.CoreAlgebra
open ManuscriptChain.Real

/-- Symmetry of the rational off-diagonal divided-difference moments. -/
theorem dualConstant_swap (s r t : ℕ) :
    dualConstant s r t = dualConstant s t r := by
  unfold dualConstant
  by_cases h : r = t
  · subst t
    simp
  · have ht : t ≠ r := Ne.symm h
    simp only [h, ht, ite_false]
    have hd : ((t : ℚ) - (r : ℚ)) = -((r : ℚ) - (t : ℚ)) := by ring
    rw [hd, mul_neg, div_neg]
    ring

/-- Constant term of the dual two-variable pencil. -/
def dualConstantMatrix {h K : ℕ} (s : ℕ)
    (c : Fin h → Fin (K + 1) → ℚ) :
    Matrix (Fin h) (Fin h) ℚ :=
  fun i j => ∑ r, ∑ t,
    c i r * c j t * dualConstant s r.val t.val

/-- Coefficient of X in the dual two-variable pencil. -/
def dualSlopeMatrix {h K : ℕ}
    (c : Fin h → Fin (K + 1) → ℚ) :
    Matrix (Fin h) (Fin h) ℚ :=
  fun i j => ∑ r, c i r * c j r

/-- Explicit finite affine pencil identity; not an abstract assumption. -/
theorem dualEntry_affine {h K : ℕ} (s : ℕ)
    (c : Fin h → Fin (K + 1) → ℚ) (i j : Fin h) :
    dualEntry s c i j =
      C (dualConstantMatrix s c i j) + C (dualSlopeMatrix c i j) * X := by
  rfl

/-- The exact derivative of the dual affine entry is the coefficient Gram
entry, independent of the zeta value and all harmonic constants. -/
theorem dualEntry_derivative {h K : ℕ} (s : ℕ)
    (c : Fin h → Fin (K + 1) → ℚ) (i j : Fin h) :
    derivative (dualEntry s c i j) = C (dualSlopeMatrix c i j) := by
  rw [dualEntry_affine]
  simp only [derivative_add, derivative_mul, derivative_C,
    derivative_X, zero_mul, zero_add, add_zero, mul_one]

/-- The coefficient matrix is symmetric for every coefficient family. -/
theorem dualSlopeMatrix_symmetric {h K : ℕ}
    (c : Fin h → Fin (K + 1) → ℚ) :
    (dualSlopeMatrix c).IsSymm := by
  ext i j
  simp only [Matrix.transpose_apply, dualSlopeMatrix]
  apply Finset.sum_congr rfl
  intro r hr
  ring

end PaperOrder.CoreAlgebra

#print axioms PaperOrder.CoreAlgebra.dualConstant_swap
#print axioms PaperOrder.CoreAlgebra.dualEntry_derivative
#print axioms PaperOrder.CoreAlgebra.dualSlopeMatrix_symmetric
