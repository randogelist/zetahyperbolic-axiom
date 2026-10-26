import Paper.Corollary_3_6
import ProofAdvances.Theorem_3_4
import Mathlib.Tactic

/-!
# Corollary 3.6 — corrected finite atomic Stieltjes moment statement

The paper's finite reciprocal-root moments form a positive semidefinite
Hankel system, not a positive definite system in every order.
The Gram factorization below is for arbitrary numbers of atoms and
arbitrary truncation order. The explicit two-atom determinant identities
exhibit positivity at order 2 and rank obstruction at order 3.

No statement of irrationality, spectral gap, or infinite support is used.
-/

noncomputable section
open scoped BigOperators
open Matrix

namespace PaperAdvances.Corollary3_6

/-- Hankel matrix of the first `n` moments of `h` real atoms. -/
def finiteHankel {h : ℕ} (u : Fin h → ℝ) (n : ℕ) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun i j => ∑ k : Fin h, u k ^ (i.val + j.val)

/-- Rectangular Vandermonde matrix, with columns indexed by atoms. -/
def finiteVandermonde {h : ℕ} (u : Fin h → ℝ) (n : ℕ) :
    Matrix (Fin n) (Fin h) ℝ :=
  fun i k => u k ^ i.val

/-- Finite atomic Hankel = Vandermonde times its transpose.
    Thus positivity is of Gram type and the rank is at most `h`. -/
theorem finite_hankel_gram {h : ℕ} (u : Fin h → ℝ) (n : ℕ) :
    finiteHankel u n =
      finiteVandermonde u n * (finiteVandermonde u n)ᵀ := by
  classical
  ext i j
  simp [finiteHankel, finiteVandermonde, Matrix.mul_apply, pow_add]

/-- Two distinct atoms give a nonnegative order-two Hankel determinant. -/
theorem two_atom_order_two_det (u v : ℝ) :
    (2 : ℝ) * (u^2 + v^2) - (u + v)^2 = (u - v)^2 := by
  ring

theorem two_atom_order_two_nonnegative (u v : ℝ) :
    0 ≤ (2 : ℝ) * (u^2 + v^2) - (u + v)^2 := by
  rw [two_atom_order_two_det]
  positivity

/-- The order-three Hankel determinant of any two-atom measure is zero.
    This is an exact counterexample to strict positivity at every order. -/
theorem two_atom_order_three_det_zero (u v : ℝ) :
    (2 : ℝ) * ((u^2 + v^2)*(u^4 + v^4) - (u^3 + v^3)^2)
      - (u+v) * ((u+v)*(u^4 + v^4) - (u^2 + v^2)*(u^3 + v^3))
      + (u^2 + v^2) * ((u+v)*(u^3 + v^3) - (u^2 + v^2)^2) = 0 := by
  ring

end PaperAdvances.Corollary3_6

#print axioms PaperAdvances.Corollary3_6.finite_hankel_gram
#print axioms PaperAdvances.Corollary3_6.two_atom_order_three_det_zero
