import LeanPaper.Section2LagrangeBasis
import Theorem_2_5_Lagrange_Pole_Diagonalization

/-!
Explicit interpolation polynomials on the actual negative-square pole nodes.
The coefficient matrix is proved equal to the inverse Vandermonde already
used by the manuscript pencil; no matrix inverse is assumed as polynomial data.
The archive18 Lagrange basis and Mathlib's finite interpolation construction
supply the source-level input. The rational-function-domain identification
remains separate from this finite polynomial basis theorem.
-/

noncomputable section
open scoped BigOperators
open Polynomial

namespace LeanPaper.Section2LagrangeBridge
open ManuscriptChain ManuscriptChain.PoleDiagonalization

def polePolynomial (p : Real.Parameters) (a : Fin p.h) : ℚ[X] :=
  Lagrange.basis Finset.univ (poleNode p) a

theorem polePolynomial_eval (p : Real.Parameters) (a b : Fin p.h) :
    (polePolynomial p a).eval (poleNode p b) = if a = b then 1 else 0 := by
  classical
  by_cases hab : a = b
  · subst b
    simp only [polePolynomial, if_pos rfl]
    exact Lagrange.eval_basis_self (poleNode_injective p).injOn (Finset.mem_univ a)
  · simp only [polePolynomial, if_neg hab]
    exact Lagrange.eval_basis_of_ne hab (Finset.mem_univ b)

theorem polePolynomial_natDegree (p : Real.Parameters) (a : Fin p.h) :
    (polePolynomial p a).natDegree = p.h - 1 := by
  simpa [polePolynomial] using
    (Lagrange.natDegree_basis (poleNode_injective p).injOn (Finset.mem_univ a))

theorem polePolynomial_ne_zero (p : Real.Parameters) (a : Fin p.h) :
    polePolynomial p a ≠ 0 := by
  exact Lagrange.basis_ne_zero (poleNode_injective p).injOn (Finset.mem_univ a)

def coefficientMatrix (p : Real.Parameters) : Matrix (Fin p.h) (Fin p.h) ℚ :=
  fun a i => (polePolynomial p a).coeff i.val

theorem polePolynomial_eval_sum (p : Real.Parameters) (a : Fin p.h) (x : ℚ) :
    (polePolynomial p a).eval x =
      ∑ i : Fin p.h, coefficientMatrix p a i * x ^ i.val := by
  have hpos : 0 < p.h := Nat.zero_lt_of_lt a.isLt
  rw [Polynomial.eval_eq_sum_range, polePolynomial_natDegree,
    Nat.sub_add_cancel hpos]
  exact (Fin.sum_univ_eq_sum_range
    (fun i => (polePolynomial p a).coeff i * x ^ i) p.h).symm

theorem coefficientMatrix_mul_vandermonde (p : Real.Parameters) :
    coefficientMatrix p * poleVandermonde p = 1 := by
  classical
  ext a b
  rw [Matrix.mul_apply]
  change (∑ i : Fin p.h, coefficientMatrix p a i * poleNode p b ^ i.val) = _
  rw [← polePolynomial_eval_sum, polePolynomial_eval]
  rfl

theorem coefficientMatrix_eq_inverse (p : Real.Parameters) :
    coefficientMatrix p = (poleVandermonde p)⁻¹ := by
  have hv : IsUnit (poleVandermonde p).det :=
    isUnit_iff_ne_zero.mpr (poleVandermonde_det_ne_zero p)
  calc
    coefficientMatrix p = coefficientMatrix p *
        (poleVandermonde p * (poleVandermonde p)⁻¹) := by
      rw [Matrix.mul_nonsing_inv _ hv, Matrix.mul_one]
    _ = (poleVandermonde p)⁻¹ := by
      rw [← Matrix.mul_assoc, coefficientMatrix_mul_vandermonde, Matrix.one_mul]

theorem coefficientMatrix_det_ne_zero (p : Real.Parameters) :
    (coefficientMatrix p).det ≠ 0 := by
  rw [coefficientMatrix_eq_inverse, Matrix.det_nonsing_inv, Ring.inverse_eq_inv]
  exact inv_ne_zero (poleVandermonde_det_ne_zero p)

theorem lagrange_pencil_eq_actual (p : Real.Parameters) :
    BasisInvariance.changeBasisPencil (Real.pencil p)
      (coefficientMatrix p) (coefficientMatrix p) = poleDiagonalPencil p := by
  rw [coefficientMatrix_eq_inverse]
  rfl

theorem actual_lagrange_entries (p : Real.Parameters) (a b : Fin p.h) :
    poleDiagonalPencil p a b =
      ∑ i : Fin p.h, ∑ j : Fin p.h,
        C ((polePolynomial p a).coeff i.val * (polePolynomial p b).coeff j.val) *
          Real.pencil p i j := by
  rw [← lagrange_pencil_eq_actual, BasisInvariance.changeBasisPencil_apply]
  rfl

theorem actual_lagrange_slope (p : Real.Parameters) :
    coefficientMatrix p * rationalDerivativeMatrix p *
      (coefficientMatrix p).transpose = Matrix.diagonal (poleWeight p) := by
  rw [coefficientMatrix_eq_inverse]
  exact pole_slope_diagonal p

end LeanPaper.Section2LagrangeBridge
