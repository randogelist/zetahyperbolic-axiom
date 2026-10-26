import LeanPaper.Section2LagrangeBridge

/-! Identify the supplied explicit product polynomial with the constructed
finite interpolation polynomial used in the actual pencil bridge. -/

noncomputable section
open scoped BigOperators
open Polynomial

namespace LeanPaper.Section2LagrangeIdentification
open ManuscriptChain ManuscriptChain.PoleDiagonalization
open LeanPaper.Section2LagrangeBridge

theorem negative_square_injective :
    Function.Injective (fun a : ℕ => -((a : ℚ) ^ 2)) := by
  intro a b hab
  have hsq : (a : ℚ) ^ 2 = (b : ℚ) ^ 2 := by linarith
  have heq := (sq_eq_sq₀ (show (0 : ℚ) ≤ a by positivity)
    (show (0 : ℚ) ≤ b by positivity)).mp hsq
  exact_mod_cast heq

theorem archive_polynomial_eq_mathlib (N K a : ℕ) :
    Zetahyperbolic.lagrangePolePolynomial N K a =
      Lagrange.basis (Finset.Icc (N + 1) K) (fun b : ℕ => -((b : ℚ) ^ 2)) a := by
  classical
  unfold Zetahyperbolic.lagrangePolePolynomial Lagrange.basis
  apply Finset.prod_congr rfl
  intro b hb
  unfold Lagrange.basisDivisor
  have hd : -((a : ℚ) ^ 2) - -((b : ℚ) ^ 2) =
      (b : ℚ) ^ 2 - (a : ℚ) ^ 2 := by ring
  rw [hd, Polynomial.C_neg]
  ring

theorem archive_polynomial_natDegree (p : Real.Parameters) (a : Fin p.h) :
    (Zetahyperbolic.lagrangePolePolynomial p.N p.K (poleIndex p a)).natDegree =
      p.h - 1 := by
  rw [archive_polynomial_eq_mathlib,
    Lagrange.natDegree_basis negative_square_injective.injOn (poleIndex_mem p a)]
  simp [Nat.card_Icc, Real.Parameters.h]

theorem archive_polynomial_eval (p : Real.Parameters) (a b : Fin p.h) :
    (Zetahyperbolic.lagrangePolePolynomial p.N p.K (poleIndex p a)).eval
      (poleNode p b) = if a = b then 1 else 0 := by
  rw [poleNode, Zetahyperbolic.lagrangePolePolynomial_eval p.N p.K
    (poleIndex p a) (poleIndex p b) (poleIndex_mem p a) (poleIndex_mem p b)]
  by_cases hab : a = b
  · simp [hab]
  · have hidx : poleIndex p a ≠ poleIndex p b := by
      intro h
      apply hab
      apply Fin.ext
      dsimp [poleIndex] at h
      omega
    simp [hab, hidx]

theorem archive_polynomial_eq_constructed (p : Real.Parameters) (a : Fin p.h) :
    Zetahyperbolic.lagrangePolePolynomial p.N p.K (poleIndex p a) =
      polePolynomial p a := by
  have hpos : 0 < p.h := Nat.zero_lt_of_lt a.isLt
  apply Polynomial.eq_of_degrees_lt_of_eval_index_eq Finset.univ
    (poleNode_injective p).injOn
  · apply lt_of_le_of_lt Polynomial.degree_le_natDegree
    rw [archive_polynomial_natDegree]
    simpa using (show (↑(p.h - 1) : WithBot ℕ) < ↑p.h from
      (WithBot.coe_lt_coe (a := p.h - 1) (b := p.h)).mpr
        (show p.h - 1 < p.h from by omega))
  · apply lt_of_le_of_lt Polynomial.degree_le_natDegree
    rw [polePolynomial_natDegree]
    simpa using (show (↑(p.h - 1) : WithBot ℕ) < ↑p.h from
      (WithBot.coe_lt_coe (a := p.h - 1) (b := p.h)).mpr
        (show p.h - 1 < p.h from by omega))
  · intro b hb
    rw [archive_polynomial_eval, polePolynomial_eval]

theorem archive_coefficients_eq_inverse (p : Real.Parameters) (a i : Fin p.h) :
    (Zetahyperbolic.lagrangePolePolynomial p.N p.K (poleIndex p a)).coeff i.val =
      (poleVandermonde p)⁻¹ a i := by
  rw [archive_polynomial_eq_constructed]
  exact congrFun (congrFun (coefficientMatrix_eq_inverse p) a) i

end LeanPaper.Section2LagrangeIdentification
