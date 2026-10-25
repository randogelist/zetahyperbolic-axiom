import LeanPaper.Section2LagrangeFunctional

/-! The two explicit forms of the Lagrange polynomial in manuscript (2.10). -/
noncomputable section
open scoped BigOperators
open Polynomial
namespace LeanPaper.Section2LagrangeFormula
open ManuscriptChain PoleDiagonalization
open Section2LagrangeBridge Section2LagrangeIdentification Section2LagrangeFunctional

theorem polePolynomial_product (p : Real.Parameters) (a : Fin p.h) :
    polePolynomial p a =
      (∏ b ∈ (Finset.Icc (p.N + 1) p.K).erase (poleIndex p a),
        (X + C ((b : ℚ) ^ 2))) *
      C (((derivative (Real.tailD p)).eval (poleNode p a))⁻¹) := by
  rw [← archive_polynomial_eq_constructed]
  unfold Zetahyperbolic.lagrangePolePolynomial
  rw [Finset.prod_mul_distrib]
  congr 1
  rw [← map_prod, Finset.prod_inv_distrib]
  congr 2
  exact (tailD_derivative_eval p (poleIndex p a) (poleIndex_mem p a)).symm

theorem polePolynomial_rational_formula (p : Real.Parameters) (a : Fin p.h) :
    algebraMap ℚ[X] (RatFunc ℚ) (polePolynomial p a) =
      algebraMap ℚ[X] (RatFunc ℚ) (Real.tailD p) /
        (algebraMap ℚ[X] (RatFunc ℚ) (X + C ((poleIndex p a : ℚ) ^ 2)) *
          algebraMap ℚ[X] (RatFunc ℚ)
            (C ((derivative (Real.tailD p)).eval (poleNode p a)))) := by
  let φ := algebraMap ℚ[X] (RatFunc ℚ)
  have hfactor : Real.tailD p = (X + C ((poleIndex p a : ℚ) ^ 2)) *
      ∏ b ∈ (Finset.Icc (p.N + 1) p.K).erase (poleIndex p a),
        (X + C ((b : ℚ) ^ 2)) :=
    (Finset.mul_prod_erase _ _ (poleIndex_mem p a)).symm
  have hx : φ (X + C ((poleIndex p a : ℚ) ^ 2)) ≠ 0 :=
    RatFunc.algebraMap_ne_zero (monic_X_add_C _).ne_zero
  have hd : (derivative (Real.tailD p)).eval (poleNode p a) ≠ 0 :=
    tailD_derivative_eval_ne_zero p _ (poleIndex_mem p a)
  have hdc : φ (C ((derivative (Real.tailD p)).eval (poleNode p a))) ≠ 0 :=
    RatFunc.algebraMap_ne_zero (by simpa using hd)
  rw [polePolynomial_product, hfactor, map_mul, map_mul]
  simp only [RatFunc.algebraMap_C, map_inv₀]
  field_simp <;> ring

/-- The second displayed product formula for the nonzero slope in (2.11). -/
theorem poleWeight_product (p : Real.Parameters) (a : Fin p.h) :
    poleWeight p a =
      (poleIndex p a : ℚ) ^ (2 * p.k) *
        (∏ ν ∈ Finset.Icc 1 p.N, ((ν : ℚ) ^ 2 - (poleIndex p a : ℚ) ^ 2)) ^
          (2 * p.m - 1) /
      ∏ b ∈ (Finset.Icc (p.N + 1) p.K).erase (poleIndex p a),
        ((b : ℚ) ^ 2 - (poleIndex p a : ℚ) ^ 2) := by
  unfold poleWeight
  rw [D_eq_Icc, eval_prod, tailD_derivative_eval p _ (poleIndex_mem p a)]
  simp only [eval_add, eval_X, eval_C, poleNode]
  simp_rw [show ∀ ν : ℕ, -(poleIndex p a : ℚ) ^ 2 + (ν : ℚ) ^ 2 =
    (ν : ℚ) ^ 2 - (poleIndex p a : ℚ) ^ 2 from fun _ => by ring]
  ring

end LeanPaper.Section2LagrangeFormula
