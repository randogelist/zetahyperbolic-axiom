import Mathlib.LinearAlgebra.Lagrange
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic

/-!
# Lagrange basis at the negative-square pole lattice

This module formalizes the elementary interpolation identities used in the
manuscript's finite pole basis. The matrix-pencil consequences are kept
separate, so these identities can be checked independently.
-/

namespace Zetahyperbolic

/--
The Lagrange polynomial at the node `-a²`, formed from all other indices
in the finite pole range `N < b ≤ K`.
-/
noncomputable def lagrangePolePolynomial (N K a : ℕ) : Polynomial ℚ :=
  ∏ b ∈ (Finset.Icc (N + 1) K).erase a,
    (Polynomial.X + Polynomial.C ((b : ℚ) ^ 2)) *
      Polynomial.C (((b : ℚ) ^ 2 - (a : ℚ) ^ 2)⁻¹)

/-- The Lagrange basis polynomial takes value one at its own pole node. -/
theorem lagrangePolePolynomial_eval_self
    (N K a : ℕ) (ha : a ∈ Finset.Icc (N + 1) K) :
    Polynomial.eval (-((a : ℚ) ^ 2)) (lagrangePolePolynomial N K a) = 1 := by
  classical
  unfold lagrangePolePolynomial
  rw [Polynomial.eval_prod]
  simp only [Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_X,
    Polynomial.eval_C]
  apply Finset.prod_eq_one
  intro b hb
  have hba : b ≠ a := (Finset.mem_erase.mp hb).1
  have hdiff : (b : ℚ) ^ 2 - (a : ℚ) ^ 2 ≠ 0 := by
    intro h
    have hs : (b : ℚ) ^ 2 = (a : ℚ) ^ 2 := sub_eq_zero.mp h
    have hb0 : (0 : ℚ) ≤ (b : ℚ) := by positivity
    have ha0 : (0 : ℚ) ≤ (a : ℚ) := by positivity
    have hcast : (b : ℚ) = (a : ℚ) := by
      nlinarith [sq_nonneg ((b : ℚ) - (a : ℚ))]
    exact hba (by exact_mod_cast hcast)
  rw [show -((a : ℚ) ^ 2) + (b : ℚ) ^ 2 =
      (b : ℚ) ^ 2 - (a : ℚ) ^ 2 by ring]
  simp [hdiff]

/-- Distinct Lagrange basis polynomials vanish at the other pole nodes. -/
theorem lagrangePolePolynomial_eval_ne
    (N K a b : ℕ) (ha : a ∈ Finset.Icc (N + 1) K)
    (hb : b ∈ Finset.Icc (N + 1) K) (hab : a ≠ b) :
    Polynomial.eval (-((b : ℚ) ^ 2)) (lagrangePolePolynomial N K a) = 0 := by
  classical
  unfold lagrangePolePolynomial
  rw [Polynomial.eval_prod]
  apply Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hab.symm, hb⟩)
  simp only [Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_X,
    Polynomial.eval_C]
  rw [show -((b : ℚ) ^ 2) + (b : ℚ) ^ 2 = 0 by ring]
  simp


/-- Kronecker-delta evaluation law for the finite Lagrange pole basis. -/
theorem lagrangePolePolynomial_eval
    (N K a b : ℕ)
    (ha : a ∈ Finset.Icc (N + 1) K)
    (hb : b ∈ Finset.Icc (N + 1) K) :
    Polynomial.eval (-((b : ℚ) ^ 2)) (lagrangePolePolynomial N K a) =
      if a = b then 1 else 0 := by
  by_cases hab : a = b
  · subst b
    simp [lagrangePolePolynomial_eval_self N K a ha]
  · simp [hab, lagrangePolePolynomial_eval_ne N K a b ha hb hab]

/-- A Lagrange pole basis polynomial equals one at a node only at its own index. -/
theorem lagrangePolePolynomial_eval_eq_one_iff
    (N K a b : ℕ)
    (ha : a ∈ Finset.Icc (N + 1) K)
    (hb : b ∈ Finset.Icc (N + 1) K) :
    Polynomial.eval (-((b : ℚ) ^ 2)) (lagrangePolePolynomial N K a) = 1
      ↔ a = b := by
  constructor
  · intro h
    by_contra hab
    have hz := lagrangePolePolynomial_eval_ne N K a b ha hb hab
    rw [h] at hz
    norm_num at hz
  · intro h
    subst b
    exact lagrangePolePolynomial_eval_self N K a ha


/-- Evaluation of the Lagrange basis at all pole nodes gives the identity matrix. -/
noncomputable def lagrangePoleEvaluationMatrix (N K : ℕ) :
    Matrix (↥(Finset.Icc (N + 1) K)) (↥(Finset.Icc (N + 1) K)) ℚ :=
  fun a b => Polynomial.eval (-((b.1 : ℚ) ^ 2))
    (lagrangePolePolynomial N K a.1)

/-- The pole evaluation matrix is the identity. -/
theorem lagrangePoleEvaluationMatrix_eq_one (N K : ℕ) :
    lagrangePoleEvaluationMatrix N K = 1 := by
  classical
  ext a b
  change Polynomial.eval (-((b.1 : ℚ) ^ 2))
      (lagrangePolePolynomial N K a.1) = (if a = b then (1 : ℚ) else 0)
  rw [lagrangePolePolynomial_eval N K a.1 b.1 a.2 b.2]
  by_cases h : a.1 = b.1
  · have hab : a = b := Subtype.ext h
    simp [h, hab]
  · have hab : a ≠ b := by
      intro hab
      exact h (congrArg Subtype.val hab)
    simp [h, hab]

/-- The Lagrange pole evaluation matrix has determinant one. -/
theorem det_lagrangePoleEvaluationMatrix (N K : ℕ) :
    Matrix.det (lagrangePoleEvaluationMatrix N K) = 1 := by
  rw [lagrangePoleEvaluationMatrix_eq_one]
  simp


/-- The Lagrange evaluation matrix has nonzero determinant. -/
theorem lagrangePoleEvaluationMatrix_det_ne_zero (N K : ℕ) :
    Matrix.det (lagrangePoleEvaluationMatrix N K) ≠ 0 := by
  rw [det_lagrangePoleEvaluationMatrix]
  norm_num

/-- The Lagrange evaluation matrix acts as the identity on coefficient vectors. -/
theorem lagrangePoleEvaluationMatrix_mulVec (N K : ℕ)
    (v : ↥(Finset.Icc (N + 1) K) → ℚ) :
    Matrix.mulVec (lagrangePoleEvaluationMatrix N K) v = v := by
  rw [lagrangePoleEvaluationMatrix_eq_one]
  simp


end Zetahyperbolic
