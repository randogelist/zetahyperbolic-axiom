import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Data.Real.Basic

/-!
# Dimension restriction on the fixed-K reading of Theorem 5.2(3)

Positive and negative subspaces for the same real-valued quadratic expression
intersect trivially. Thus two h-dimensional subspaces inside the fixed space
of polynomials of degree at most K require 2h ≤ K+1. In particular K=h=2,
allowed by the opening hypotheses of Theorem 5.2, cannot satisfy its literal
fixed-K conclusion. The intended repair must allow a sufficiently large K
depending on h, as the proof's polynomial approximation paragraph does.

This obstruction is independent of the separate missing infinite-tail
estimate in the construction of the proposed positive/negative subspaces.
-/

noncomputable section

namespace LeanPaper.KreinDimensionObstruction

open Module

theorem positive_negative_disjoint
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (q : V → ℝ) (S T : Submodule ℝ V)
    (hS : ∀ v ∈ S, v ≠ 0 → 0 < q v)
    (hT : ∀ v ∈ T, v ≠ 0 → q v < 0) : Disjoint S T := by
  rw [Submodule.disjoint_def]
  intro v hvS hvT
  by_contra hn
  exact (lt_asymm (hS v hvS hn) (hT v hvT hn))

theorem positive_negative_dimension_bound
    {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (q : V → ℝ) (S T : Submodule ℝ V)
    (hS : ∀ v ∈ S, v ≠ 0 → 0 < q v)
    (hT : ∀ v ∈ T, v ≠ 0 → q v < 0) :
    finrank ℝ S + finrank ℝ T ≤ finrank ℝ V :=
  Submodule.finrank_add_finrank_le_of_disjoint (positive_negative_disjoint q S T hS hT)

theorem fixed_degree_requires_twice_dimension
    (K h : ℕ) (q : (Fin (K+1) → ℝ) → ℝ)
    (S T : Submodule ℝ (Fin (K+1) → ℝ))
    (hS : ∀ v ∈ S, v ≠ 0 → 0 < q v)
    (hT : ∀ v ∈ T, v ≠ 0 → q v < 0)
    (dS : finrank ℝ S = h) (dT : finrank ℝ T = h) :
    2*h ≤ K+1 := by
  have hd := positive_negative_dimension_bound q S T hS hT
  simp only [dS, dT, Module.finrank_pi, Module.finrank_self, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one] at hd
  omega

theorem fixed_K_two_h_two_impossible
    (q : (Fin 3 → ℝ) → ℝ) :
    ¬ ∃ S T : Submodule ℝ (Fin 3 → ℝ),
      finrank ℝ S = 2 ∧ finrank ℝ T = 2 ∧
      (∀ v ∈ S, v ≠ 0 → 0 < q v) ∧
      (∀ v ∈ T, v ≠ 0 → q v < 0) := by
  rintro ⟨S, T, dS, dT, hS, hT⟩
  have hd := fixed_degree_requires_twice_dimension 2 2 q S T hS hT dS dT
  omega

end LeanPaper.KreinDimensionObstruction

#print axioms LeanPaper.KreinDimensionObstruction.fixed_K_two_h_two_impossible
