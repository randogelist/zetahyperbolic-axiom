import Theorem_2_5_Lagrange_Pole_Diagonalization
import Mathlib.Algebra.Polynomial.PartialFractions
import Mathlib.Tactic

/-!
Constructive simple-pole partial-fraction decomposition of the actual
rational Hankel kernel numerator over the negative-square pole lattice.
-/

noncomputable section
open scoped BigOperators
open Polynomial

namespace ManuscriptChain.PartialFractions

def kernelNumerator (p : Real.Parameters) (d : ℕ) : ℚ[X] :=
  Real.D p.N ^ (2 * p.m - 1) * X ^ d

structure KernelPartialFractionData (p : Real.Parameters) (d : ℕ) where
  quotient : ℚ[X]
  remainder : ℕ → ℚ[X]
  remainder_degree : ∀ a ∈ Finset.Icc (p.N + 1) p.K,
    (remainder a).degree <
      (Polynomial.X + Polynomial.C ((a : ℚ) ^ 2)).degree
  numerator_eq :
    kernelNumerator p d =
      quotient * Real.tailD p +
        ∑ a ∈ Finset.Icc (p.N + 1) p.K,
          remainder a * ∏ b ∈ (Finset.Icc (p.N + 1) p.K).erase a,
            (Polynomial.X + Polynomial.C ((b : ℚ) ^ 2))

theorem tailPoleFactors_pairwise_coprime (p : Real.Parameters) :
    Set.Pairwise (↑(Finset.Icc (p.N + 1) p.K) : Set ℕ)
      (fun a b : ℕ =>
        IsCoprime
          (Polynomial.X + Polynomial.C ((a : ℚ) ^ 2))
          (Polynomial.X + Polynomial.C ((b : ℚ) ^ 2))) := by
  intro a ha b hb hab
  have habq : (a : ℚ) ≠ b := by exact_mod_cast hab
  have hdiff : (a : ℚ) ^ 2 - (b : ℚ) ^ 2 ≠ 0 := by
    intro h
    have hsq : (a : ℚ) ^ 2 = (b : ℚ) ^ 2 := sub_eq_zero.mp h
    have ha0 : 0 ≤ (a : ℚ) := by positivity
    have hb0 : 0 ≤ (b : ℚ) := by positivity
    have heq : (a : ℚ) = (b : ℚ) := by
      nlinarith [sq_nonneg ((a : ℚ) - (b : ℚ))]
    exact habq heq
  let c : ℚ := ((a : ℚ) ^ 2 - (b : ℚ) ^ 2)⁻¹
  refine ⟨Polynomial.C c, -Polynomial.C c, ?_⟩
  have hsub :
      (Polynomial.X + Polynomial.C ((a : ℚ) ^ 2)) -
        (Polynomial.X + Polynomial.C ((b : ℚ) ^ 2)) =
      Polynomial.C ((a : ℚ) ^ 2 - (b : ℚ) ^ 2) := by
    rw [Polynomial.C_sub]
    ring
  calc
    Polynomial.C c * (Polynomial.X + Polynomial.C ((a : ℚ) ^ 2)) +
        (-Polynomial.C c) * (Polynomial.X + Polynomial.C ((b : ℚ) ^ 2)) =
      Polynomial.C c *
        ((Polynomial.X + Polynomial.C ((a : ℚ) ^ 2)) -
          (Polynomial.X + Polynomial.C ((b : ℚ) ^ 2))) := by ring
    _ = Polynomial.C c * Polynomial.C ((a : ℚ) ^ 2 - (b : ℚ) ^ 2) := by rw [hsub]
    _ = 1 := by
      rw [← Polynomial.C_mul]
      simp [c, hdiff]

theorem kernelNumerator_partial_fraction_exists (p : Real.Parameters) (d : ℕ) :
    Nonempty (KernelPartialFractionData p d) := by
  classical
  obtain ⟨q, r, hr, hf⟩ :=
    Polynomial.eq_quo_mul_prod_add_sum_rem_mul_prod
      (f := kernelNumerator p d)
      (s := Finset.Icc (p.N + 1) p.K)
      (g := fun a : ℕ => Polynomial.X + Polynomial.C ((a : ℚ) ^ 2))
      (hg := by
        intro a ha
        exact Polynomial.monic_X_add_C _)
      (hgg := by simpa using tailPoleFactors_pairwise_coprime p)
  refine ⟨⟨q, r, hr, ?_⟩⟩
  simpa [Real.tailD] using hf

noncomputable def data (p : Real.Parameters) (d : ℕ) :
    KernelPartialFractionData p d :=
  Classical.choice (kernelNumerator_partial_fraction_exists p d)

end ManuscriptChain.PartialFractions
