import LeanPaper.Rebuild.PartialFractionsQuotient
import Mathlib.Tactic

/-!
# Exact pole coefficients of the manuscript rational Hankel kernel

The residue of the coprime partial-fraction expansion at a negative-square
pole equals the Section 2 coefficient obtained by differentiating the tail
denominator. This completes the algebraic polynomial-plus-poles identity.
-/

noncomputable section
open scoped BigOperators
open Polynomial

namespace ManuscriptChain.PartialFractions

def residueCoeff (p : Real.Parameters) (d a : ℕ) : ℚ :=
  ((data p d).remainder a).coeff 0

theorem residueCoeff_eq_formula (p : Real.Parameters) (d a : ℕ)
    (ha : a ∈ Finset.Icc (p.N + 1) p.K) :
    residueCoeff p d a =
      (kernelNumerator p d).eval (-(a : ℚ) ^ 2) /
        ∏ b ∈ (Finset.Icc (p.N + 1) p.K).erase a,
          ((b : ℚ) ^ 2 - (a : ℚ) ^ 2) := by
  classical
  let s := Finset.Icc (p.N + 1) p.K
  let x : ℚ := -((a : ℚ) ^ 2)
  have htail : (Real.tailD p).eval x = 0 := by
    unfold Real.tailD
    rw [eval_prod]
    apply Finset.prod_eq_zero ha
    simp [x]
  have hprod (b : ℕ) :
      (∏ c ∈ s.erase b, (X + C ((c : ℚ) ^ 2))).eval x =
        ∏ c ∈ s.erase b, ((c : ℚ) ^ 2 - (a : ℚ) ^ 2) := by
    rw [eval_prod]
    apply Finset.prod_congr rfl
    intro c hc
    simp [x, sub_eq_add_neg, add_comm]
  have heval : (kernelNumerator p d).eval x =
      ∑ b ∈ s, ((data p d).remainder b *
        ∏ c ∈ s.erase b, (X + C ((c : ℚ) ^ 2))).eval x := by
    have h := congrArg (Polynomial.eval x) (data p d).numerator_eq
    rw [eval_add, eval_mul, htail] at h
    simp only [mul_zero, zero_add, eval_finsetSum] at h
    simpa [s] using h
  have hsum :
      (∑ b ∈ s, ((data p d).remainder b *
        ∏ c ∈ s.erase b, (X + C ((c : ℚ) ^ 2))).eval x) =
      residueCoeff p d a * ∏ c ∈ s.erase a, ((c : ℚ) ^ 2 - (a : ℚ) ^ 2) := by
    rw [Finset.sum_eq_single a]
    · rw [eval_mul, data_remainder_constant p d a ha, eval_C, hprod a]
      rfl
    · intro b hb hba
      rw [eval_mul, hprod b]
      apply mul_eq_zero.mpr
      right
      apply Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨Ne.symm hba, ha⟩)
      simp
    · intro hnot
      exact (hnot ha).elim
  rw [hsum] at heval
  have hden : (∏ c ∈ s.erase a, ((c : ℚ) ^ 2 - (a : ℚ) ^ 2)) ≠ 0 := by
    rw [← PoleDiagonalization.tailD_derivative_eval p a ha]
    exact PoleDiagonalization.tailD_derivative_eval_ne_zero p a ha
  have hdiv := congrArg (fun y : ℚ => y /
    ∏ c ∈ s.erase a, ((c : ℚ) ^ 2 - (a : ℚ) ^ 2)) heval
  simp only [mul_div_cancel_right₀ _ hden] at hdiv
  exact hdiv.symm

theorem residueCoeff_eq_actual (p : Real.Parameters) (i j a : ℕ)
    (ha : a ∈ Finset.Icc (p.N + 1) p.K) :
    residueCoeff p (i + j) a = Real.residue p i j a := by
  rw [residueCoeff_eq_formula p (i + j) a ha]
  unfold Real.residue Real.numerator kernelNumerator
  rw [PoleDiagonalization.tailD_derivative_eval p a ha]

theorem rational_kernel_decomposition (p : Real.Parameters) (i j : ℕ) :
    Real.numerator p i j =
      Real.quotient p i j * Real.tailD p +
        ∑ a ∈ Finset.Icc (p.N + 1) p.K,
          C (Real.residue p i j a) *
            ∏ b ∈ (Finset.Icc (p.N + 1) p.K).erase a,
              (X + C ((b : ℚ) ^ 2)) := by
  classical
  change kernelNumerator p (i + j) = _
  rw [(data p (i + j)).numerator_eq,
    data_quotient_eq_actual p i j]
  congr 1
  apply Finset.sum_congr rfl
  intro a ha
  rw [data_remainder_constant p (i + j) a ha]
  simpa only [residueCoeff] using congrArg
    (fun c : ℚ => C c *
      ∏ b ∈ (Finset.Icc (p.N + 1) p.K).erase a, (X + C ((b : ℚ) ^ 2)))
    (residueCoeff_eq_actual p i j a ha)

end ManuscriptChain.PartialFractions
