import LeanPaper.Rebuild.PartialFractionsResidues
import Theorem_3_1_Rational_Integral_Bridge
import Theorem_3_1_Pole_Integral_Identity

/-!
Connect the commit-pinned `snditeration` partial-fraction construction to the
existing manuscript kernel. The polynomial identity applies directly to every
`Real.Parameters` value. All tail poles have positive natural index, so its
square-variable evaluation has no pole at any real `y`, including zero.

This is an algebraic replacement input. It neither asserts general RatFunc
representation independence nor removes the analytic/admissibility hypotheses
from the weighted Gram construction.
-/

noncomputable section
open scoped BigOperators
open Polynomial MeasureTheory Set

namespace LeanPaper.RebuildKernelBridge

open ManuscriptChain

theorem tailD_eval_square_pos (p : Real.Parameters) (y : ℝ) :
    0 < (Real.tailD p).eval₂ (algebraMap ℚ ℝ) (y ^ 2) := by
  simp only [Real.tailD, Polynomial.eval₂_finsetProd, Polynomial.eval₂_add,
    Polynomial.eval₂_X, Polynomial.eval₂_C, Polynomial.eval₂_pow,
    Polynomial.eval₂_natCast, map_pow, map_natCast]
  apply Finset.prod_pos
  intro a ha
  have haN : 0 < a := lt_of_lt_of_le (Nat.succ_pos p.N) (Finset.mem_Icc.mp ha).1
  have haR : 0 < (a : ℝ) := by exact_mod_cast haN
  positivity

/-- The rebuilt polynomial-plus-poles identity evaluates to the existing
resolved kernel for every real square argument and arbitrary parameter data. -/
theorem resolvedKernel_eq_fraction_all_real (p : Real.Parameters)
    (i j : ℕ) (y : ℝ) :
    Hyperbolic.resolvedKernel p i j y =
      (Real.numerator p i j).eval₂ (algebraMap ℚ ℝ) (y ^ 2) /
        (Real.tailD p).eval₂ (algebraMap ℚ ℝ) (y ^ 2) := by
  let s := Finset.Icc (p.N + 1) p.K
  let T : ℝ := ∏ a ∈ s, (y ^ 2 + (a : ℝ) ^ 2)
  have hev : (Real.tailD p).eval₂ (algebraMap ℚ ℝ) (y ^ 2) = T := by
    simp only [Real.tailD, Polynomial.eval₂_finsetProd, Polynomial.eval₂_add,
      Polynomial.eval₂_X, Polynomial.eval₂_C, Polynomial.eval₂_pow,
    Polynomial.eval₂_natCast, map_pow, map_natCast]
    rfl
  have hT : T ≠ 0 := by
    rw [← hev]
    exact ne_of_gt (tailD_eval_square_pos p y)
  rw [hev]
  apply (eq_div_iff hT).2
  have hf := congrArg (fun q : ℚ[X] => q.eval₂ (algebraMap ℚ ℝ) (y ^ 2))
    (PartialFractions.rational_kernel_decomposition p i j)
  simp only [Polynomial.eval₂_add, Polynomial.eval₂_mul,
    Polynomial.eval₂_finsetSum, Polynomial.eval₂_finsetProd, Polynomial.eval₂_C,
    Polynomial.eval₂_X, Polynomial.eval₂_pow, Polynomial.eval₂_natCast, map_pow, map_natCast] at hf
  rw [hev] at hf
  rw [hf]
  unfold Hyperbolic.resolvedKernel
  rw [add_mul, Finset.sum_mul]
  have heq (q : ℚ[X]) : Real.evalQ q (y ^ 2) =
      q.eval₂ (algebraMap ℚ ℝ) (y ^ 2) := by
    simp [Real.evalQ, Real.realPolynomial, Polynomial.eval_map]
    rfl
  rw [heq]
  congr 1
  apply Finset.sum_congr rfl
  intro a ha
  have ha' : a ∈ s := ha
  have haN : 0 < a := lt_of_lt_of_le (Nat.succ_pos p.N) (Finset.mem_Icc.mp ha).1
  have haR : 0 < (a : ℝ) := by exact_mod_cast haN
  have hd : y ^ 2 + (a : ℝ) ^ 2 ≠ 0 := by positivity
  change (↑(Real.residue p i j a) / (y ^ 2 + (a : ℝ) ^ 2)) * T =
    ↑(Real.residue p i j a) * ∏ b ∈ s.erase a, (y ^ 2 + (b : ℝ) ^ 2)
  rw [show T = (y ^ 2 + (a : ℝ) ^ 2) * ∏ b ∈ s.erase a,
      (y ^ 2 + (b : ℝ) ^ 2) from (Finset.mul_prod_erase s _ ha').symm]
  field_simp

/-- The actual manuscript matrix entry is the integral of the rebuilt rational
kernel. Positivity of the odd-weight index is the only parameter hypothesis. -/
theorem gram_eq_fraction_integral (p : Real.Parameters) (hk : 0 < p.k)
    (i j : Fin p.h) :
    Real.gram p (Real.zeta p.weight) i j =
      ∫ y : ℝ in Ioi 0,
        ((Real.numerator p i.val j.val).eval₂ (algebraMap ℚ ℝ) (y ^ 2) /
          (Real.tailD p).eval₂ (algebraMap ℚ ℝ) (y ^ 2)) *
            Hyperbolic.density p.k y := by
  rw [Hyperbolic.gram_eq_resolvedKernel_integral p
    (Hyperbolic.poleIntegralIdentity p.k hk) i j]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro y _
  dsimp only
  rw [resolvedKernel_eq_fraction_all_real]

end LeanPaper.RebuildKernelBridge
