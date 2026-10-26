import LeanPaper.ImportedSection56.RankOneWitness
import Theorem_3_1_Zeta_Tail
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

/-!
# Principal theorem 5.2 — unconditional analytic closure of the 1×1 witness

Elementary comparison for ζ(7) = Σ_{n≥1}n⁻⁷:
  ∀ n≥1, 64*n ≤ (n+1)^6,
  1/(n+1)^7 ≤ (1/64)(1/n−1/(n+1)),
so ζ(7) ≤ 65/64 < 38/37.

Together with the frozen (37X−38) Beukers determinant, this produces
an unconditional signed rank-1 rational witness in the actual weight-seven
moment pencil.  It DOES NOT assert all-dimensional polynomial Krein cones
or the infinite-dimensional positivity/tail conclusions of manuscript 5.2.
-/

noncomputable section
open scoped BigOperators
namespace PaperOrder.PrincipalTheorems

/-- The key arithmetic inequality after the shift n↦n+1.
The difference (n+2)^6−64(n+1) is a polynomial with nonnegative
coefficients for every n≥0. -/
private theorem power_six_shift_bound (n : ℕ) :
    (64 : ℝ) * (((n + 1 : ℕ) : ℝ)) ≤ (((n + 2 : ℕ) : ℝ)) ^ 6 := by
  have hnonneg :
      (0 : ℝ) ≤ (n : ℝ)^6 + 12 * (n : ℝ)^5 +
        60 * (n : ℝ)^4 + 160 * (n : ℝ)^3 +
        240 * (n : ℝ)^2 + 128 * (n : ℝ) := by
    positivity
  have hcore :
      (64 : ℝ) * ((n : ℝ) + 1) ≤ ((n : ℝ) + 2)^6 := by
    nlinarith [hnonneg]
  simpa [Nat.cast_add] using hcore

/-- Every term beyond 1 in ζ(7) is dominated by a telescoping term. -/
private theorem tail_pointwise (n : ℕ) :
    (1 / (((n + 2 : ℕ) : ℝ)^7) : ℝ) ≤
      (1 / 64 : ℝ) *
        (1 / (((n + 1 : ℕ) : ℝ)) - 1 / (((n + 2 : ℕ) : ℝ))) := by
  have h1 : 0 < (((n + 1 : ℕ) : ℝ)) := by positivity
  have h2 : 0 < (((n + 2 : ℕ) : ℝ)) := by positivity
  have hden :
      (64 : ℝ) * (((n + 1 : ℕ) : ℝ)) * (((n + 2 : ℕ) : ℝ)) ≤
        (((n + 2 : ℕ) : ℝ)) ^ 7 := by
    calc
      (64 : ℝ) * (((n + 1 : ℕ) : ℝ)) * (((n + 2 : ℕ) : ℝ)) ≤
          ((((n + 2 : ℕ) : ℝ)) ^ 6) * (((n + 2 : ℕ) : ℝ)) :=
            mul_le_mul_of_nonneg_right (power_six_shift_bound n) (le_of_lt h2)
      _ = (((n + 2 : ℕ) : ℝ)) ^ 7 := by ring
  have hone :
      (1 / (((n + 2 : ℕ) : ℝ)^7) : ℝ) ≤
        1 / ((64 : ℝ) * (((n + 1 : ℕ) : ℝ)) * (((n + 2 : ℕ) : ℝ))) :=
    one_div_le_one_div_of_le (by positivity) hden
  calc
    (1 / (((n + 2 : ℕ) : ℝ)^7) : ℝ) ≤
        1 / ((64 : ℝ) * (((n + 1 : ℕ) : ℝ)) * (((n + 2 : ℕ) : ℝ))) := hone
    _ = (1 / 64 : ℝ) *
          (1 / (((n + 1 : ℕ) : ℝ)) - 1 / (((n + 2 : ℕ) : ℝ))) := by
      have ha : (((n + 1 : ℕ) : ℝ)) ≠ 0 := ne_of_gt h1
      have hb : (((n + 2 : ℕ) : ℝ)) ≠ 0 := ne_of_gt h2
      field_simp [ha, hb]
      push_cast
      ring

/-- The comparison series telescopes for each finite cutoff. -/
private theorem reciprocal_telescope (N : ℕ) :
    (∑ n ∈ Finset.range N,
      (1 / (((n + 1 : ℕ) : ℝ)) - 1 / (((n + 2 : ℕ) : ℝ)))) =
        1 - 1 / (((N + 1 : ℕ) : ℝ)) := by
  induction N with
  | zero => norm_num
  | succ N ih =>
      rw [Finset.sum_range_succ, ih]
      rw [show N.succ + 1 = N + 2 by omega]
      ring

/-- Purely elementary estimate: ζ(7)−1 ≤ 1/64. -/
theorem zetaSeven_tail_le_one_div_64 :
    (∑' n : ℕ, 1 / (((n + 2 : ℕ) : ℝ)^7)) ≤ (1 / 64 : ℝ) := by
  have hs : Summable (fun n : ℕ => 1 / (((n + 2 : ℕ) : ℝ)^7)) := by
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      (ManuscriptChain.Real.zeta_tail_summable (s := 7) (by norm_num) 1)
  apply hs.tsum_le_of_sum_range_le
  intro N
  calc
    (∑ n ∈ Finset.range N, (1 / (((n + 2 : ℕ) : ℝ)^7) : ℝ)) ≤
      ∑ n ∈ Finset.range N,
        (1 / 64 : ℝ) *
          (1 / (((n + 1 : ℕ) : ℝ)) - 1 / (((n + 2 : ℕ) : ℝ))) := by
        apply Finset.sum_le_sum
        intro n hn
        exact tail_pointwise n
    _ = (1 / 64 : ℝ) * (1 - 1 / (((N + 1 : ℕ) : ℝ))) := by
      rw [← Finset.mul_sum, reciprocal_telescope]
    _ ≤ (1 / 64 : ℝ) := by
      have h : 0 ≤ (1 / (((N + 1 : ℕ) : ℝ)) : ℝ) := by positivity
      nlinarith

/-- Needed for the frozen rational root 38/37: a complete unconditional
proof from the defining convergent zeta series, with no numerical oracle. -/
theorem zetaSeven_lt_38_div_37 :
    ManuscriptChain.Real.zeta 7 < (38 / 37 : ℝ) := by
  have htail :=
    (ManuscriptChain.Real.zeta_tail_sum (s := 7) (by norm_num) 1)
  have hharm : (ManuscriptChain.Real.harmonic 7 1 : ℝ) = 1 := by
    norm_num [ManuscriptChain.Real.harmonic, Finset.sum_range_succ]
  have hid :
      (∑' n : ℕ, 1 / (((n + 2 : ℕ) : ℝ)^7)) =
        ManuscriptChain.Real.zeta 7 - 1 := by
    simpa [hharm, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htail
  have hupper : ManuscriptChain.Real.zeta 7 ≤ (65 / 64 : ℝ) := by
    have hb := zetaSeven_tail_le_one_div_64
    rw [hid] at hb
    norm_num at hb ⊢
    linarith
  have hstrict : (65 / 64 : ℝ) < (38 / 37 : ℝ) := by norm_num
  exact lt_of_le_of_lt hupper hstrict

/-- Unconditional negative evaluation at the genuine ζ(7), not merely at
an auxiliary rational parameter. -/
theorem weightSeven_rankOne_negative_unconditional :
    ManuscriptChain.Real.evalQ
      (ManuscriptChain.Real.dualDelta 7 negativeWeightSevenRow)
      (ManuscriptChain.Real.zeta 7) < 0 :=
  negativeWeightSeven_below_zero_at_zeta zetaSeven_lt_38_div_37

end PaperOrder.PrincipalTheorems

#print axioms PaperOrder.PrincipalTheorems.zetaSeven_tail_le_one_div_64
#print axioms PaperOrder.PrincipalTheorems.zetaSeven_lt_38_div_37
#print axioms PaperOrder.PrincipalTheorems.weightSeven_rankOne_negative_unconditional
