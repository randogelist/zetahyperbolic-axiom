import LeanPaper.BeukersMomentSeries

/-!
# Theorem 5.1: off-diagonal moments of the actual two-variable density

The finite six-term reciprocal identity converts the absolutely summable
geometric-series moments into a difference of two ζ(6) tails. Since the
tails share the same ζ(6), their difference is an exactly rational
divided difference of harmonic sums. All endpoints and denominator
nonvanishing conditions are proved, not assumed.
-/

noncomputable section
open scoped BigOperators
open MeasureTheory Set
namespace ManuscriptChain.Beukers

private theorem reciprocal_sum_six (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0)
    (hab : a ≠ b) :
    (1 / 6 : ℝ) * (∑ j : Fin 6,
      (1 / a ^ (j.val + 1)) * (1 / b ^ (5 - j.val + 1))) =
      (1 / b ^ 6 - 1 / a ^ 6) / (6 * (a - b)) := by
  have hd : a - b ≠ 0 := sub_ne_zero.mpr hab
  simp [Fin.sum_univ_succ]
  field_simp [ha, hb, hd] <;> ring

private theorem offdiagonal_series_term (r t n : ℕ) (hrt : r ≠ t) :
    (1 / 6 : ℝ) * (∑ j : Fin 6,
      1 / (((r + n : ℕ) : ℝ) + 1) ^ (j.val + 1) *
      (1 / (((t + n : ℕ) : ℝ) + 1) ^ (5 - j.val + 1))) =
        (1 / (((t + n : ℕ) : ℝ) + 1) ^ 6 -
         1 / (((r + n : ℕ) : ℝ) + 1) ^ 6) /
          (6 * ((r : ℝ) - (t : ℝ))) := by
  let a : ℝ := (((r + n : ℕ) : ℝ) + 1)
  let b : ℝ := (((t + n : ℕ) : ℝ) + 1)
  have ha : a ≠ 0 := by dsimp [a]; positivity
  have hb : b ≠ 0 := by dsimp [b]; positivity
  have hab : a ≠ b := by
    intro heq
    have hcast : (r : ℝ) = (t : ℝ) := by
      dsimp [a, b] at heq
      push_cast at heq
      linarith
    exact hrt (by exact_mod_cast hcast)
  have h := reciprocal_sum_six a b ha hb hab
  dsimp [a, b] at h
  have hdiff :
      (((r + n : ℕ) : ℝ) + 1) - (((t + n : ℕ) : ℝ) + 1) =
        (r : ℝ) - (t : ℝ) := by push_cast; ring
  rw [hdiff] at h
  exact h

/-- Actual offdiagonal moment of the manuscript's positive Beukers weight:
    the ζ(6) series cancel, leaving the rational harmonic divided difference. -/
theorem offdiagonal_moment (r t : ℕ) (hrt : r ≠ t) :
    (∫ z, z.1 ^ r * z.2 ^ t * density z ∂squareMeasure) =
      ((Real.harmonic 6 r : ℝ) - (Real.harmonic 6 t : ℝ)) /
        (6 * ((r : ℝ) - (t : ℝ))) := by
  rw [integral_density_moment_series]
  simp_rw [offdiagonal_series_term r t _ hrt]
  have ht : Summable (fun n : ℕ =>
      1 / (((t + n : ℕ) : ℝ) + 1) ^ 6) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      Real.zeta_tail_summable (s := 6) (by norm_num) t
  have hr : Summable (fun n : ℕ =>
      1 / (((r + n : ℕ) : ℝ) + 1) ^ 6) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      Real.zeta_tail_summable (s := 6) (by norm_num) r
  have hsub := (ht.hasSum.sub hr.hasSum).tsum_eq
  rw [tsum_div_const, hsub]
  have htailt :
      (∑' n : ℕ, 1 / (((t + n : ℕ) : ℝ) + 1) ^ 6) =
        Real.zeta 6 - (Real.harmonic 6 t : ℝ) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      Real.zeta_tail_sum (s := 6) (by norm_num) t
  have htailr :
      (∑' n : ℕ, 1 / (((r + n : ℕ) : ℝ) + 1) ^ 6) =
        Real.zeta 6 - (Real.harmonic 6 r : ℝ) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      Real.zeta_tail_sum (s := 6) (by norm_num) r
  rw [htailt, htailr]
  ring

/-- Printed Theorem 5.1, both cases, on the actual ℝ×ℝ Lebesgue product. -/
theorem theorem_5_1_exact_moments (r t : ℕ) :
    (∫ z, z.1 ^ r * z.2 ^ t * density z ∂squareMeasure) =
      if h : r = t then
        Real.zeta 7 - (Real.harmonic 7 r : ℝ)
      else
        ((Real.harmonic 6 r : ℝ) - (Real.harmonic 6 t : ℝ)) /
          (6 * ((r : ℝ) - (t : ℝ))) := by
  split_ifs with h
  · subst t
    exact diagonal_moment r
  · exact offdiagonal_moment r t h

end ManuscriptChain.Beukers
