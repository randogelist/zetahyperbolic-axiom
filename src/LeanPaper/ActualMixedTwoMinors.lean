import LeanPaper.ShiftedSolidMinors

/-!
# All second-order mixed minors of the actual moment matrix

The row and column gaps need not agree. Strict adjacent moment log-convexity
implies strict monotonicity of every positive-gap moment ratio, which proves
the arbitrary-gap 2-by-2 minors directly for the actual manuscript measure.
This advances original 3.3 without asserting its higher-order mixed minors.
-/
noncomputable section
open scoped BigOperators
open MeasureTheory Matrix

namespace LeanPaper.ActualMixedTwoMinors
open ManuscriptChain

def moment (p : Real.Parameters) (n : ℕ) : ℝ :=
  ∫ t, t^n ∂ConcreteMoment.momentMeasure p

theorem moment_pos (p : Real.Parameters) (n : ℕ) : 0 < moment p n := by
  have h := ConcreteMoment.sparse_shifted_moment_det_pos p n
    (fun _ : Fin 1 => 0) (fun i j _ => Subsingleton.elim i j)
  simpa [Matrix.det_fin_one, moment] using h

theorem strict_adjacent_moment (p : Real.Parameters) (n : ℕ) :
    0 < moment p n * moment p (n + 2) - (moment p (n + 1))^2 := by
  have h := ConcreteMoment.sparse_shifted_moment_det_pos p n
    (fun i : Fin 2 => i.val) Fin.val_injective
  simpa [Matrix.det_fin_two, moment, pow_two] using h

theorem successive_ratio_strictMono (p : Real.Parameters) :
    StrictMono (fun n : ℕ => moment p (n + 1) / moment p n) := by
  apply strictMono_nat_of_lt_succ
  intro n
  apply (div_lt_div_iff₀ (moment_pos p n) (moment_pos p (n + 1))).mpr
  have h := strict_adjacent_moment p n
  nlinarith only [h]

private theorem ratio_split (p : Real.Parameters) (n d : ℕ) :
    moment p (n + (d + 1 + 1)) / moment p n =
      (moment p (n + (d + 1)) / moment p n) *
        (moment p ((n + (d + 1)) + 1) / moment p (n + (d + 1))) := by
  rw [show n + (d + 1 + 1) = (n + (d + 1)) + 1 by omega]
  field_simp [ne_of_gt (moment_pos p n), ne_of_gt (moment_pos p (n + (d + 1)))] <;> ring

/-- Every positive-gap ratio increases strictly, not just consecutive ratios. -/
theorem gap_ratio_strictMono (p : Real.Parameters) (d : ℕ) :
    StrictMono (fun n : ℕ => moment p (n + (d + 1)) / moment p n) := by
  induction d with
  | zero => simpa only [Nat.zero_add] using successive_ratio_strictMono p
  | succ d ih =>
      intro a b hab
      rw [ratio_split, ratio_split]
      have hs := successive_ratio_strictMono p
        (show a + (d + 1) < b + (d + 1) by omega)
      calc
        _ < (moment p (b + (d + 1)) / moment p b) *
            (moment p ((a + (d + 1)) + 1) / moment p (a + (d + 1))) :=
          mul_lt_mul_of_pos_right (ih hab)
            (div_pos (moment_pos p _) (moment_pos p _))
        _ < _ := mul_lt_mul_of_pos_left hs
          (div_pos (moment_pos p _) (moment_pos p _))

/-- Strict mixed Hankel inequality with completely independent positive gaps. -/
theorem mixed_moment_two_pos (p : Real.Parameters) {a b c d : ℕ}
    (hab : a < b) (hcd : c < d) :
    0 < moment p (a + c) * moment p (b + d) -
      moment p (a + d) * moment p (b + c) := by
  let gap := b - a - 1
  have hg : b = a + (gap + 1) := by dsimp [gap]; omega
  have h := gap_ratio_strictMono p gap (show a + c < a + d by omega)
  rw [show a + c + (gap + 1) = b + c by omega,
    show a + d + (gap + 1) = b + d by omega] at h
  have hc := (div_lt_div_iff₀ (moment_pos p (a + c))
    (moment_pos p (a + d))).mp h
  nlinarith only [hc]

/-- Every ordered second-order mixed minor of the actual manuscript Gram
matrix is strictly positive; neither equal gaps nor common offsets are required. -/
theorem actual_gram_mixed_two_pos (p : Real.Parameters) (hp : Real.Admissible p)
    (rows cols : Fin 2 → Fin p.h) (hrows : StrictMono rows) (hcols : StrictMono cols) :
    0 < ((Real.gram p (Real.zeta p.weight)).submatrix rows cols).det := by
  rw [Matrix.det_fin_two]
  simp only [Matrix.submatrix_apply, gram_eq_moment p hp]
  exact mixed_moment_two_pos p
    (show (rows 0).val < (rows 1).val from hrows (by decide))
    (show (cols 0).val < (cols 1).val from hcols (by decide))

end LeanPaper.ActualMixedTwoMinors

#print axioms LeanPaper.ActualMixedTwoMinors.gap_ratio_strictMono
#print axioms LeanPaper.ActualMixedTwoMinors.actual_gram_mixed_two_pos
