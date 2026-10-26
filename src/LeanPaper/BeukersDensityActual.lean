import LeanPaper.BeukersOffDiagonalActual

/-!
# Theorem 5.1: positivity of the printed Beukers density

The density is strictly positive at every point of the open unit square,
rather than merely a formal integral kernel. The moment identities are
theorems in BeukersOffDiagonal.lean over this very same density.
-/

noncomputable section
open MeasureTheory Set

namespace ManuscriptChain.Beukers

theorem density_strictly_positive_on_square (z : ℝ × ℝ)
    (hz : z ∈ square) : 0 < density z := by
  have hxy0 : 0 < z.1 * z.2 := mul_pos hz.1.1 hz.2.1
  have hxy1 : z.1 * z.2 < 1 := by
    have hh := mul_lt_mul_of_pos_right hz.1.2 hz.2.1
    nlinarith [hz.2.2]
  have hlog : 0 < -Real.log (z.1 * z.2) :=
    neg_pos.mpr (Real.log_neg hxy0 hxy1)
  unfold density
  exact div_pos (pow_pos hlog _)
    (mul_pos (by norm_num) (sub_pos.mpr hxy1))

theorem density_measurable : Measurable density := by
  unfold density
  fun_prop

end ManuscriptChain.Beukers
