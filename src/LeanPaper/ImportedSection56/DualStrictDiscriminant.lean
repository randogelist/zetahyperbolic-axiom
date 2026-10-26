import LeanPaper.ImportedSection56.DualDiscriminant

/-!
# Theorem 5.2: strict spectral separation in a 2x2 dual pencil

The existing sum-of-squares discriminant certificate becomes STRICT when
the off-diagonal coefficient b*u-a*v is nonzero. This gives a usable
finite sufficient condition for simple, distinct real generalized roots.
-/

noncomputable section
namespace PaperOrder.CoreAlgebra

/-- A generic nonproportionality certificate forces a strictly
positive discriminant, strengthening universal nonnegativity. -/
theorem dualTwoByTwo_discriminant_pos_of_nonproportional
    (a b c u v w : ℝ) (hu : 0 < u)
    (hM : 0 < u * w - v ^ 2)
    (hsep : b * u - a * v ≠ 0) :
    0 < dualTwoByTwoDiscriminant a b c u v w := by
  have hleft : 0 ≤ (a * (u * w - v ^ 2) - c * u ^ 2 +
      2 * b * u * v - a * v ^ 2) ^ 2 := sq_nonneg _
  have hright : 0 < (4 : ℝ) * (u * w - v ^ 2) * (b * u - a * v) ^ 2 := by
    exact mul_pos (mul_pos (by norm_num) hM)
      (sq_pos_of_ne_zero hsep)
  have hmul : 0 < u ^ 2 * dualTwoByTwoDiscriminant a b c u v w := by
    rw [dualTwoByTwo_discriminant_sos]
    exact add_pos_of_nonneg_of_pos hleft hright
  have hu2 : 0 < u ^ 2 := sq_pos_of_ne_zero (ne_of_gt hu)
  by_contra hnot
  have hle : dualTwoByTwoDiscriminant a b c u v w ≤ 0 :=
    le_of_not_gt hnot
  have hbad : u ^ 2 * dualTwoByTwoDiscriminant a b c u v w ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (le_of_lt hu2) hle
  exact (not_le_of_gt hmul) hbad

end PaperOrder.CoreAlgebra

#print axioms PaperOrder.CoreAlgebra.dualTwoByTwo_discriminant_pos_of_nonproportional
