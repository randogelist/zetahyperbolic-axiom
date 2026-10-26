import Paper.Theorem_3_4
import Mathlib.Tactic

/-!
# Theorem 3.4 — Dodgson condensation, genuine 3-by-3 case

For a symmetric 3-by-3 matrix with entries
  [a b c; b d e; c e f],
the identity below is the exact Desnanot–Jacobi / Dodgson relation
  det(A)*det([a]) = det([a,b;b,d])*det([a,c;c,f]) - det([a,b;b,e])^2.

The sign inequality is the paper's formula (3.5) for r=3.
These lemmas do not yet establish the arbitrary-r determinant identity
or the generalized-eigenvalue interlacing assertion.
-/

noncomputable section

namespace PaperAdvances.Theorem3_4

/-- Exact Dodgson condensation for every symmetric 3-by-3 real matrix. -/
theorem symmetric_3x3_dodgson (a b c d e f : ℝ) :
    a * (a*d*f + 2*b*c*e - a*e^2 - d*c^2 - f*b^2) =
      (a*d - b^2) * (a*f - c^2) - (a*e - b*c)^2 := by
  ring

/-- At a zero of the 2-by-2 leading principal minor,
    the 3-by-3 Dodgson product is nonpositive. -/
theorem symmetric_3x3_sign_at_minor_zero (a b c d e f : ℝ)
    (hz : a*d - b^2 = 0) :
    a * (a*d*f + 2*b*c*e - a*e^2 - d*c^2 - f*b^2) ≤ 0 := by
  rw [symmetric_3x3_dodgson, hz]
  nlinarith [sq_nonneg (a*e - b*c)]

end PaperAdvances.Theorem3_4

#print axioms PaperAdvances.Theorem3_4.symmetric_3x3_dodgson
#print axioms PaperAdvances.Theorem3_4.symmetric_3x3_sign_at_minor_zero
