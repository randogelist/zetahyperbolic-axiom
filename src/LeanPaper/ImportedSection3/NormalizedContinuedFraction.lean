import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic


/-!
# Corollary 3.5: corrected 2x2 normalized Schur / J-fraction identity

For a normalized affine spectral pencil I+tB, B=[[a,b],[b,c]],
the determinant is (1+ta)(1+tc)-t²b². The Schur complement contains
1+tc and t²b²/(1+ta), not the unscaled denominators printed in (3.6).
The general Jacobi/Lanczos correspondence is NOT claimed here.
-/

namespace LeanPaper.Section3ContinuedFractions

/-- Exact determinant of the 2x2 normalized symmetric affine pencil. -/
def normalizedTwoDet (a b c t : ℝ) : ℝ :=
  (1+t*a)*(1+t*c) - (t*b)^2

theorem corollary_3_5_normalized_two_det (a b c t : ℝ) :
    (Matrix.det
      (![![1+t*a, t*b],![t*b,1+t*c]] : Matrix (Fin 2) (Fin 2) ℝ)) =
        normalizedTwoDet a b c t := by
  have hmatrix :
      (![![1+t*a, t*b], ![t*b, 1+t*c]] : Matrix (Fin 2) (Fin 2) ℝ) =
        !![1+t*a, t*b; t*b, 1+t*c] := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [hmatrix]
  simpa only [normalizedTwoDet, pow_two] using
    (Matrix.det_fin_two_of (1+t*a) (t*b) (t*b) (1+t*c))

/-- Two-level J-fraction denominator, with the essential normalization. -/
theorem corollary_3_5_two_level_schur_identity
    (a b c t : ℝ) (h : 1+t*a ≠ 0) :
    (1+t*a) * (1+t*c - (t*b)^2/(1+t*a)) =
      normalizedTwoDet a b c t := by
  unfold normalizedTwoDet
  field_simp [h]

end LeanPaper.Section3ContinuedFractions

#print axioms LeanPaper.Section3ContinuedFractions.corollary_3_5_normalized_two_det
#print axioms LeanPaper.Section3ContinuedFractions.corollary_3_5_two_level_schur_identity


/-!
# Correct normalized 3-level J-fraction identity

The affine spectral pencil is I+tB; hence tridiagonal off-diagonals are
multiplied by t, and Schur complements involve t². These exact formulas
reinforce the corrected 2x2 version of Corollary 3.5.
-/

namespace LeanPaper.Section3ContinuedFractions

/-- Three-level determinant of a tridiagonal normalized affine pencil. -/
def normalizedThreeContinuant (a b c d e t : ℝ) : ℝ :=
  (1+t*a)*((1+t*c)*(1+t*e)-(t*d)^2) - (t*b)^2*(1+t*e)

/-- The recurrence for the three-level continuant. -/
theorem normalized_three_continuant_recurrence (a b c d e t : ℝ) :
    normalizedThreeContinuant a b c d e t =
      (1+t*e)*((1+t*a)*(1+t*c)-(t*b)^2) -
         (t*d)^2*(1+t*a) := by
  unfold normalizedThreeContinuant
  ring

/-- The properly normalized nested three-level Schur complement. -/
theorem normalized_three_schur_identity (a b c d e t : ℝ)
    (h1 : 1+t*a ≠ 0)
    (h2 : 1+t*c - (t*b)^2/(1+t*a) ≠ 0) :
    (1+t*a) * (1+t*c - (t*b)^2/(1+t*a)) *
      (1+t*e - (t*d)^2/(1+t*c - (t*b)^2/(1+t*a))) =
        normalizedThreeContinuant a b c d e t := by
  -- Cancel the two Schur denominators separately.  This avoids forcing
  -- `field_simp` to clear an expanded nested rational expression.
  let aa : ℝ := 1 + t * a
  let bb : ℝ := 1 + t * c
  let cc : ℝ := 1 + t * e
  let pp : ℝ := (t * b) ^ 2
  let qq : ℝ := (t * d) ^ 2
  have haa : aa ≠ 0 := h1
  have hbb : bb - pp / aa ≠ 0 := h2
  have hcancel1 : aa * (pp / aa) = pp := by
    calc
      aa * (pp / aa) = (pp / aa) * aa := mul_comm _ _
      _ = pp := div_mul_cancel₀ pp haa
  have hcancel2 : (bb - pp / aa) * (qq / (bb - pp / aa)) = qq := by
    calc
      (bb - pp / aa) * (qq / (bb - pp / aa)) =
          (qq / (bb - pp / aa)) * (bb - pp / aa) := mul_comm _ _
      _ = qq := div_mul_cancel₀ qq hbb
  change aa * (bb - pp / aa) * (cc - qq / (bb - pp / aa)) =
    aa * (bb * cc - qq) - pp * cc
  calc
    aa * (bb - pp / aa) * (cc - qq / (bb - pp / aa)) =
        aa * ((bb - pp / aa) * cc -
          (bb - pp / aa) * (qq / (bb - pp / aa))) := by ring
    _ = aa * ((bb - pp / aa) * cc - qq) := by rw [hcancel2]
    _ = (aa * bb - pp) * cc - aa * qq := by
      calc
        aa * ((bb - pp / aa) * cc - qq) =
            (aa * (bb - pp / aa)) * cc - aa * qq := by ring
        _ = (aa * bb - pp) * cc - aa * qq := by
          rw [mul_sub, hcancel1]
    _ = aa * (bb * cc - qq) - pp * cc := by ring

end LeanPaper.Section3ContinuedFractions

#print axioms LeanPaper.Section3ContinuedFractions.normalized_three_continuant_recurrence
#print axioms LeanPaper.Section3ContinuedFractions.normalized_three_schur_identity

namespace LeanPaper.Section3ContinuedFractions

/-- The three-level continuant is the determinant of the actual normalized
tridiagonal matrix. This identifies the finite expression without asserting
that the manuscript pencil has already been tridiagonalized. -/
theorem normalized_three_continuant_eq_det (a b c d e t : ℝ) :
    normalizedThreeContinuant a b c d e t =
      (Matrix.det
        (!![1+t*a, t*b, 0; t*b, 1+t*c, t*d; 0, t*d, 1+t*e] :
          Matrix (Fin 3) (Fin 3) ℝ)) := by
  simp [Matrix.det_fin_three, normalizedThreeContinuant]
  ring

end LeanPaper.Section3ContinuedFractions

#print axioms LeanPaper.Section3ContinuedFractions.normalized_three_continuant_eq_det
