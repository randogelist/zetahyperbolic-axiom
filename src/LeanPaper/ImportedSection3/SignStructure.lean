import LeanPaper.ImportedSection3.RealExponent
import MAIN_CHAIN_ASSEMBLED

/-!
# Theorem 3.3: proved finite signature and determinant components

This file proves the positive Gram determinant for the actual odd-weight
paper matrix; the exact leading coefficient identity; and the statement
that the numbers of positive/negative diagonal pole weights in the continuous
exponent extension are constant as s varies.

It does NOT claim that all non-principal minors are strictly positive,
that the Carleman criterion has been formalized, or that Sylvester's inertia
numbers have been identified with the printed alternating counts.  These
remain outstanding components of Theorem 3.3.
-/

noncomputable section
open scoped BigOperators Classical

namespace PaperAdvances.Theorem3_3

open ManuscriptChain

/-- At all admissible odd weights, the *actual* Gram determinant is positive. -/
theorem actual_gram_det_pos (p : ManuscriptChain.Real.Parameters) (hp : ManuscriptChain.Real.Admissible p) :
    0 < (ManuscriptChain.Real.gram p (ManuscriptChain.Real.zeta p.weight)).det :=
  (ManuscriptChain.GRAM_POSITIVE p hp).det_pos

/-- Exact leading coefficient, as a signed finite pole product, equation (3.4)
in its factored form prior to cancellation of the Vandermonde denominator. -/
theorem leading_coefficient_product (p : ManuscriptChain.Real.Parameters) :
    (ManuscriptChain.Real.delta p).leadingCoeff =
      (PoleDiagonalization.poleVandermonde p).det ^ 2 *
        ∏ a : Fin p.h, PoleDiagonalization.poleWeight p a := by
  rw [PoleDiagonalization.delta_leadingCoeff,
    PoleDiagonalization.rationalDerivativeMatrix_det]

/-- Positive and negative diagonal-coefficient counts are s-independent. -/
theorem positive_pole_index_set (p : ManuscriptChain.Real.Parameters) (s : ℝ) :
    (Finset.univ.filter (fun a : Fin p.h => 0 < Proposition3_2.gamma p s a)) =
      (Finset.univ.filter (fun a : Fin p.h =>
        0 < (PoleDiagonalization.poleWeight p a : ℝ))) := by
  classical
  ext a
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact Proposition3_2.gamma_pos_iff p s a

theorem negative_pole_index_set (p : ManuscriptChain.Real.Parameters) (s : ℝ) :
    (Finset.univ.filter (fun a : Fin p.h => Proposition3_2.gamma p s a < 0)) =
      (Finset.univ.filter (fun a : Fin p.h =>
        (PoleDiagonalization.poleWeight p a : ℝ) < 0)) := by
  classical
  ext a
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact Proposition3_2.gamma_neg_iff p s a

/-- The diagonal inertia counts of the real-s pencil are independent of s. -/
theorem positive_pole_count_constant (p : ManuscriptChain.Real.Parameters) (s t : ℝ) :
    (Finset.univ.filter (fun a : Fin p.h => 0 < Proposition3_2.gamma p s a)).card =
      (Finset.univ.filter (fun a : Fin p.h => 0 < Proposition3_2.gamma p t a)).card := by
  simp only [positive_pole_index_set]

theorem negative_pole_count_constant (p : ManuscriptChain.Real.Parameters) (s t : ℝ) :
    (Finset.univ.filter (fun a : Fin p.h => Proposition3_2.gamma p s a < 0)).card =
      (Finset.univ.filter (fun a : Fin p.h => Proposition3_2.gamma p t a < 0)).card := by
  simp only [negative_pole_index_set]

/-- Arithmetic identity used in the printed weight-five leading sign parity.
This identity alone does NOT prove the pole product sign. -/
theorem weight_five_parity_correction (n : ℤ) :
    (1539 * n * n - 27 * n) - (n * n - n) =
      2 * (756 * n * n + 13 * n * (n - 1)) := by
  ring

end PaperAdvances.Theorem3_3

#print axioms PaperAdvances.Theorem3_3.actual_gram_det_pos
#print axioms PaperAdvances.Theorem3_3.leading_coefficient_product
#print axioms PaperAdvances.Theorem3_3.positive_pole_count_constant
