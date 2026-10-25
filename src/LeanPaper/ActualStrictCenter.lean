import LeanPaper.StrictCenteredLaguerre
import LeanPaper.SlopeIndefinite

/-!
# The strict degree-normalized center bound in Theorem 3.7(1)

The actual alternating pole signs give two different spectral factors.
The reciprocal-root dispersion identity then makes the normalized Laguerre
bound strict. The primitive integer normalization is explicitly transported.
-/

noncomputable section
open Polynomial

namespace LeanPaper.ActualStrictCenter

open ManuscriptChain
open LeanPaper.NormalizedNewton LeanPaper.HigherDerivativeTuran
open LeanPaper.ReciprocalRootMoments LeanPaper.StrictCenteredLaguerre

theorem actual_distinct_roots (p : Real.Parameters) (hp : Real.Admissible p)
    (hh : 2 ≤ p.h) : ∃ i j, manuscriptRoots p hp i ≠ manuscriptRoots p hp j := by
  obtain ⟨i, j, hij⟩ := SlopeIndefinite.actual_factorization_not_constant p hp hh
  refine ⟨i, j, ?_⟩
  intro heq
  apply hij
  have hi : (General.factorization p (GRAM_POSITIVE p hp)).beta i ≠ 0 :=
    (General.factorization p (GRAM_POSITIVE p hp)).beta_ne_zero i
  have hj : (General.factorization p (GRAM_POSITIVE p hp)).beta j ≠ 0 :=
    (General.factorization p (GRAM_POSITIVE p hp)).beta_ne_zero j
  simp only [manuscriptRoots, Spectral.RootFactorization.root] at heq
  have hinv :
      ((General.factorization p (GRAM_POSITIVE p hp)).beta i)⁻¹ =
      ((General.factorization p (GRAM_POSITIVE p hp)).beta j)⁻¹ := by
    simpa only [one_div] using (sub_right_inj.mp heq)
  exact inv_injective hinv

theorem actual_primitive_laguerre_strict_offroots
    (p : Real.Parameters) (hp : Real.Admissible p) (hh : 2 ≤ p.h)
    (x : ℝ) (hx : (primitiveRealPolynomial p).eval x ≠ 0) :
    0 < laguerre p.h (primitiveRealPolynomial p) x := by
  obtain ⟨i, j, hij⟩ := actual_distinct_roots p hp hh
  have hdelta : Real.evalQ (Real.delta p) x ≠ 0 := by
    rw [primitiveRealPolynomial_identity, Polynomial.eval_mul, Polynomial.eval_C] at hx
    exact (mul_ne_zero_iff.mp hx).2
  have hlag := actual_laguerre_strict_of_distinct_roots p hp x hdelta i j hij
  have hscale : (0 : ℝ) < (GeneralIrrationality.normalization p).scale := by
    exact_mod_cast (GeneralIrrationality.normalization p).scale_pos
  rw [primitiveRealPolynomial_identity]
  have heq : laguerre p.h
      (C ((GeneralIrrationality.normalization p).scale : ℝ) *
        Real.realPolynomial (Real.delta p)) x =
      ((GeneralIrrationality.normalization p).scale : ℝ) ^ 2 *
        laguerre p.h (Real.realPolynomial (Real.delta p)) x := by
    simp only [laguerre, Polynomial.derivative_C_mul, Polynomial.eval_mul,
      Polynomial.eval_C]
    ring
  rw [heq]
  exact mul_pos (sq_pos_of_pos hscale) hlag

theorem strict_divided_bound (n : ℕ) (P : ℝ[X]) (x : ℝ)
    (hn : 0 < n) (hx : P.eval x ≠ 0) (h : 0 < laguerre n P x) :
    P.derivative.derivative.eval x / P.eval x <
      (1 - 1 / (n : ℝ)) * (P.derivative.eval x / P.eval x) ^ 2 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hid :
      (1 - 1 / (n : ℝ)) * (P.derivative.eval x / P.eval x) ^ 2 -
        P.derivative.derivative.eval x / P.eval x =
      laguerre n P x / ((n : ℝ) * (P.eval x)^2) := by
    unfold laguerre
    field_simp [hx, ne_of_gt hnR]
    <;> ring
  have hpos := div_pos h (mul_pos hnR (sq_pos_of_ne_zero hx))
  rw [← hid] at hpos
  linarith

/-- Literal strict logarithmic second-derivative inequality at true zeta. -/
theorem theorem_3_7_strict_center
    (p : Real.Parameters) (hp : Real.Admissible p) (hh : 2 ≤ p.h) :
    (primitiveRealPolynomial p).derivative.derivative.eval (Real.zeta p.weight) /
        (primitiveRealPolynomial p).eval (Real.zeta p.weight) <
      (1 - 1 / (p.h : ℝ)) *
        ((primitiveRealPolynomial p).derivative.eval (Real.zeta p.weight) /
          (primitiveRealPolynomial p).eval (Real.zeta p.weight)) ^ 2 := by
  have hx : (primitiveRealPolynomial p).eval (Real.zeta p.weight) ≠ 0 :=
    ne_of_gt (GeneralIrrationality.primitivePolynomial_eval_pos p hp)
  exact strict_divided_bound p.h _ _ (by omega) hx
    (actual_primitive_laguerre_strict_offroots p hp hh _ hx)

end LeanPaper.ActualStrictCenter

#print axioms LeanPaper.ActualStrictCenter.theorem_3_7_strict_center
