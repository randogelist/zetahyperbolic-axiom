import LeanPaper.ReciprocalRootMoments
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# First logarithmic derivative and its exact rational witness

The actual constructed determinant factorization gives P'/P = sum 1/(x-r).
Consequently the manuscript's opposite-gap convention sum 1/(r-x) has a
minus sign. At a rational non-root shift its witness is the rational number
-P'(q)/P(q). No spectral or Gram certificate is passed by the caller.

Higher logarithmic derivatives and rationality of every higher power sum are
separate assertions; this module establishes the first order exactly.
-/

noncomputable section
open scoped BigOperators
open Polynomial

namespace LeanPaper.ReciprocalLogDerivative

open ManuscriptChain.Spectral
open LeanPaper.ReciprocalRootMoments

theorem factorization_logDeriv {n : ℕ} {p : SymmetricAffinePencil n}
    (c : RootFactorization p) (x : ℝ) (hx : p.detPolynomial.eval x ≠ 0) :
    logDeriv (fun t : ℝ => p.detPolynomial.eval t) x =
      ∑ i, (x - c.root i)⁻¹ := by
  have hroot (i : Fin n) : x ≠ c.root i := by
    intro heq
    apply hx
    rw [heq]
    exact c.eval_root i
  have hfac (i : Fin n) : 1 + (x - p.center) * c.beta i ≠ 0 := by
    intro hi
    exact hroot i ((linear_factor_eq_zero_iff p.center (c.beta i) x
      (c.beta_ne_zero i)).mp hi)
  have hd (i : Fin n) :
      HasDerivAt (fun t : ℝ => 1 + (t - p.center) * c.beta i) (c.beta i) x := by
    simpa [spectralFactor] using (spectralFactor p.center (c.beta i)).hasDerivAt x
  have heq : (fun t : ℝ => p.detPolynomial.eval t) =
      (fun t : ℝ => Matrix.det p.base * ∏ i, (1 + (t - p.center) * c.beta i)) := by
    funext t
    exact c.eval_eq t
  rw [heq, logDeriv_const_mul x _ c.base_det_ne_zero,
    logDeriv_prod (fun i _ => hfac i) (fun i _ => (hd i).differentiableAt)]
  apply Finset.sum_congr rfl
  intro i _
  rw [logDeriv_apply, (hd i).deriv]
  have hlinear : 1 + (x - p.center) * c.beta i = (x - c.root i) * c.beta i := by
    dsimp only [RootFactorization.root]
    field_simp [c.beta_ne_zero i]
    ring
  rw [hlinear]
  field_simp [c.beta_ne_zero i, sub_ne_zero.mpr (hroot i)]

theorem actual_logDeriv
    (p : ManuscriptChain.Real.Parameters)
    (hp : ManuscriptChain.Real.Admissible p) (x : ℝ)
    (hx : ManuscriptChain.Real.evalQ (ManuscriptChain.Real.delta p) x ≠ 0) :
    logDeriv (ManuscriptChain.Real.evalQ (ManuscriptChain.Real.delta p)) x =
      ∑ i, (x - manuscriptRoots p hp i)⁻¹ := by
  have hc := factorization_logDeriv
    (ManuscriptChain.General.factorization p (ManuscriptChain.GRAM_POSITIVE p hp)) x
    (by simpa only [ManuscriptChain.Real.manuscriptPencil_detPolynomial,
      ManuscriptChain.Real.evalQ] using hx)
  change logDeriv (fun t : ℝ =>
    (ManuscriptChain.Real.realPolynomial (ManuscriptChain.Real.delta p)).eval t) x = _
  simpa only [ManuscriptChain.Real.manuscriptPencil_detPolynomial,
    manuscriptRoots] using hc

/-- This sign is the correction required by the printed r-x convention. -/
theorem actual_opposite_gap_sum
    (p : ManuscriptChain.Real.Parameters)
    (hp : ManuscriptChain.Real.Admissible p) (x : ℝ)
    (hx : ManuscriptChain.Real.evalQ (ManuscriptChain.Real.delta p) x ≠ 0) :
    (∑ i, (manuscriptRoots p hp i - x)⁻¹) =
      -logDeriv (ManuscriptChain.Real.evalQ (ManuscriptChain.Real.delta p)) x := by
  rw [actual_logDeriv p hp x hx, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [show manuscriptRoots p hp i - x = -(x - manuscriptRoots p hp i) by ring,
    inv_neg]

theorem evalQ_at_rat (P : ℚ[X]) (q : ℚ) :
    ManuscriptChain.Real.evalQ P (q : ℝ) = ((P.eval q : ℚ) : ℝ) := by
  exact Polynomial.eval_map_apply (p := P) (Rat.castHom ℝ) q

theorem rational_logDeriv (P : ℚ[X]) (q : ℚ) :
    logDeriv (ManuscriptChain.Real.evalQ P) (q : ℝ) =
      ((P.derivative.eval q / P.eval q : ℚ) : ℝ) := by
  rw [logDeriv_apply]
  change deriv (fun x : ℝ => (P.map (Rat.castHom ℝ)).eval x) (q : ℝ) /
    ManuscriptChain.Real.evalQ P (q : ℝ) = _
  rw [Polynomial.deriv, Polynomial.derivative_map]
  rw [show (P.derivative.map (Rat.castHom ℝ)).eval (q : ℝ) =
      ((P.derivative.eval q : ℚ) : ℝ) from evalQ_at_rat P.derivative q,
    evalQ_at_rat P q]
  norm_cast

/-- The rational witness is computed from the actual rational polynomial. -/
theorem actual_first_inverse_gap_sum_rational
    (p : ManuscriptChain.Real.Parameters)
    (hp : ManuscriptChain.Real.Admissible p) (q : ℚ)
    (hq : ManuscriptChain.Real.evalQ (ManuscriptChain.Real.delta p) (q : ℝ) ≠ 0) :
    (∑ i, (manuscriptRoots p hp i - (q : ℝ))⁻¹) =
      ((-(ManuscriptChain.Real.delta p).derivative.eval q /
        (ManuscriptChain.Real.delta p).eval q : ℚ) : ℝ) := by
  rw [actual_opposite_gap_sum p hp (q : ℝ) hq,
    rational_logDeriv (ManuscriptChain.Real.delta p) q]
  push_cast
  ring

/-- The real logarithm here is log of the absolute value in Mathlib's real
log convention. Its derivative is valid on either sign component of P. -/
theorem actual_log_hasDerivAt
    (p : ManuscriptChain.Real.Parameters)
    (hp : ManuscriptChain.Real.Admissible p) (x : ℝ)
    (hx : ManuscriptChain.Real.evalQ (ManuscriptChain.Real.delta p) x ≠ 0) :
    HasDerivAt (fun t : ℝ =>
      Real.log (ManuscriptChain.Real.evalQ (ManuscriptChain.Real.delta p) t))
      (∑ i, (x - manuscriptRoots p hp i)⁻¹) x := by
  rw [← actual_logDeriv p hp x hx, logDeriv_apply]
  change HasDerivAt (fun t : ℝ => Real.log
    ((ManuscriptChain.Real.realPolynomial (ManuscriptChain.Real.delta p)).eval t))
    (deriv (fun t : ℝ =>
      (ManuscriptChain.Real.realPolynomial (ManuscriptChain.Real.delta p)).eval t) x /
      (ManuscriptChain.Real.realPolynomial (ManuscriptChain.Real.delta p)).eval x) x
  rw [Polynomial.deriv]
  exact ((ManuscriptChain.Real.realPolynomial
    (ManuscriptChain.Real.delta p)).hasDerivAt x).log hx

end LeanPaper.ReciprocalLogDerivative

#print axioms LeanPaper.ReciprocalLogDerivative.actual_first_inverse_gap_sum_rational
#print axioms LeanPaper.ReciprocalLogDerivative.actual_log_hasDerivAt
