import LeanPaper.ReciprocalLogDerivative

/-!
# The second reciprocal-root power sum is rational

Differentiate the actual first logarithmic-derivative identity on its open
non-root domain. This proves S_2 = (P'^2-P''P)/P^2, including the exact
rational witness at rational shifts. The second derivative of log|P| is -S_2.
No distinctness of roots or noncancellation of pole terms is assumed.
Higher-order moments remain a separate obligation.
-/

noncomputable section
open scoped BigOperators Topology
open Filter Polynomial

namespace LeanPaper.ReciprocalSecondMoment

open LeanPaper.ReciprocalRootMoments
open LeanPaper.ReciprocalLogDerivative

theorem polynomial_logDeriv_hasDerivAt (P : ℚ[X]) (x : ℝ)
    (hx : ManuscriptChain.Real.evalQ P x ≠ 0) :
    HasDerivAt (logDeriv (ManuscriptChain.Real.evalQ P))
      ((ManuscriptChain.Real.evalQ P.derivative.derivative x *
          ManuscriptChain.Real.evalQ P x -
          (ManuscriptChain.Real.evalQ P.derivative x) ^ 2) /
        (ManuscriptChain.Real.evalQ P x) ^ 2) x := by
  have heq : logDeriv (ManuscriptChain.Real.evalQ P) =
      (fun y : ℝ => ManuscriptChain.Real.evalQ P.derivative y /
        ManuscriptChain.Real.evalQ P y) := by
    funext y
    change deriv (fun z : ℝ => (P.map (Rat.castHom ℝ)).eval z) y /
      (P.map (Rat.castHom ℝ)).eval y =
        (P.derivative.map (Rat.castHom ℝ)).eval y / (P.map (Rat.castHom ℝ)).eval y
    rw [Polynomial.deriv, Polynomial.derivative_map]
  rw [heq]
  have hh := ((P.map (Rat.castHom ℝ)).derivative.hasDerivAt x).fun_div
    ((P.map (Rat.castHom ℝ)).hasDerivAt x) hx
  simpa only [ManuscriptChain.Real.evalQ, ManuscriptChain.Real.realPolynomial,
    Polynomial.derivative_map, pow_two] using hh

theorem actual_logDeriv_hasDerivAt
    (p : ManuscriptChain.Real.Parameters)
    (hp : ManuscriptChain.Real.Admissible p) (x : ℝ)
    (hx : ManuscriptChain.Real.evalQ (ManuscriptChain.Real.delta p) x ≠ 0) :
    HasDerivAt (logDeriv (ManuscriptChain.Real.evalQ (ManuscriptChain.Real.delta p)))
      (-reciprocalEvenMoment (manuscriptRoots p hp) x 1) x := by
  have hgap (i : Fin p.h) : x - manuscriptRoots p hp i ≠ 0 := by
    intro heq
    apply hx
    rw [sub_eq_zero.mp heq]
    exact manuscriptRoots_eval p hp i
  have hterm (i : Fin p.h) :
      HasDerivAt (fun y : ℝ => (y - manuscriptRoots p hp i)⁻¹)
        (-reciprocalAtom (manuscriptRoots p hp) x i) x := by
    have hd : HasDerivAt (fun y : ℝ => y - manuscriptRoots p hp i) 1 x := by
      simpa only [hasDerivAt_sub_const_iff] using (hasDerivAt_id' x)
    have hh := hd.fun_inv (hgap i)
    have heq : manuscriptRoots p hp i - x = -(x - manuscriptRoots p hp i) := by ring
    simpa only [reciprocalAtom, heq, inv_neg, neg_sq, neg_div,
      one_div, inv_pow] using hh
  have hsum : HasDerivAt (fun y : ℝ => ∑ i, (y - manuscriptRoots p hp i)⁻¹)
      (-reciprocalEvenMoment (manuscriptRoots p hp) x 1) x := by
    simpa only [Finset.sum_neg_distrib, reciprocalEvenMoment, pow_one] using
      (HasDerivAt.fun_sum (u := Finset.univ) (fun i _ => hterm i))
  apply hsum.congr_of_eventuallyEq
  have hevent := ((ManuscriptChain.Real.realPolynomial
    (ManuscriptChain.Real.delta p)).continuousAt).eventually_ne hx
  filter_upwards [hevent] with y hy
  exact actual_logDeriv p hp y hy

/-- The genuine second derivative of the real logarithm has the negative
sign dictated by the reciprocal even power sum. -/
theorem actual_log_second_hasDerivAt
    (p : ManuscriptChain.Real.Parameters)
    (hp : ManuscriptChain.Real.Admissible p) (x : ℝ)
    (hx : ManuscriptChain.Real.evalQ (ManuscriptChain.Real.delta p) x ≠ 0) :
    HasDerivAt
      (deriv (fun y : ℝ => Real.log
        (ManuscriptChain.Real.evalQ (ManuscriptChain.Real.delta p) y)))
      (-reciprocalEvenMoment (manuscriptRoots p hp) x 1) x := by
  apply (actual_logDeriv_hasDerivAt p hp x hx).congr_of_eventuallyEq
  have hevent := ((ManuscriptChain.Real.realPolynomial
    (ManuscriptChain.Real.delta p)).continuousAt).eventually_ne hx
  filter_upwards [hevent] with y hy
  exact (ReciprocalLogDerivative.actual_log_hasDerivAt p hp y hy).deriv.trans
    (actual_logDeriv p hp y hy).symm

/-- The first even reciprocal-root moment has the exact polynomial quotient
formula required for rationality. -/
theorem actual_second_moment_formula
    (p : ManuscriptChain.Real.Parameters)
    (hp : ManuscriptChain.Real.Admissible p) (x : ℝ)
    (hx : ManuscriptChain.Real.evalQ (ManuscriptChain.Real.delta p) x ≠ 0) :
    reciprocalEvenMoment (manuscriptRoots p hp) x 1 =
      ((ManuscriptChain.Real.evalQ (ManuscriptChain.Real.delta p).derivative x) ^ 2 -
        ManuscriptChain.Real.evalQ (ManuscriptChain.Real.delta p).derivative.derivative x *
          ManuscriptChain.Real.evalQ (ManuscriptChain.Real.delta p) x) /
        (ManuscriptChain.Real.evalQ (ManuscriptChain.Real.delta p) x) ^ 2 := by
  have heq := (actual_logDeriv_hasDerivAt p hp x hx).unique
    (polynomial_logDeriv_hasDerivAt (ManuscriptChain.Real.delta p) x hx)
  have hh := congrArg Neg.neg heq
  simp only [neg_neg] at hh
  calc
    _ = _ := hh
    _ = _ := by ring

theorem actual_second_moment_rational
    (p : ManuscriptChain.Real.Parameters)
    (hp : ManuscriptChain.Real.Admissible p) (q : ℚ)
    (hq : ManuscriptChain.Real.evalQ (ManuscriptChain.Real.delta p) (q : ℝ) ≠ 0) :
    reciprocalEvenMoment (manuscriptRoots p hp) (q : ℝ) 1 =
      ((((ManuscriptChain.Real.delta p).derivative.eval q) ^ 2 -
        (ManuscriptChain.Real.delta p).derivative.derivative.eval q *
          (ManuscriptChain.Real.delta p).eval q) /
        ((ManuscriptChain.Real.delta p).eval q) ^ 2 : ℚ) := by
  rw [actual_second_moment_formula p hp (q : ℝ) hq]
  simp only [evalQ_at_rat, Rat.cast_div, Rat.cast_sub, Rat.cast_pow, Rat.cast_mul]

end LeanPaper.ReciprocalSecondMoment

#print axioms LeanPaper.ReciprocalSecondMoment.actual_second_moment_formula
#print axioms LeanPaper.ReciprocalSecondMoment.actual_second_moment_rational
