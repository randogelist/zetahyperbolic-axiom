import LeanPaper.ReciprocalLogDerivative
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# Constructed rational witnesses for every logarithmic derivative

A pair of rational polynomials represents a rational function. Quotient-rule
differentiation constructs the next pair, without normalization or a supplied
derivative certificate. Starting at P'/P produces all iterated logarithmic
derivatives on the nonzero locus of P. At a rational point every pair evaluates
to an explicit rational number.
-/

noncomputable section
open scoped Topology
open Filter Polynomial

namespace LeanPaper.RationalLogJets

open ManuscriptChain
open LeanPaper.ReciprocalLogDerivative

def jetStep (J : ℚ[X] × ℚ[X]) : ℚ[X] × ℚ[X] :=
  (J.1.derivative * J.2 - J.1 * J.2.derivative, J.2 ^ 2)

def logJet (P : ℚ[X]) : ℕ → ℚ[X] × ℚ[X]
  | 0 => (P.derivative, P)
  | n + 1 => jetStep (logJet P n)

def jetValue (J : ℚ[X] × ℚ[X]) (x : ℝ) : ℝ :=
  Real.evalQ J.1 x / Real.evalQ J.2 x

def rationalJetValue (J : ℚ[X] × ℚ[X]) (q : ℚ) : ℚ :=
  J.1.eval q / J.2.eval q

theorem evalQ_hasDerivAt (P : ℚ[X]) (x : ℝ) :
    HasDerivAt (Real.evalQ P) (Real.evalQ P.derivative x) x := by
  change HasDerivAt (fun y : ℝ => (P.map (Rat.castHom ℝ)).eval y)
    ((P.derivative.map (Rat.castHom ℝ)).eval x) x
  simpa only [Polynomial.derivative_map] using (P.map (Rat.castHom ℝ)).hasDerivAt x

theorem jetStep_hasDerivAt (J : ℚ[X] × ℚ[X]) (x : ℝ)
    (hx : Real.evalQ J.2 x ≠ 0) :
    HasDerivAt (jetValue J) (jetValue (jetStep J) x) x := by
  change HasDerivAt (fun y : ℝ => Real.evalQ J.1 y / Real.evalQ J.2 y) _ x
  have hh := (evalQ_hasDerivAt J.1 x).fun_div (evalQ_hasDerivAt J.2 x) hx
  simpa only [jetValue, jetStep, Real.evalQ, Real.realPolynomial,
    Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_pow,
    Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_pow] using hh

theorem logJet_denominator_ne_zero (P : ℚ[X]) (n : ℕ) (x : ℝ)
    (hx : Real.evalQ P x ≠ 0) : Real.evalQ (logJet P n).2 x ≠ 0 := by
  induction n with
  | zero => exact hx
  | succ n ih =>
      simpa only [logJet, jetStep, Real.evalQ, Real.realPolynomial,
        Polynomial.map_pow, Polynomial.eval_pow] using pow_ne_zero 2 ih

theorem logJet_zero_eq (P : ℚ[X]) :
    jetValue (logJet P 0) = logDeriv (Real.evalQ P) := by
  funext x
  change Real.evalQ P.derivative x / Real.evalQ P x =
    deriv (Real.evalQ P) x / Real.evalQ P x
  rw [(evalQ_hasDerivAt P x).deriv]

/-- Every iterated logarithmic derivative is the value of the recursively
constructed rational pair. The sole domain hypothesis is P(x) != 0. -/
theorem iterated_logDeriv_eq_jet (P : ℚ[X]) (n : ℕ) (x : ℝ)
    (hx : Real.evalQ P x ≠ 0) :
    iteratedDeriv n (logDeriv (Real.evalQ P)) x = jetValue (logJet P n) x := by
  induction n generalizing x with
  | zero => simp only [iteratedDeriv_zero, logJet_zero_eq]
  | succ n ih =>
      rw [iteratedDeriv_succ]
      have hh := jetStep_hasDerivAt (logJet P n) x (logJet_denominator_ne_zero P n x hx)
      have heq : iteratedDeriv n (logDeriv (Real.evalQ P)) =ᶠ[𝓝 x]
          jetValue (logJet P n) := by
        have hevent := (evalQ_hasDerivAt P x).continuousAt.eventually_ne hx
        filter_upwards [hevent] with y hy
        exact ih y hy
      exact (hh.congr_of_eventuallyEq heq).deriv

theorem jetValue_at_rat (J : ℚ[X] × ℚ[X]) (q : ℚ) :
    jetValue J (q : ℝ) = (rationalJetValue J q : ℝ) := by
  simp only [jetValue, rationalJetValue, evalQ_at_rat, Rat.cast_div]

theorem iterated_logDeriv_rational (P : ℚ[X]) (n : ℕ) (q : ℚ)
    (hq : Real.evalQ P (q : ℝ) ≠ 0) :
    iteratedDeriv n (logDeriv (Real.evalQ P)) (q : ℝ) =
      (rationalJetValue (logJet P n) q : ℝ) := by
  rw [iterated_logDeriv_eq_jet P n (q : ℝ) hq, jetValue_at_rat]

/-- The jet identity concerns actual iterated derivatives of log|P|, not a
formal sequence merely named logarithmic derivatives. -/
theorem iterated_log_eq_logDeriv (P : ℚ[X]) (n : ℕ) (x : ℝ)
    (hx : Real.evalQ P x ≠ 0) :
    iteratedDeriv (n + 1) (fun y : ℝ => _root_.Real.log (Real.evalQ P y)) x =
      iteratedDeriv n (logDeriv (Real.evalQ P)) x := by
  rw [iteratedDeriv_succ']
  apply Filter.EventuallyEq.iteratedDeriv_eq
  have hevent := (evalQ_hasDerivAt P x).continuousAt.eventually_ne hx
  filter_upwards [hevent] with y hy
  rw [logDeriv_apply, (evalQ_hasDerivAt P y).deriv]
  exact ((evalQ_hasDerivAt P y).log hy).deriv

theorem iterated_log_rational (P : ℚ[X]) (n : ℕ) (q : ℚ)
    (hq : Real.evalQ P (q : ℝ) ≠ 0) :
    iteratedDeriv (n + 1) (fun y : ℝ => _root_.Real.log (Real.evalQ P y)) (q : ℝ) =
      (rationalJetValue (logJet P n) q : ℝ) := by
  rw [iterated_log_eq_logDeriv P n (q : ℝ) hq,
    iterated_logDeriv_rational P n q hq]

end LeanPaper.RationalLogJets

#print axioms LeanPaper.RationalLogJets.iterated_log_rational
