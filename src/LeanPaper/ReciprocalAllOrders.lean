import LeanPaper.RationalLogJets
import MAIN_CHAIN_IRRATIONALITY

/-!
# Corrected all-order reciprocal-root identities (Corollary 3.6)

For the manuscript convention S_m(x) = sum (r_j-x)^(-m), the m-th
logarithmic derivative is -(m-1)! S_m(x), with a constant minus sign.
The roots are the actual constructed roots, counted with multiplicity.
Rational witnesses are constructed by polynomial quotient differentiation.
The same identities hold for the actual primitive integer normalization.
This does not assert the false all-order strict Hankel positivity.
-/

noncomputable section
open scoped BigOperators Topology
open Filter Polynomial

namespace LeanPaper.ReciprocalAllOrders

open ManuscriptChain
open LeanPaper.ReciprocalRootMoments LeanPaper.ReciprocalLogDerivative
open LeanPaper.RationalLogJets

def inverseGapSum {h : ℕ} (r : Fin h → ℝ) (m : ℕ) (x : ℝ) : ℝ :=
  ∑ i, ((r i - x)⁻¹) ^ m

theorem inverseGapSum_hasDerivAt {h : ℕ} (r : Fin h → ℝ) (n : ℕ) (x : ℝ)
    (hx : ∀ i, r i - x ≠ 0) :
    HasDerivAt (inverseGapSum r (n + 1))
      ((n + 1 : ℕ) * inverseGapSum r (n + 2) x) x := by
  have ht (i : Fin h) :
      HasDerivAt (fun y : ℝ => ((r i - y)⁻¹) ^ (n + 1))
        ((n + 1 : ℕ) * ((r i - x)⁻¹) ^ (n + 2)) x := by
    have hd : HasDerivAt (fun y : ℝ => r i - y) (-1) x :=
      (hasDerivAt_id x).const_sub (r i)
    apply ((hd.fun_inv (hx i)).pow (n + 1)).congr_deriv
    simp only [Nat.add_sub_cancel, neg_neg, one_div, ← inv_pow, pow_add]
    ring
  change HasDerivAt (fun y : ℝ => ∑ i, ((r i - y)⁻¹) ^ (n + 1)) _ x
  simpa only [inverseGapSum, Finset.mul_sum] using
    HasDerivAt.fun_sum (u := Finset.univ) (fun i _ => ht i)

theorem actual_iterated_logDeriv
    (p : Real.Parameters) (hp : Real.Admissible p) (n : ℕ) (x : ℝ)
    (hx : Real.evalQ (Real.delta p) x ≠ 0) :
    iteratedDeriv n (logDeriv (Real.evalQ (Real.delta p))) x =
      -(n.factorial : ℝ) * inverseGapSum (manuscriptRoots p hp) (n + 1) x := by
  induction n generalizing x with
  | zero =>
      simp only [iteratedDeriv_zero, Nat.factorial_zero, Nat.cast_one, neg_mul,
        one_mul, inverseGapSum, zero_add, pow_one]
      exact (neg_eq_iff_eq_neg.mpr (actual_opposite_gap_sum p hp x hx)).symm
  | succ n ih =>
      rw [iteratedDeriv_succ]
      have hgap (i : Fin p.h) : manuscriptRoots p hp i - x ≠ 0 := by
        intro hi
        apply hx
        rw [← sub_eq_zero.mp hi]
        exact manuscriptRoots_eval p hp i
      have hd := (inverseGapSum_hasDerivAt (manuscriptRoots p hp) n x hgap).const_mul
        (-(n.factorial : ℝ))
      have heq : iteratedDeriv n (logDeriv (Real.evalQ (Real.delta p))) =ᶠ[𝓝 x]
          (fun y => -(n.factorial : ℝ) * inverseGapSum (manuscriptRoots p hp) (n + 1) y) := by
        have hevent := (evalQ_hasDerivAt (Real.delta p) x).continuousAt.eventually_ne hx
        filter_upwards [hevent] with y hy
        exact ih y hy
      convert (hd.congr_of_eventuallyEq heq).deriv using 1
      simp only [Nat.factorial_succ, Nat.cast_mul]
      ring

/-- Actual derivatives of log|delta|; the sign is negative at every order. -/
theorem actual_iterated_log
    (p : Real.Parameters) (hp : Real.Admissible p) (n : ℕ) (x : ℝ)
    (hx : Real.evalQ (Real.delta p) x ≠ 0) :
    iteratedDeriv (n + 1) (fun y : ℝ => _root_.Real.log (Real.evalQ (Real.delta p) y)) x =
      -(n.factorial : ℝ) * inverseGapSum (manuscriptRoots p hp) (n + 1) x := by
  rw [iterated_log_eq_logDeriv (Real.delta p) n x hx,
    actual_iterated_logDeriv p hp n x hx]

def rationalMoment (P : ℚ[X]) (n : ℕ) (q : ℚ) : ℚ :=
  -rationalJetValue (logJet P n) q / (n.factorial : ℚ)

/-- Explicit rational witness for every positive-order reciprocal-root sum. -/
theorem actual_inverseGapSum_rational
    (p : Real.Parameters) (hp : Real.Admissible p) (n : ℕ) (q : ℚ)
    (hq : Real.evalQ (Real.delta p) (q : ℝ) ≠ 0) :
    inverseGapSum (manuscriptRoots p hp) (n + 1) (q : ℝ) =
      (rationalMoment (Real.delta p) n q : ℝ) := by
  have hh := actual_iterated_logDeriv p hp n (q : ℝ) hq
  rw [iterated_logDeriv_rational (Real.delta p) n q hq] at hh
  have hf : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  simp only [rationalMoment, Rat.cast_div, Rat.cast_neg, Rat.cast_natCast]
  apply (eq_div_iff hf).mpr
  nlinarith [hh]

/-- The positive even Stieltjes moments have explicit rational witnesses,
including arbitrary orders rather than only the first two powers. -/
theorem actual_even_moment_rational
    (p : Real.Parameters) (hp : Real.Admissible p) (m : ℕ) (q : ℚ)
    (hq : Real.evalQ (Real.delta p) (q : ℝ) ≠ 0) :
    reciprocalEvenMoment (manuscriptRoots p hp) (q : ℝ) (m + 1) =
      (rationalMoment (Real.delta p) (2 * m + 1) q : ℝ) := by
  rw [reciprocalEvenMoment_eq_powerSum]
  have heq : 2 * (m + 1) = (2 * m + 1) + 1 := by omega
  simpa only [inverseGapSum, heq] using
    actual_inverseGapSum_rational p hp (2 * m + 1) q hq

theorem actual_even_moment_exists_rational
    (p : Real.Parameters) (hp : Real.Admissible p) (m : ℕ) (q : ℚ)
    (hq : Real.evalQ (Real.delta p) (q : ℝ) ≠ 0) :
    ∃ a : ℚ, reciprocalEvenMoment (manuscriptRoots p hp) (q : ℝ) m = (a : ℝ) := by
  cases m with
  | zero => exact ⟨p.h, by simp⟩
  | succ m => exact ⟨rationalMoment (Real.delta p) (2 * m + 1) q,
      actual_even_moment_rational p hp m q hq⟩

/-- Positive primitive normalization has exactly the same logarithmic derivative. -/
theorem primitive_logDeriv_eq (p : Real.Parameters) :
    logDeriv (RealTransfer.evalReal (GeneralIrrationality.primitivePolynomial p)) =
      logDeriv (Real.evalQ (Real.delta p)) := by
  have heq : RealTransfer.evalReal (GeneralIrrationality.primitivePolynomial p) =
      (fun x : ℝ => ((GeneralIrrationality.normalization p).scale : ℝ) *
        Real.evalQ (Real.delta p) x) :=
    funext (GeneralIrrationality.primitivePolynomial_eval p)
  have hs : ((GeneralIrrationality.normalization p).scale : ℝ) ≠ 0 := by
    exact_mod_cast ne_of_gt (GeneralIrrationality.normalization p).scale_pos
  funext x
  rw [heq, logDeriv_const_mul x _ hs]

theorem primitive_iterated_logDeriv
    (p : Real.Parameters) (hp : Real.Admissible p) (n : ℕ) (x : ℝ)
    (hx : RealTransfer.evalReal (GeneralIrrationality.primitivePolynomial p) x ≠ 0) :
    iteratedDeriv n
      (logDeriv (RealTransfer.evalReal (GeneralIrrationality.primitivePolynomial p))) x =
      -(n.factorial : ℝ) * inverseGapSum (manuscriptRoots p hp) (n + 1) x := by
  rw [primitive_logDeriv_eq]
  apply actual_iterated_logDeriv p hp n x
  intro hh
  apply hx
  rw [GeneralIrrationality.primitivePolynomial_eval, hh, mul_zero]

theorem primitive_evalQ_eq (p : Real.Parameters) :
    RealTransfer.evalReal (GeneralIrrationality.primitivePolynomial p) =
      Real.evalQ ((GeneralIrrationality.primitivePolynomial p).map (Int.castRingHom ℚ)) := by
  have hc : (Rat.castHom ℝ).comp (Int.castRingHom ℚ) = Int.castRingHom ℝ := by
    ext z
    simp
  funext y
  simp [RealTransfer.evalReal, Real.evalQ, Real.realPolynomial, Polynomial.map_map,
    Polynomial.eval_map, hc]

/-- The same rational witness can be computed directly from the actual
primitive integer polynomial, embedded into Q[X]. -/
theorem primitive_inverseGapSum_rational
    (p : Real.Parameters) (hp : Real.Admissible p) (n : ℕ) (q : ℚ)
    (hq : RealTransfer.evalReal (GeneralIrrationality.primitivePolynomial p) (q : ℝ) ≠ 0) :
    inverseGapSum (manuscriptRoots p hp) (n + 1) (q : ℝ) =
      (rationalMoment ((GeneralIrrationality.primitivePolynomial p).map (Int.castRingHom ℚ))
        n q : ℝ) := by
  have hh := primitive_iterated_logDeriv p hp n (q : ℝ) hq
  rw [primitive_evalQ_eq] at hq hh
  rw [iterated_logDeriv_rational _ n q hq] at hh
  have hf : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  simp only [rationalMoment, Rat.cast_div, Rat.cast_neg, Rat.cast_natCast]
  apply (eq_div_iff hf).mpr
  nlinarith [hh]

theorem primitive_iterated_log
    (p : Real.Parameters) (hp : Real.Admissible p) (n : ℕ) (x : ℝ)
    (hx : RealTransfer.evalReal (GeneralIrrationality.primitivePolynomial p) x ≠ 0) :
    iteratedDeriv (n + 1)
      (fun y : ℝ => _root_.Real.log
        (RealTransfer.evalReal (GeneralIrrationality.primitivePolynomial p) y)) x =
      -(n.factorial : ℝ) * inverseGapSum (manuscriptRoots p hp) (n + 1) x := by
  let Q : ℚ[X] := (GeneralIrrationality.primitivePolynomial p).map (Int.castRingHom ℚ)
  have heq : RealTransfer.evalReal (GeneralIrrationality.primitivePolynomial p) = Real.evalQ Q :=
    primitive_evalQ_eq p
  rw [heq] at hx ⊢
  rw [iterated_log_eq_logDeriv Q n x hx, ← heq]
  exact primitive_iterated_logDeriv p hp n x (by simpa only [heq] using hx)

end LeanPaper.ReciprocalAllOrders

#print axioms LeanPaper.ReciprocalAllOrders.actual_inverseGapSum_rational
#print axioms LeanPaper.ReciprocalAllOrders.actual_iterated_log
#print axioms LeanPaper.ReciprocalAllOrders.primitive_iterated_log
