import LeanPaper.ImportedMultiweight.PositiveSlopeSpectrum
import LeanPaper.ImportedSection3.CubicTuran
import MAIN_CHAIN_ASSEMBLED
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Tactic

/-!
# Direct principal theorem advance: Theorem 3.7 in arbitrary dimension

This is the first-derivative Turan/Laguerre inequality for the ACTUAL
odd-zeta rational Hankel determinant. The archived dual specializations
are not imported here. The full statement is for every matrix dimension,
not just the quadratic/cubic examples of the earlier source.

The key is a proved exact derivative identity for any real affine factor:
T(L*P) = L(x)^2*T(P) + (L'(x))^2*P(x)^2,
where T(P) = P'(x)^2 - P(x)*P''(x).

The resulting nonnegativity uses only the already established REAL
linear-factor representations. It does NOT prove higher-order Turan
inequalities, arbitrary interlacing, the zeta(7) Beukers integral, or any
irrationality assertion. No new axioms or implicit witnesses.
-/

noncomputable section
open scoped BigOperators
open Polynomial

namespace PaperAdvances.Theorem3_7_AllDegrees

/-- The actual first-derivative Turan/Laguerre expression of a real polynomial. -/
def turan (P : ℝ[X]) (x : ℝ) : ℝ :=
  ((Polynomial.derivative P).eval x) ^ 2 -
    P.eval x * ((Polynomial.derivative (Polynomial.derivative P)).eval x)

/-- Exact affine multiplication identity, valid for ALL real polynomials. -/
theorem turan_mul_linear (P L : ℝ[X]) (a x : ℝ)
    (hL : Polynomial.derivative L = Polynomial.C a) :
    turan (L * P) x =
      (L.eval x) ^ 2 * turan P x + a ^ 2 * (P.eval x) ^ 2 := by
  have hfirst : Polynomial.derivative (L * P) =
      Polynomial.C a * P + L * Polynomial.derivative P := by
    rw [Polynomial.derivative_mul, hL]
  have hsecond :
      Polynomial.derivative (Polynomial.derivative (L * P)) =
        (2 : ℝ[X]) * Polynomial.C a * Polynomial.derivative P +
          L * Polynomial.derivative (Polynomial.derivative P) := by
    rw [hfirst]
    simp only [Polynomial.derivative_add, Polynomial.derivative_mul,
      Polynomial.derivative_C, hL, zero_mul, zero_add]
    ring
  unfold turan
  rw [hsecond, hfirst]
  simp [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C] <;> ring

/-- The affine X-factor has constant formal derivative. -/
theorem affine_derivative (a b : ℝ) :
    Polynomial.derivative
      (Polynomial.C a * (Polynomial.X : ℝ[X]) + Polynomial.C b) =
        Polynomial.C a := by
  rw [Polynomial.derivative_add, Polynomial.derivative_C_mul_X,
    Polynomial.derivative_C, add_zero]

/-- Universal exact recurrence for products of linear real factors. -/
theorem turan_mul_affine (P : ℝ[X]) (a b x : ℝ) :
    turan ((Polynomial.C a * (Polynomial.X : ℝ[X]) + Polynomial.C b) * P) x =
      (a * x + b) ^ 2 * turan P x + a ^ 2 * (P.eval x) ^ 2 := by
  rw [turan_mul_linear P _ a x (affine_derivative a b)]
  simp only [Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X] <;> ring

/-- Real scalar multiplication preserves the Turan inequality, even for
negative or vanishing scale. -/
theorem turan_const_mul (P : ℝ[X]) (c x : ℝ) :
    turan (Polynomial.C c * P) x = c ^ 2 * turan P x := by
  simpa using (turan_mul_linear P (Polynomial.C c) 0 x (by simp))

/-- Complete first-derivative Turan inequality at EVERY finite degree for
an arbitrary real affine-factor family, without sign restrictions. -/
theorem finite_affine_turan_nonnegative {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (a b : ι → ℝ) (x : ℝ) :
    0 ≤ turan (s.prod (fun i =>
      Polynomial.C (a i) * (Polynomial.X : ℝ[X]) + Polynomial.C (b i))) x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp [turan]
  | @insert i s hi ih =>
      rw [Finset.prod_insert hi, turan_mul_affine]
      exact add_nonneg
        (mul_nonneg (sq_nonneg _) ih)
        (mul_nonneg (sq_nonneg _) (sq_nonneg _))

/-- Every real polynomial with an explicit REAL affine-factorization
satisfies the full-degree first-derivative Turan inequality. -/
theorem factored_turan_nonnegative {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (a b : ι → ℝ) (c : ℝ) (P : ℝ[X])
    (hP : P = Polynomial.C c *
      s.prod (fun i => Polynomial.C (a i) * (Polynomial.X : ℝ[X]) +
        Polynomial.C (b i))) (x : ℝ) :
    0 ≤ turan P x := by
  rw [hP, turan_const_mul]
  exact mul_nonneg (sq_nonneg c)
    (finite_affine_turan_nonnegative s a b x)

/-- Theorem 3.7 first-derivative Turan inequality for any symmetric
finite pencil with its already-proved real spectral factorization. -/
theorem spectral_turan_nonnegative {n : ℕ}
    {p : ManuscriptChain.Spectral.SymmetricAffinePencil n}
    (h : ManuscriptChain.Spectral.RootFactorization p) (x : ℝ) :
    0 ≤ turan p.detPolynomial x := by
  have hfactor (i : Fin n) :
      ManuscriptChain.Spectral.spectralFactor p.center (h.beta i) =
        Polynomial.C (h.beta i) * (Polynomial.X : ℝ[X]) +
          Polynomial.C (1 - p.center * h.beta i) := by
    simp only [ManuscriptChain.Spectral.spectralFactor, map_sub,
      map_mul, map_one]
    ring
  rw [h.factorization, turan_const_mul]
  apply mul_nonneg (sq_nonneg _)
  simp_rw [hfactor]
  exact finite_affine_turan_nonnegative Finset.univ h.beta
    (fun i => 1 - p.center * h.beta i) x

/-- Printed Theorem 3.7: a nontrivial ALL-DEGREES extension of the
quadratic/cubic proofs, now on the *actual* rational Hankel determinant.
No additional Gram-positivity premise remains: it is discharged by the
previously certified odd-weight moment integral and Gram theorem. -/
theorem THEOREM_3_7_ACTUAL_ALL_DEGREES
    (p : ManuscriptChain.Real.Parameters)
    (hp : ManuscriptChain.Real.Admissible p) (x : ℝ) :
    0 ≤ turan (ManuscriptChain.Real.realPolynomial
        (ManuscriptChain.Real.delta p)) x := by
  have hpositive : ManuscriptChain.General.GramPositive p :=
    ManuscriptChain.GRAM_POSITIVE p hp
  have h := spectral_turan_nonnegative
    (ManuscriptChain.General.factorization p hpositive) x
  simpa only [ManuscriptChain.Real.manuscriptPencil_detPolynomial] using h

/-- First-derivative Turan inequality for every symmetric positive-slope
pencil, including indefinite or singular constant matrices. -/
theorem positive_slope_turan_nonnegative {n : ℕ}
    (p : ManuscriptChain.Spectral.SymmetricAffinePencil n)
    (hp : p.direction.PosDef) (x : ℝ) :
    0 ≤ turan p.detPolynomial x := by
  obtain ⟨beta, hfactor⟩ :=
    PaperAdvances.Theorem5_2_RealRoots.positive_slope_factorization p hp
  rw [hfactor, turan_const_mul]
  apply mul_nonneg (sq_nonneg _)
  have ht := finite_affine_turan_nonnegative
    (Finset.univ : Finset (Fin n))
    (fun _ : Fin n => (1 : ℝ))
    (fun i => beta i - p.center) x
  simpa using ht

end PaperAdvances.Theorem3_7_AllDegrees

#print axioms PaperAdvances.Theorem3_7_AllDegrees.turan_mul_linear
#print axioms PaperAdvances.Theorem3_7_AllDegrees.finite_affine_turan_nonnegative
#print axioms PaperAdvances.Theorem3_7_AllDegrees.THEOREM_3_7_ACTUAL_ALL_DEGREES
