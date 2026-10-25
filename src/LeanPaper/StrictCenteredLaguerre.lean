import LeanPaper.NormalizedNewton
import LeanPaper.ReciprocalSecondMoment

/-!
# Exact strictness obstruction for the degree-normalized Laguerre bound

The difference between the two sides is a sum of squared pairwise reciprocal
root gaps. Thus the strengthened inequality is strict precisely when the
reciprocal gaps are not all equal. This file keeps that mathematical condition
explicit; ordinary real splitting alone does not establish strictness.
-/

noncomputable section
open scoped BigOperators
open Polynomial

namespace LeanPaper.StrictCenteredLaguerre

def dispersion {n : ℕ} (v : Fin n → ℝ) : ℝ :=
  (n : ℝ) * (∑ i, v i ^ 2) - (∑ i, v i) ^ 2

theorem pairwise_square_identity {n : ℕ} (v : Fin n → ℝ) :
    (∑ i, ∑ j, (v i - v j) ^ 2) = 2 * dispersion v := by
  simp only [sub_sq, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.sum_const, Finset.sum_mul, Finset.mul_sum]
  simp only [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  simp only [← Finset.mul_sum, ← Finset.sum_mul]
  unfold dispersion
  ring

theorem dispersion_nonnegative {n : ℕ} (v : Fin n → ℝ) :
    0 ≤ dispersion v := by
  have h : 0 ≤ ∑ i, ∑ j, (v i - v j) ^ 2 :=
    Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => sq_nonneg _))
  rw [pairwise_square_identity] at h
  linarith

theorem dispersion_positive_of_distinct {n : ℕ} (v : Fin n → ℝ)
    (i j : Fin n) (hij : v i ≠ v j) : 0 < dispersion v := by
  have hsq : 0 < (v i - v j) ^ 2 := sq_pos_of_ne_zero (sub_ne_zero.mpr hij)
  have hrow : (v i - v j) ^ 2 ≤ ∑ k, (v i - v k) ^ 2 :=
    Finset.single_le_sum (fun k _ => sq_nonneg (v i - v k)) (Finset.mem_univ j)
  have htotal : (∑ k, (v i - v k) ^ 2) ≤ ∑ l, ∑ k, (v l - v k) ^ 2 :=
    Finset.single_le_sum
      (fun l _ => Finset.sum_nonneg (fun k _ => sq_nonneg _)) (Finset.mem_univ i)
  have h := lt_of_lt_of_le hsq (le_trans hrow htotal)
  rw [pairwise_square_identity] at h
  linarith

theorem dispersion_eq_zero_iff {n : ℕ} (v : Fin n → ℝ) :
    dispersion v = 0 ↔ ∀ i j, v i = v j := by
  constructor
  · intro hz i j
    by_contra hij
    have h := dispersion_positive_of_distinct v i j hij
    linarith
  · intro heq
    have h : (∑ i, ∑ j, (v i - v j) ^ 2) = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      apply Finset.sum_eq_zero
      intro j _
      rw [heq i j, sub_self, zero_pow (by decide)]
    rw [pairwise_square_identity] at h
    linarith

open ManuscriptChain
open ReciprocalRootMoments ReciprocalLogDerivative ReciprocalSecondMoment
open NormalizedNewton

theorem evalQ_logDeriv (P : ℚ[X]) (x : ℝ) :
    logDeriv (Real.evalQ P) x = Real.evalQ P.derivative x / Real.evalQ P x := by
  rw [logDeriv_apply]
  change deriv (fun y : ℝ => (P.map (Rat.castHom ℝ)).eval y) x /
      (P.map (Rat.castHom ℝ)).eval x = _
  rw [Polynomial.deriv, Polynomial.derivative_map]
  rfl

/-- The exact sharpened gap for the actual determinant, with its real roots. -/
theorem actual_laguerre_dispersion (p : Real.Parameters) (hp : Real.Admissible p)
    (x : ℝ) (hx : Real.evalQ (Real.delta p) x ≠ 0) :
    laguerre p.h (Real.realPolynomial (Real.delta p)) x =
      (Real.evalQ (Real.delta p) x) ^ 2 *
        dispersion (fun i => (x - manuscriptRoots p hp i)⁻¹) := by
  have hfirst := actual_logDeriv p hp x hx
  rw [evalQ_logDeriv] at hfirst
  have hsecond := actual_second_moment_formula p hp x hx
  have heven : reciprocalEvenMoment (manuscriptRoots p hp) x 1 =
      ∑ i, ((x - manuscriptRoots p hp i)⁻¹) ^ 2 := by
    apply Finset.sum_congr rfl
    intro i _
    simp only [reciprocalAtom, pow_one]
    rw [show manuscriptRoots p hp i - x = -(x - manuscriptRoots p hp i) by ring,
      inv_neg, neg_sq]
  rw [heven] at hsecond
  unfold dispersion
  rw [← hfirst, hsecond]
  unfold laguerre Real.evalQ Real.realPolynomial
  simp only [Polynomial.derivative_map]
  have hx' : ((Real.delta p).map (Rat.castHom ℝ)).eval x ≠ 0 := hx
  field_simp [hx']
  <;> ring

theorem actual_laguerre_strict_of_distinct_roots
    (p : Real.Parameters) (hp : Real.Admissible p) (x : ℝ)
    (hx : Real.evalQ (Real.delta p) x ≠ 0)
    (i j : Fin p.h) (hij : manuscriptRoots p hp i ≠ manuscriptRoots p hp j) :
    0 < laguerre p.h (Real.realPolynomial (Real.delta p)) x := by
  rw [actual_laguerre_dispersion p hp x hx]
  apply mul_pos (sq_pos_of_ne_zero hx)
  apply dispersion_positive_of_distinct _ i j
  intro heq
  have h := inv_injective heq
  apply hij
  linarith

end LeanPaper.StrictCenteredLaguerre

#print axioms LeanPaper.StrictCenteredLaguerre.dispersion_eq_zero_iff
#print axioms LeanPaper.StrictCenteredLaguerre.actual_laguerre_dispersion
#print axioms LeanPaper.StrictCenteredLaguerre.actual_laguerre_strict_of_distinct_roots
