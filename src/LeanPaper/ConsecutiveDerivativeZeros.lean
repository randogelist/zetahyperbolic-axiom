import LeanPaper.NormalizedNewton

/-!
# Consecutive derivative zeros force a root

For a real-split polynomial, two consecutive derivative values cannot both
vanish at a non-root, provided the lower derivative is nonconstant. This
removes the proposed interior zero-block exception for the zeta-centered
Taylor coefficients. It does not assert that each individual coefficient
is nonzero: such a claim is false for general real-rooted polynomials.
-/

noncomputable section
open Polynomial

namespace LeanPaper.ConsecutiveDerivativeZeros

open LeanPaper.HigherDerivativeTuran
open PaperAdvances.Theorem3_7_AllDegrees

theorem consecutive_derivative_zeros_force_root {P : ℝ[X]} (hP : P.Splits)
    (k : ℕ) (hk : k < P.natDegree) (x : ℝ)
    (hzero : (Polynomial.derivative^[k] P).eval x = 0)
    (hnext : (Polynomial.derivative^[k + 1] P).eval x = 0) : P.eval x = 0 := by
  induction k with
  | zero => simpa only [Function.iterate_zero, id_eq] using hzero
  | succ k ih =>
      have hk' : k < P.natDegree := by omega
      have htur : turan (Polynomial.derivative^[k] P) x = 0 := by
        have h1 : (Polynomial.derivative (Polynomial.derivative^[k] P)).eval x = 0 := by
          simpa only [Function.iterate_succ_apply'] using hzero
        have h2 : (Polynomial.derivative (Polynomial.derivative
            (Polynomial.derivative^[k] P))).eval x = 0 := by
          simpa only [Function.iterate_succ_apply'] using hnext
        simp only [turan, h1, h2, zero_pow (by decide : 2 ≠ 0), mul_zero, sub_zero]
      have hprev := ((iterated_turan_eq_zero_iff hP k hk' x).mp htur).1
      exact ih hk' hprev hzero

theorem consecutive_derivative_nonvanishing {P : ℝ[X]} (hP : P.Splits)
    (k : ℕ) (hk : k < P.natDegree) (x : ℝ) (hx : P.eval x ≠ 0) :
    (Polynomial.derivative^[k] P).eval x ≠ 0 ∨
      (Polynomial.derivative^[k + 1] P).eval x ≠ 0 := by
  by_contra hh
  push Not at hh
  exact hx (consecutive_derivative_zeros_force_root hP k hk x hh.1 hh.2)

/-- At every non-root, consecutive Taylor coefficients cannot both vanish. -/
theorem consecutive_taylor_nonvanishing {P : ℝ[X]} (hP : P.Splits)
    (k : ℕ) (hk : k < P.natDegree) (x : ℝ) (hx : P.eval x ≠ 0) :
    (P.taylor x).coeff k ≠ 0 ∨ (P.taylor x).coeff (k + 1) ≠ 0 := by
  have hs : (P.taylor x).Splits := hP.comp_X_add_C x
  have hh := consecutive_derivative_nonvanishing hs k
    (by simpa only [Polynomial.natDegree_taylor] using hk) 0
    (by simpa [Polynomial.taylor_apply, Polynomial.eval_comp] using hx)
  have hv (j : ℕ) : (Polynomial.derivative^[j] (P.taylor x)).eval 0 =
      (j.factorial : ℝ) * (P.taylor x).coeff j := by
    rw [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_iterate_derivative]
    simp only [zero_add, Nat.descFactorial_self, nsmul_eq_mul]
  rcases hh with hh | hh
  · exact Or.inl (fun heq => hh (by rw [hv k, heq, mul_zero]))
  · exact Or.inr (fun heq => hh (by rw [hv (k + 1), heq, mul_zero]))

open ManuscriptChain

/-- Applied to the actual primitive manuscript polynomial at the zeta center. -/
theorem actual_centered_consecutive_nonvanishing
    (p : Real.Parameters) (hp : Real.Admissible p) (k : ℕ) (hk : k < p.h) :
    ((primitiveRealPolynomial p).taylor (Real.zeta p.weight)).coeff k ≠ 0 ∨
      ((primitiveRealPolynomial p).taylor (Real.zeta p.weight)).coeff (k + 1) ≠ 0 := by
  apply consecutive_taylor_nonvanishing (primitiveRealPolynomial_splits p hp) k
  · simpa only [primitiveRealPolynomial_natDegree] using hk
  · exact ne_of_gt (GeneralIrrationality.primitivePolynomial_eval_pos p hp)

/-- Diagnostic for the manuscript's argument, not an actual-family counterexample:
real splitting, distinct nonzero roots and nonzero center do not force every
centered coefficient to be nonzero. The middle coefficient of X^2-1 vanishes. -/
theorem distinct_nonzero_roots_allow_zero_coefficient :
    ∃ P : ℝ[X], P.Splits ∧ P.eval 0 ≠ 0 ∧
      P.eval 1 = 0 ∧ P.eval (-1) = 0 ∧ (1 : ℝ) ≠ -1 ∧ P.coeff 1 = 0 := by
  refine ⟨(X - C 1) * (X - C (-1)),
    (Polynomial.Splits.X_sub_C 1).mul (Polynomial.Splits.X_sub_C (-1)), ?_⟩
  have heq : ((X - C 1) * (X - C (-1)) : ℝ[X]) = X ^ 2 - 1 := by
    simp only [C_neg, C_1]
    ring
  rw [heq]
  norm_num [Polynomial.coeff_sub, Polynomial.coeff_one]

end LeanPaper.ConsecutiveDerivativeZeros

#print axioms LeanPaper.ConsecutiveDerivativeZeros.consecutive_taylor_nonvanishing
#print axioms LeanPaper.ConsecutiveDerivativeZeros.actual_centered_consecutive_nonvanishing
