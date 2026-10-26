import ProofAdvances.Corollary_3_6
import Mathlib.Tactic

/-!
# Theorem 3.7 — exact first and second Turan inequalities in degree 3

Let P(X) = (X-a)(X-b)(X-c) with a,b,c real. We prove the
square decompositions for the first and second Turan expressions.
This establishes the complete Turan nonnegativity inequalities (3.7)
for degree h=3, both m=1 and m=2; the full arbitrary-degree theorem and
claimed Newton coefficient equality cases are still open.

We also prove the 3-mode spectral Cauchy inequality that underlies
the centered Taylor-coefficient bound stated in the manuscript.
-/

noncomputable section

namespace PaperAdvances.Theorem3_7

/-- The first Turan expression for a cubic with real roots is a sum of squares. -/
theorem cubic_first_turan_identity (x a b c : ℝ) :
    ((x-b)*(x-c) + (x-a)*(x-c) + (x-a)*(x-b))^2
      - ((x-a)*(x-b)*(x-c)) * (2*((x-a)+(x-b)+(x-c))) =
      ((x-b)*(x-c))^2 + ((x-a)*(x-c))^2 + ((x-a)*(x-b))^2 := by
  ring

theorem cubic_first_turan_nonnegative (x a b c : ℝ) :
    0 ≤ ((x-b)*(x-c) + (x-a)*(x-c) + (x-a)*(x-b))^2
      - ((x-a)*(x-b)*(x-c)) * (2*((x-a)+(x-b)+(x-c))) := by
  rw [cubic_first_turan_identity]
  positivity

/-- The second Turan expression for the cubic is also a sum of squares. -/
theorem cubic_second_turan_identity (x a b c : ℝ) :
    (2*((x-a)+(x-b)+(x-c)))^2
      - 6*((x-a)*(x-b) + (x-a)*(x-c) + (x-b)*(x-c)) =
      3*((x-a)^2 + (x-b)^2 + (x-c)^2)
        + ((x-a)+(x-b)+(x-c))^2 := by
  ring

theorem cubic_second_turan_nonnegative (x a b c : ℝ) :
    0 ≤ (2*((x-a)+(x-b)+(x-c)))^2
      - 6*((x-a)*(x-b) + (x-a)*(x-c) + (x-b)*(x-c)) := by
  rw [cubic_second_turan_identity]
  positivity

/-- Exact finite spectral variance identity for three real eigenvalues. -/
theorem three_mode_variance (a b c : ℝ) :
    3*(a^2 + b^2 + c^2) - (a+b+c)^2 =
      (a-b)^2 + (a-c)^2 + (b-c)^2 := by
  ring

/-- The h=3 case of F''(0) ≤ (1-1/h) F'(0)^2 for F(0)=1,
    F(Y)= ∏ (1+beta_j*Y). -/
theorem three_mode_taylor_bound (a b c : ℝ) :
    3 * (2*(a*b + a*c + b*c)) ≤ 2*(a+b+c)^2 := by
  nlinarith [sq_nonneg (a-b), sq_nonneg (a-c), sq_nonneg (b-c)]

end PaperAdvances.Theorem3_7

#print axioms PaperAdvances.Theorem3_7.cubic_first_turan_nonnegative
#print axioms PaperAdvances.Theorem3_7.cubic_second_turan_nonnegative
#print axioms PaperAdvances.Theorem3_7.three_mode_taylor_bound
