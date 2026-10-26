import PaperChain.Stage04
import Theorem_4_1_Integer_Polynomial_Irrationality

/-!
Stage 5: the actual integer-polynomial denominator obstruction, and the
proved abstract exponential-decay -> irrationality theorem. The first
part of the paper's *quantitative irrationality measure* additionally
needs spectral local comparison, index selection, and height estimates.
-/

namespace PaperChain
open Polynomial
open ManuscriptChain.RealTransfer

/-- A direct, genuinely proved conditional irrationality criterion. -/
theorem stage05_irrational_from_quadratic_decay
    {Q : ℕ → Polynomial ℤ} {ξ : ℝ} {n₀ D : ℕ} {c : ℝ}
    (hc : 0 < c)
    (nonzero : ∀ n, n₀ ≤ n → evalReal (Q n) ξ ≠ 0)
    (degree : ∀ n, n₀ ≤ n → (Q n).natDegree ≤ D * (n + 1))
    (decay : ∀ n, n₀ ≤ n →
      |evalReal (Q n) ξ| ≤ Real.exp (-c * ((n + 1 : ℕ) : ℝ) ^ 2)) :
    Irrational ξ :=
  irrational_of_linear_degree_quadratic_decay hc nonzero degree decay

/-- Quantitative integer-exponent separation from checked local comparison,
decay and an index budget (the extra analytic hypotheses are explicit). -/
theorem stage05_conditional_rational_measure
    {Q : ℕ → Polynomial ℤ} {ξ : ℝ} {radius budget : ℕ → ℝ}
    {n₀ μ b₀ : ℕ}
    (comparison : LocalComparison Q ξ radius n₀)
    (decay : Decay Q ξ budget n₀)
    (indices : IndexBudget Q radius budget n₀ μ b₀) :
    RationalMeasure ξ μ b₀ :=
  conditional_measure comparison decay indices

end PaperChain
