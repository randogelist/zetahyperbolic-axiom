import MAIN_CHAIN_ASSEMBLED
import Theorem_4_1_General_Odd_Zeta_Application
import Theorem_4_1_Integer_Polynomial_Irrationality
import Theorem_4_1_Linear_Odd_Zeta_Family

/-!
# General odd-zeta irrationality, conditional on normalized decay

The completed analytic chain supplies positivity and nonvanishing. Primitive
integer normalization and exact degree are constructed. Linear degree growth
and quadratic decay then imply irrationality, without a spectral estimate.
The decay hypothesis below is not proved for an actual family here.
-/

noncomputable section

namespace ManuscriptChain.GeneralArithmetic

theorem gramPositiveFamily (F : OddWeightFamily) : GramPositiveFamily F :=
  fun n hn => ManuscriptChain.GRAM_POSITIVE (F.parameters n) (F.admissible n hn)

theorem normalized_eval_nonzero (F : OddWeightFamily) (n : ℕ)
    (hn : F.onset ≤ n) : RealTransfer.evalReal (F.Q n) F.center ≠ 0 :=
  family_eval_nonzero F (gramPositiveFamily F) n hn

/-- A bundled *unproved* decay input. The degree condition is structural;
the substantive estimate concerns the primitive integer normalization. -/
def DecayHypothesis (F : OddWeightFamily) : Prop :=
  ∃ D : ℕ, ∃ c : ℝ, 0 < c ∧
    (∀ n, F.onset ≤ n → (F.parameters n).h ≤ D * (n + 1)) ∧
    (∀ n, F.onset ≤ n →
      |RealTransfer.evalReal (F.Q n) F.center| ≤
        Real.exp (-c * ((n + 1 : ℕ) : ℝ) ^ 2))

/-- The remaining quantitative estimate, allowing an arbitrary finite onset. -/
def EventualQuadraticDecay (F : OddWeightFamily) : Prop :=
  ∃ n₀ : ℕ, ∃ c : ℝ, 0 < c ∧
    ∀ n, n₀ ≤ n → |RealTransfer.evalReal (F.Q n) F.center| ≤
      Real.exp (-c * ((n + 1 : ℕ) : ℝ) ^ 2)

theorem irrational_of_quadratic_decay (F : OddWeightFamily)
    {D : ℕ} {c : ℝ} (hc : 0 < c)
    (degree : ∀ n, F.onset ≤ n → (F.parameters n).h ≤ D * (n + 1))
    (upper : ∀ n, F.onset ≤ n →
      |RealTransfer.evalReal (F.Q n) F.center| ≤
        Real.exp (-c * ((n + 1 : ℕ) : ℝ) ^ 2)) :
    Irrational F.center := by
  apply RealTransfer.irrational_of_linear_degree_quadratic_decay (D := D) hc
    (normalized_eval_nonzero F) _ upper
  intro n hn
  rw [F.degree n]
  exact degree n hn

theorem irrational_of_eventual_quadratic_decay (F : OddWeightFamily)
    {D : ℕ}
    (degree : ∀ n, F.onset ≤ n → (F.parameters n).h ≤ D * (n + 1))
    (decay : EventualQuadraticDecay F) : Irrational F.center := by
  obtain ⟨n₀, c, hc, upper⟩ := decay
  apply RealTransfer.irrational_of_linear_degree_quadratic_decay
    (n₀ := max F.onset n₀) (D := D) hc
  · intro n hn
    exact normalized_eval_nonzero F n ((le_max_left _ _).trans hn)
  · intro n hn
    rw [F.degree n]
    exact degree n ((le_max_left _ _).trans hn)
  · intro n hn
    exact upper n ((le_max_right _ _).trans hn)

/-- Stronger approximation conclusion: the compatible index budget remains
an additional quantitative input; positivity is already proved. -/
theorem measure_and_irrational (F : OddWeightFamily)
    (budget : ℕ → ℝ) (μ b₀ : ℕ) (upper : EvaluationUpper F budget)
    (index : RealTransfer.IndexBudget F.Q
      (localRadius F (gramPositiveFamily F)) budget F.onset μ b₀) :
    RealTransfer.RationalMeasure F.center μ b₀ ∧ Irrational F.center :=
  general_measure_and_irrational F (gramPositiveFamily F) budget μ b₀ upper index

end ManuscriptChain.GeneralArithmetic

namespace ManuscriptChain

/-- General fixed-odd-weight implication. Bundling the remaining estimate does
not discharge it, and the spectral statement alone does not imply this result. -/
theorem GENERAL_IRRATIONALITY (F : GeneralArithmetic.OddWeightFamily)
    (decay : GeneralArithmetic.DecayHypothesis F) : Irrational F.center := by
  obtain ⟨D, c, hc, degree, upper⟩ := decay
  exact GeneralArithmetic.irrational_of_quadratic_decay F hc degree upper

theorem GENERAL_RIEMANN_ZETA_IRRATIONALITY (F : GeneralArithmetic.OddWeightFamily)
    (decay : GeneralArithmetic.DecayHypothesis F) :
    Irrational (riemannZeta ((2 * F.k + 1 : ℕ) : ℂ)).re := by
  rw [← F.center_eq_riemannZeta]
  exact GENERAL_IRRATIONALITY F decay

/-- For explicit proportional families the degree bound is proved. The sole
remaining quantitative hypothesis is eventual decay of the primitive Q_n. -/
theorem LINEAR_FAMILY_IRRATIONALITY (k m a b : ℕ)
    (hk : 0 < k) (hm : 0 < m) (ha : 0 < a) (hab : a < b)
    (decay : GeneralArithmetic.EventualQuadraticDecay
      (GeneralArithmetic.linearFamily k m a b hk hm ha hab)) :
    Irrational (Real.zeta (2 * k + 1)) := by
  apply GeneralArithmetic.irrational_of_eventual_quadratic_decay
    (GeneralArithmetic.linearFamily k m a b hk hm ha hab) (D := b - a) _ decay
  intro n _
  rw [GeneralArithmetic.linearFamily_h]

theorem LINEAR_FAMILY_RIEMANN_ZETA_IRRATIONALITY (k m a b : ℕ)
    (hk : 0 < k) (hm : 0 < m) (ha : 0 < a) (hab : a < b)
    (decay : GeneralArithmetic.EventualQuadraticDecay
      (GeneralArithmetic.linearFamily k m a b hk hm ha hab)) :
    Irrational (riemannZeta ((2 * k + 1 : ℕ) : ℂ)).re := by
  have hcenter := (GeneralArithmetic.linearFamily k m a b hk hm ha hab).center_eq_riemannZeta
  change Real.zeta (2 * k + 1) = (riemannZeta ((2 * k + 1 : ℕ) : ℂ)).re at hcenter
  rw [← hcenter]
  exact LINEAR_FAMILY_IRRATIONALITY k m a b hk hm ha hab decay

end ManuscriptChain

#print axioms ManuscriptChain.GeneralArithmetic.normalized_eval_nonzero
#print axioms ManuscriptChain.GENERAL_IRRATIONALITY
#print axioms ManuscriptChain.GENERAL_RIEMANN_ZETA_IRRATIONALITY
#print axioms ManuscriptChain.LINEAR_FAMILY_IRRATIONALITY
#print axioms ManuscriptChain.LINEAR_FAMILY_RIEMANN_ZETA_IRRATIONALITY
#print axioms ManuscriptChain.GeneralArithmetic.measure_and_irrational
