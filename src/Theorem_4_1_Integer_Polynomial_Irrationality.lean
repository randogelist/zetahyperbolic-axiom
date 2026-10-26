import Theorem_4_1_Spectral_Irrationality_Measure_Criterion

/-!
# Integer-polynomial criterion for bare irrationality

Nonzero integer-polynomial values that decay faster than the denominator cost
already rule out rationality. Spectral comparison is needed for the separate
quantitative approximation measure, not for this denominator contradiction.
The final criterion constructs its index from linear degree growth and
quadratic exponential decay; no index-selection premise is left implicit.
These are conditional implications. No decay estimate for the manuscript's
actual family is proved by this module.
-/

noncomputable section
open Polynomial

namespace ManuscriptChain.RealTransfer

/-- Exact integer-denominator obstruction. No spectral assumption is required. -/
theorem irrational_of_denominator_decay
    {Q : ℕ → Polynomial ℤ} {ξ : ℝ}
    (decay : ∀ b : ℕ, 0 < b → ∃ n : ℕ,
      evalReal (Q n) ξ ≠ 0 ∧
      (b : ℝ) ^ (Q n).natDegree * |evalReal (Q n) ξ| < 1) :
    Irrational ξ := by
  rw [Irrational]
  rintro ⟨r, hr⟩
  obtain ⟨n, hne, hsmall⟩ := decay r.den r.pos
  have hratio : (r.num : ℝ) / (r.den : ℝ) = ξ :=
    (Rat.cast_def r).symm.trans hr
  apply polynomial_integer_squeeze (Q n) r.num r.den r.pos
  · rw [hratio]
    exact hne
  · rw [hratio]
    exact hsmall

/-- For any fixed denominator, quadratic decay beats linear degree growth.
The witness index is constructed with the Archimedean property. -/
theorem exists_index_of_linear_degree_quadratic_decay
    {Q : ℕ → Polynomial ℤ} {ξ : ℝ} {n₀ D : ℕ} {c : ℝ}
    (hc : 0 < c)
    (degree : ∀ n, n₀ ≤ n → (Q n).natDegree ≤ D * (n + 1))
    (upper : ∀ n, n₀ ≤ n →
      |evalReal (Q n) ξ| ≤ Real.exp (-c * ((n + 1 : ℕ) : ℝ) ^ 2))
    (b : ℕ) (hb : 0 < b) :
    ∃ n : ℕ, n₀ ≤ n ∧
      (b : ℝ) ^ (Q n).natDegree * |evalReal (Q n) ξ| < 1 := by
  obtain ⟨N, hN⟩ := exists_nat_gt (((D : ℝ) * (b : ℝ)) / c)
  let n := n₀ + N
  have hn : n₀ ≤ n := by dsimp [n]; omega
  have hNx : (N : ℝ) < ((n + 1 : ℕ) : ℝ) := by
    exact_mod_cast (show N < n + 1 by dsimp [n]; omega)
  have hx : 0 < ((n + 1 : ℕ) : ℝ) := by positivity
  have hdom : (D : ℝ) * (b : ℝ) < c * ((n + 1 : ℕ) : ℝ) := by
    have h := (div_lt_iff₀ hc).mp (hN.trans hNx)
    simpa only [mul_comm] using h
  have hd : ((Q n).natDegree : ℝ) ≤ (D : ℝ) * ((n + 1 : ℕ) : ℝ) := by
    exact_mod_cast degree n hn
  have hlinear := mul_le_mul_of_nonneg_right hd (Nat.cast_nonneg b : (0 : ℝ) ≤ b)
  have hquadratic := mul_lt_mul_of_pos_right hdom hx
  have hnegative : ((Q n).natDegree : ℝ) * (b : ℝ) +
      (-c * ((n + 1 : ℕ) : ℝ) ^ 2) < 0 := by
    nlinarith
  have hbexp : (b : ℝ) ≤ Real.exp (b : ℝ) := by
    linarith [Real.add_one_le_exp (b : ℝ)]
  have hpow : (b : ℝ) ^ (Q n).natDegree ≤
      Real.exp (((Q n).natDegree : ℝ) * (b : ℝ)) := by
    rw [Real.exp_nat_mul]
    exact pow_le_pow_left₀ (Nat.cast_nonneg b) hbexp _
  refine ⟨n, hn, ?_⟩
  calc
    (b : ℝ) ^ (Q n).natDegree * |evalReal (Q n) ξ|
        ≤ (b : ℝ) ^ (Q n).natDegree *
            Real.exp (-c * ((n + 1 : ℕ) : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_left (upper n hn) (by positivity)
    _ ≤ Real.exp (((Q n).natDegree : ℝ) * (b : ℝ)) *
            Real.exp (-c * ((n + 1 : ℕ) : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_right hpow (Real.exp_pos _).le
    _ = Real.exp (((Q n).natDegree : ℝ) * (b : ℝ) +
            (-c * ((n + 1 : ℕ) : ℝ) ^ 2)) := (Real.exp_add _ _).symm
    _ < 1 := Real.exp_lt_one_iff.mpr hnegative

/-- Bare irrationality follows from nonzero values, linear degree growth, and
quadratic decay for the same integer-polynomial family. -/
theorem irrational_of_linear_degree_quadratic_decay
    {Q : ℕ → Polynomial ℤ} {ξ : ℝ} {n₀ D : ℕ} {c : ℝ}
    (hc : 0 < c)
    (nonzero : ∀ n, n₀ ≤ n → evalReal (Q n) ξ ≠ 0)
    (degree : ∀ n, n₀ ≤ n → (Q n).natDegree ≤ D * (n + 1))
    (upper : ∀ n, n₀ ≤ n →
      |evalReal (Q n) ξ| ≤ Real.exp (-c * ((n + 1 : ℕ) : ℝ) ^ 2)) :
    Irrational ξ := by
  apply irrational_of_denominator_decay
  intro b hb
  obtain ⟨n, hn, hsmall⟩ :=
    exists_index_of_linear_degree_quadratic_decay hc degree upper b hb
  exact ⟨n, nonzero n hn, hsmall⟩

end ManuscriptChain.RealTransfer

#print axioms ManuscriptChain.RealTransfer.irrational_of_denominator_decay
#print axioms ManuscriptChain.RealTransfer.exists_index_of_linear_degree_quadratic_decay
#print axioms ManuscriptChain.RealTransfer.irrational_of_linear_degree_quadratic_decay
