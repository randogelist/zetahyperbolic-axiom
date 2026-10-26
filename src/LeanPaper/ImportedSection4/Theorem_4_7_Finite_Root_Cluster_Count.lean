import LeanPaper.ImportedSection4.Theorem_4_6_Leading_Coefficient_Determinant_Barrier

/-!
# Theorem 4.7 — finite averaging-to-clustering inequality

For a finite list of spectral logarithmic exponents s_j, assume
s_j<=U and mean(s_j)>=mu. Then a positive proportion must have
s_j>=tau. This is the exact counting argument in the manuscript,
without asserting the unproved input bounds on the actual B_K.
-/

namespace PaperOrder.Section4

/-- Number of exponents at least the specified clustering threshold. -/
noncomputable def countAtLeastThreshold (τ : ℝ) : List ℝ → ℕ
  | [] => 0
  | x :: xs => (if τ ≤ x then 1 else 0) + countAtLeastThreshold τ xs

/-- Elementary upper bound: outside the cluster, s_j < tau, and in the
cluster s_j <= U. The argument works for negative exponents as well. -/
theorem theorem_4_7_finite_cluster_sum_bound
    (xs : List ℝ) (U τ : ℝ) :
    (∀ x ∈ xs, x ≤ U) →
      xs.sum ≤ τ * (xs.length : ℝ) +
        (U - τ) * (countAtLeastThreshold τ xs : ℝ) := by
  induction xs with
  | nil =>
      intro _
      simp [countAtLeastThreshold]
  | cons x xs ih =>
      intro hcap
      have hx : x ≤ U := hcap x (by simp)
      have htail : ∀ y ∈ xs, y ≤ U := by
        intro y hy
        exact hcap y (by simp [hy])
      have hprev := ih htail
      by_cases hgood : τ ≤ x
      · have hcalc :
            x + xs.sum ≤ τ * ((xs.length : ℝ) + 1) +
              (U - τ) * ((countAtLeastThreshold τ xs : ℝ) + 1) := by
          nlinarith [hprev, hx]
        simpa [countAtLeastThreshold, hgood, List.sum_cons,
          List.length_cons, Nat.cast_add, Nat.cast_one,
          add_assoc, add_comm, add_left_comm] using hcalc
      · have hbad : x < τ := lt_of_not_ge hgood
        have hcalc :
            x + xs.sum ≤ τ * ((xs.length : ℝ) + 1) +
              (U - τ) * (countAtLeastThreshold τ xs : ℝ) := by
          nlinarith [hprev, hbad]
        simpa [countAtLeastThreshold, hgood, List.sum_cons,
          List.length_cons, Nat.cast_add, Nat.cast_one,
          add_assoc, add_comm, add_left_comm] using hcalc

/-- Quantitative proportion of clustered spectral exponents, based
only on an upper bound and a lower bound for the average. -/
theorem theorem_4_7_cluster_fraction_lower_bound
    (xs : List ℝ) (U τ μ : ℝ)
    (hU : τ < U)
    (hcap : ∀ x ∈ xs, x ≤ U)
    (haverage : μ * (xs.length : ℝ) ≤ xs.sum) :
    (μ - τ) / (U - τ) * (xs.length : ℝ) ≤
      (countAtLeastThreshold τ xs : ℝ) := by
  have hsum := theorem_4_7_finite_cluster_sum_bound xs U τ hcap
  have hkey :
      (μ - τ) * (xs.length : ℝ) ≤
        (U - τ) * (countAtLeastThreshold τ xs : ℝ) := by
    nlinarith [hsum, haverage]
  have hden : 0 < U - τ := by linarith
  calc
    (μ - τ) / (U - τ) * (xs.length : ℝ) =
        ((μ - τ) * (xs.length : ℝ)) / (U - τ) := by ring
    _ ≤ (countAtLeastThreshold τ xs : ℝ) :=
      (div_le_iff₀ hden).2 (by nlinarith [hkey])

/-- Exact rational check of the paper's quoted 1.40 percent threshold,
assuming its determinant lower bound and eigenvalue upper bound. -/
theorem theorem_4_7_cluster_percentage_arithmetic :
    (14 / 1000 : ℚ) <
      ((2589 / 10000 : ℚ) - (1 / 10 : ℚ)) /
        ((11411 / 1000 : ℚ) - (1 / 10 : ℚ)) := by
  norm_num

end PaperOrder.Section4

#print axioms PaperOrder.Section4.theorem_4_7_finite_cluster_sum_bound
#print axioms PaperOrder.Section4.theorem_4_7_cluster_fraction_lower_bound
#print axioms PaperOrder.Section4.theorem_4_7_cluster_percentage_arithmetic
