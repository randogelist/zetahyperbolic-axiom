import LeanPaper.ImportedSection4.Theorem_4_7_Finite_Root_Cluster_Count

/-!
# Proposition 4.8 — finite root-factor distance inequalities

For a real-root factorization F(X) = c*prod_j(X-r_j), pointwise
spectral distances yield lower and upper product bounds by the
degree. This is the purely finite implication in (4.16). It does
not claim the necessary exponential root gap has been established.
-/

namespace PaperOrder.Section4

/-- Absolute-value root-distance factors have nonnegative product. -/
theorem proposition_4_8_distance_product_nonnegative
    (ξ : ℝ) (xs : List ℝ) :
    0 ≤ (xs.map (fun r => |ξ - r|)).prod := by
  induction xs with
  | nil => simp
  | cons r rs ih =>
      simpa [List.map_cons, List.prod_cons] using
        (mul_nonneg (abs_nonneg (ξ - r)) ih)

/-- Lower bound on the product when every root has distance at least delta. -/
theorem proposition_4_8_distance_product_lower
    (ξ δ : ℝ) (xs : List ℝ) (hδ : 0 ≤ δ) :
    (∀ r ∈ xs, δ ≤ |ξ - r|) →
      δ ^ xs.length ≤ (xs.map (fun r => |ξ - r|)).prod := by
  induction xs with
  | nil =>
      intro _
      simp
  | cons r rs ih =>
      intro hroots
      have hr : δ ≤ |ξ - r| := hroots r (by simp)
      have hrs : ∀ x ∈ rs, δ ≤ |ξ - x| := by
        intro x hx
        exact hroots x (by simp [hx])
      have htail := ih hrs
      have hmul :
          δ * δ ^ rs.length ≤
            |ξ - r| * (rs.map (fun x => |ξ - x|)).prod :=
        mul_le_mul hr htail (pow_nonneg hδ _) (abs_nonneg _)
      simpa [List.length_cons, List.map_cons, List.prod_cons,
        pow_succ, mul_assoc, mul_comm, mul_left_comm] using hmul

/-- Upper bound on the product when all roots lie in the eta cluster. -/
theorem proposition_4_8_distance_product_upper
    (ξ η : ℝ) (xs : List ℝ) (hη : 0 ≤ η) :
    (∀ r ∈ xs, |ξ - r| ≤ η) →
      (xs.map (fun r => |ξ - r|)).prod ≤ η ^ xs.length := by
  induction xs with
  | nil =>
      intro _
      simp
  | cons r rs ih =>
      intro hroots
      have hr : |ξ - r| ≤ η := hroots r (by simp)
      have hrs : ∀ x ∈ rs, |ξ - x| ≤ η := by
        intro x hx
        exact hroots x (by simp [hx])
      have htail := ih hrs
      have hnonneg := proposition_4_8_distance_product_nonnegative ξ rs
      have hmul :
          |ξ - r| * (rs.map (fun x => |ξ - x|)).prod ≤
            η * η ^ rs.length :=
        mul_le_mul hr htail hnonneg hη
      simpa [List.length_cons, List.map_cons, List.prod_cons,
        pow_succ, mul_assoc, mul_comm, mul_left_comm] using hmul

/-- The exact lower and upper coefficient-scaled bounds at the center. -/
theorem proposition_4_8_factor_evaluation_bounds
    (ξ c δ η : ℝ) (xs : List ℝ) (hδ : 0 ≤ δ) (hη : 0 ≤ η)
    (hlower : ∀ r ∈ xs, δ ≤ |ξ - r|)
    (hupper : ∀ r ∈ xs, |ξ - r| ≤ η) :
    |c| * δ ^ xs.length ≤
      |c| * (xs.map (fun r => |ξ - r|)).prod ∧
      |c| * (xs.map (fun r => |ξ - r|)).prod ≤
        |c| * η ^ xs.length := by
  constructor
  · exact mul_le_mul_of_nonneg_left
      (proposition_4_8_distance_product_lower ξ δ xs hδ hlower)
      (abs_nonneg c)
  · exact mul_le_mul_of_nonneg_left
      (proposition_4_8_distance_product_upper ξ η xs hη hupper)
      (abs_nonneg c)

end PaperOrder.Section4

#print axioms PaperOrder.Section4.proposition_4_8_distance_product_nonnegative
#print axioms PaperOrder.Section4.proposition_4_8_distance_product_lower
#print axioms PaperOrder.Section4.proposition_4_8_distance_product_upper
#print axioms PaperOrder.Section4.proposition_4_8_factor_evaluation_bounds
