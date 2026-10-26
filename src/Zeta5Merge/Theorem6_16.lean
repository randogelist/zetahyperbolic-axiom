import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Theorem 6.16: uniform comparison requires endpoint positivity

This module proves the compactness step for a ratio on `[0,1]`. Applications
must supply the continuous compactified ratio and its strictly positive
endpoint values. It does not identify the manuscript's formal beta functional
with an analytic weight, nor prove that identity by an assumption-free shortcut.
-/

namespace Zeta5Merge.Theorem6_16

/-- A positive continuous function on the closed compactified interval has a
strictly positive uniform lower bound and a finite upper bound. -/
theorem uniform_bounds_of_positive_continuous
    (ratio : ℝ → ℝ)
    (hcontinuous : ContinuousOn ratio (Set.Icc 0 1))
    (hpositive : ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 < ratio t) :
    ∃ lower upper : ℝ, 0 < lower ∧ 0 < upper ∧
      ∀ t ∈ Set.Icc (0 : ℝ) 1, lower ≤ ratio t ∧ ratio t ≤ upper := by
  have hnonempty : (Set.Icc (0 : ℝ) 1).Nonempty := ⟨0, by norm_num⟩
  obtain ⟨a, ha, hmin⟩ := isCompact_Icc.exists_isMinOn hnonempty hcontinuous
  obtain ⟨b, hb, hmax⟩ := isCompact_Icc.exists_isMaxOn hnonempty hcontinuous
  exact ⟨ratio a, ratio b, hpositive a ha, hpositive b hb,
    fun t ht => ⟨hmin ht, hmax ht⟩⟩

/-- Separating the two endpoints makes the exact additional obligations
visible: interior positivity does not supply either one. -/
theorem uniform_bounds_of_positive_interior_and_endpoints
    (ratio : ℝ → ℝ)
    (hcontinuous : ContinuousOn ratio (Set.Icc 0 1))
    (hinterior : ∀ t ∈ Set.Ioo (0 : ℝ) 1, 0 < ratio t)
    (hzero : 0 < ratio 0) (hone : 0 < ratio 1) :
    ∃ lower upper : ℝ, 0 < lower ∧ 0 < upper ∧
      ∀ t ∈ Set.Icc (0 : ℝ) 1, lower ≤ ratio t ∧ ratio t ≤ upper := by
  apply uniform_bounds_of_positive_continuous ratio hcontinuous
  intro t ht
  by_cases ht0 : t = 0
  · simpa [ht0] using hzero
  by_cases ht1 : t = 1
  · simpa [ht1] using hone
  apply hinterior t
  exact ⟨lt_of_le_of_ne ht.1 (Ne.symm ht0), lt_of_le_of_ne ht.2 ht1⟩

/-- Pull the compact ratio bounds back to actual weights. The ratio identity,
its analytic continuity, and endpoint positivity remain explicit inputs. -/
theorem weight_comparison_of_compact_ratio
    (ratio compactify weight mixedWeight : ℝ → ℝ)
    (hcontinuous : ContinuousOn ratio (Set.Icc 0 1))
    (hpositive : ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 < ratio t)
    (hcompactify : ∀ v : ℝ, 0 < v → compactify v ∈ Set.Icc (0 : ℝ) 1)
    (hweight : ∀ v : ℝ, 0 < v → 0 ≤ weight v)
    (hidentity : ∀ v : ℝ, 0 < v → mixedWeight v = ratio (compactify v) * weight v) :
    ∃ lower upper : ℝ, 0 < lower ∧ 0 < upper ∧
      ∀ v : ℝ, 0 < v → lower * weight v ≤ mixedWeight v ∧
        mixedWeight v ≤ upper * weight v := by
  obtain ⟨lower, upper, hlower, hupper, hbounds⟩ :=
    uniform_bounds_of_positive_continuous ratio hcontinuous hpositive
  refine ⟨lower, upper, hlower, hupper, ?_⟩
  intro v hv
  obtain ⟨hl, hu⟩ := hbounds (compactify v) (hcompactify v hv)
  rw [hidentity v hv]
  exact ⟨mul_le_mul_of_nonneg_right hl (hweight v hv),
    mul_le_mul_of_nonneg_right hu (hweight v hv)⟩

/-- Exact counterexample: the ratio `t` is continuous, positive throughout
`(0,1]`, and positive at the far endpoint, but has no positive uniform lower
bound because its other endpoint is zero. -/
theorem missing_zero_endpoint_counterexample :
    ContinuousOn (fun t : ℝ => t) (Set.Icc 0 1) ∧
      (∀ t ∈ Set.Ioc (0 : ℝ) 1, 0 < t) ∧
      (0 : ℝ) < 1 ∧
      ¬ (∃ lower : ℝ, 0 < lower ∧
        ∀ t ∈ Set.Ioc (0 : ℝ) 1, lower ≤ t) := by
  refine ⟨continuous_id.continuousOn, fun _ ht => ht.1, by norm_num, ?_⟩
  rintro ⟨lower, hlower, hbound⟩
  have htpos : 0 < min (lower / 2) (1 / 2 : ℝ) := by positivity
  have htone : min (lower / 2) (1 / 2 : ℝ) ≤ 1 := by
    exact (min_le_right _ _).trans (by norm_num)
  have h := hbound (min (lower / 2) (1 / 2 : ℝ)) ⟨htpos, htone⟩
  have hm := min_le_left (lower / 2) (1 / 2 : ℝ)
  linarith

end Zeta5Merge.Theorem6_16

#print axioms Zeta5Merge.Theorem6_16.uniform_bounds_of_positive_continuous
#print axioms Zeta5Merge.Theorem6_16.uniform_bounds_of_positive_interior_and_endpoints
#print axioms Zeta5Merge.Theorem6_16.weight_comparison_of_compact_ratio
#print axioms Zeta5Merge.Theorem6_16.missing_zero_endpoint_counterexample
