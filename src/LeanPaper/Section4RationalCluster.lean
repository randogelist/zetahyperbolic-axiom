import LeanPaper.Section4TransferComplete
import Mathlib.Algebra.Order.Floor.Ring

/-!
# Corrected rational-root exclusion for exponential clusters

The upper-closeness premise in Proposition 4.8 is kept explicit. An eventual
rational approximation measure controls large denominators, and irrationality
gives a uniform positive separation for all bounded denominators. Combining
these two arguments removes the small-denominator exception. No lower root
separation estimate is turned into an upper-closeness estimate.
-/

noncomputable section
open Filter Topology

namespace LeanPaper.Section4RationalCluster

/-- A real-exponent eventual approximation measure already excludes rational
centers: a rational representation can be rescaled to arbitrarily large
denominators. The exponent need not be an integer. -/
theorem irrational_of_real_measure (ξ μ : ℝ) (b₀ : ℕ)
    (hmeasure : ∀ a : ℤ, ∀ b : ℕ, 0 < b → b₀ ≤ b →
      (b : ℝ)^(-μ) < |ξ-(a : ℝ)/b|) : Irrational ξ := by
  rw [Irrational]
  rintro ⟨r, hr⟩
  let t : ℕ := b₀ + 1
  let b : ℕ := r.den * t
  let a : ℤ := r.num * (t : ℤ)
  have ht : 0 < t := by dsimp [t]; omega
  have hd : 0 < r.den := r.pos
  have hb : 0 < b := Nat.mul_pos hd ht
  have hbb : b₀ ≤ b := by
    dsimp [b, t]
    exact le_trans (by omega : b₀ ≤ b₀+1)
      (by simpa using Nat.mul_le_mul_right (b₀+1) (show 1 ≤ r.den by omega))
  have htR : (t : ℝ) ≠ 0 := by exact_mod_cast ht.ne'
  have hdR : (r.den : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  have hab : (a : ℝ)/(b : ℝ) = ξ := by
    calc
      (a : ℝ)/(b : ℝ) = (r.num : ℝ)/(r.den : ℝ) := by
        dsimp [a, b]
        push_cast
        field_simp <;> ring
      _ = (r : ℝ) := (Rat.cast_def r).symm
      _ = ξ := hr
  have h := hmeasure a b hb hbb
  rw [hab, sub_self, abs_zero] at h
  exact not_lt_of_ge (Real.rpow_pos_of_pos (by exact_mod_cast hb) (-μ)).le h

/-- Construct a positive separation from every rational with a fixed positive
denominator. The two neighboring integers around `b*ξ` provide the bound. -/
theorem fixed_denominator_separation (ξ : ℝ) (hξ : Irrational ξ)
    (b : ℕ) (hb : 0 < b) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ a : ℤ, δ ≤ |ξ-(a : ℝ)/b| := by
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hne (a : ℤ) : ξ ≠ (a : ℝ)/b := by
    intro h
    rw [Irrational] at hξ
    apply hξ
    refine ⟨(a : ℚ)/(b : ℚ), ?_⟩
    simpa only [Rat.cast_div, Rat.cast_intCast, Rat.cast_natCast] using h.symm
  let A : ℤ := ⌊(b : ℝ)*ξ⌋
  have hl : 0 < (b : ℝ)*ξ-(A : ℝ) := by
    have hfloor : (A : ℝ) ≤ (b : ℝ)*ξ := Int.floor_le _
    by_contra hn
    have heq : ξ*(b : ℝ) = (A : ℝ) := by
      have hnonpos := le_of_not_gt hn
      nlinarith
    exact hne A ((eq_div_iff hbR.ne').2 heq)
  have hu : 0 < (A : ℝ)+1-(b : ℝ)*ξ :=
    sub_pos.mpr (Int.lt_floor_add_one _)
  refine ⟨min ((b : ℝ)*ξ-(A : ℝ)) ((A : ℝ)+1-(b : ℝ)*ξ)/(b : ℝ),
    div_pos (lt_min hl hu) hbR, ?_⟩
  intro a
  apply (div_le_iff₀ hbR).2
  by_cases ha : a ≤ A
  · have haR : (a : ℝ) ≤ (A : ℝ) := by exact_mod_cast ha
    calc
      min ((b : ℝ)*ξ-(A : ℝ)) ((A : ℝ)+1-(b : ℝ)*ξ)
          ≤ (b : ℝ)*ξ-(A : ℝ) := min_le_left _ _
      _ ≤ (b : ℝ)*ξ-(a : ℝ) := by linarith
      _ = (ξ-(a : ℝ)/(b : ℝ))*(b : ℝ) := by field_simp [hbR.ne']; ring
      _ ≤ |ξ-(a : ℝ)/(b : ℝ)|*(b : ℝ) :=
        mul_le_mul_of_nonneg_right (le_abs_self _) hbR.le
  · have haZ : A+1 ≤ a := by omega
    have haR : (A : ℝ)+1 ≤ (a : ℝ) := by exact_mod_cast haZ
    calc
      min ((b : ℝ)*ξ-(A : ℝ)) ((A : ℝ)+1-(b : ℝ)*ξ)
          ≤ (A : ℝ)+1-(b : ℝ)*ξ := min_le_right _ _
      _ ≤ (a : ℝ)-(b : ℝ)*ξ := by linarith
      _ = -(ξ-(a : ℝ)/(b : ℝ))*(b : ℝ) := by field_simp [hbR.ne']; ring
      _ ≤ |ξ-(a : ℝ)/(b : ℝ)|*(b : ℝ) :=
        mul_le_mul_of_nonneg_right (neg_le_abs _) hbR.le

/-- Uniform separation for every bounded positive denominator, with no bound
on the numerator. This closes the finite-denominator gap in the cluster proof. -/
theorem bounded_denominator_separation (ξ : ℝ) (hξ : Irrational ξ) (B : ℕ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ a : ℤ, ∀ b : ℕ, 0 < b → b ≤ B →
      δ ≤ |ξ-(a : ℝ)/b| := by
  induction B with
  | zero =>
    refine ⟨1, by norm_num, ?_⟩
    intro a b hb hbB
    omega
  | succ B ih =>
    obtain ⟨δ, hδ, hold⟩ := ih
    obtain ⟨η, hη, hnew⟩ := fixed_denominator_separation ξ hξ (B+1) (by omega)
    refine ⟨min δ η, lt_min hδ hη, ?_⟩
    intro a b hb hbB
    by_cases hle : b ≤ B
    · exact (min_le_left _ _).trans (hold a b hb hle)
    · have heq : b = B+1 := by omega
      subst b
      exact (min_le_right _ _).trans (hnew a)

/-- An approximation measure and an actual upper-closeness estimate force
an exponential lower bound on the denominator. -/
theorem cluster_denominator_lower (ξ μ t : ℝ) (hμ : 0 < μ)
    (a : ℤ) (b : ℕ) (hb : 0 < b)
    (hmeasure : (b : ℝ)^(-μ) < |ξ-(a : ℝ)/b|)
    (hclose : |ξ-(a : ℝ)/b| ≤ Real.exp (-t)) :
    Real.exp (t/μ) < (b : ℝ) := by
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hexp := hmeasure.trans_le hclose
  rw [Real.rpow_def_of_pos hbR] at hexp
  have hlog := Real.exp_lt_exp.mp hexp
  have ht : t/μ < Real.log (b : ℝ) := (div_lt_iff₀ hμ).2 (by nlinarith)
  calc
    Real.exp (t/μ) < Real.exp (Real.log (b : ℝ)) := Real.exp_lt_exp.mpr ht
    _ = (b : ℝ) := Real.exp_log hbR

/-- Corrected 4.8(1): for every fixed positive cluster rate, sufficiently
small cluster disks exclude all small denominators, including those below
the onset of the eventual irrationality measure. Nothing is asserted for
roots outside this cluster. -/
theorem eventual_rational_cluster_exclusion (ξ μ τ : ℝ) (hμ : 0 < μ)
    (hτ : 0 < τ) (b₀ : ℕ)
    (hmeasure : ∀ a : ℤ, ∀ b : ℕ, 0 < b → b₀ ≤ b →
      (b : ℝ)^(-μ) < |ξ-(a : ℝ)/b|) :
    ∀ᶠ K : ℕ in atTop, ∀ a : ℤ, ∀ b : ℕ, 0 < b →
      |ξ-(a : ℝ)/b| ≤ Real.exp (-τ*(K : ℝ)) →
      Real.exp ((τ/μ)*(K : ℝ)) < (b : ℝ) := by
  have hξ := irrational_of_real_measure ξ μ b₀ hmeasure
  obtain ⟨δ, hδ, hsmall⟩ := bounded_denominator_separation ξ hξ b₀
  have ht : Tendsto (fun K : ℕ => τ*(K : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop hτ
  have he : Tendsto (fun K : ℕ => Real.exp (-τ*(K : ℝ))) atTop (𝓝 0) := by
    simpa only [neg_mul] using Real.tendsto_exp_neg_atTop_nhds_zero.comp ht
  filter_upwards [he.eventually (gt_mem_nhds hδ)] with K hK
  intro a b hb hclose
  have hb₀ : b₀ ≤ b := by
    by_contra hnot
    have hble : b ≤ b₀ := (lt_of_not_ge hnot).le
    have hh := hsmall a b hb hble
    linarith
  have h := cluster_denominator_lower ξ μ (τ*(K : ℝ)) hμ a b hb
    (hmeasure a b hb hb₀) (by simpa only [neg_mul] using hclose)
  convert h using 1 <;> congr 1 <;> ring

/-- The printed final rounding in 4.8(1) reverses the exponent comparison:
even a cluster rate 11.411 and measure exponent 25687 would yield a rate
strictly below 1/2251. The weaker rate 1/2252 is supported by that pair. -/
theorem paper_cluster_denominator_arithmetic :
    (1/2252 : ℚ) < (11411/1000 : ℚ)/25687 ∧
      (11411/1000 : ℚ)/25687 < (1/2251 : ℚ) := by
  norm_num

end LeanPaper.Section4RationalCluster

#print axioms LeanPaper.Section4RationalCluster.irrational_of_real_measure
#print axioms LeanPaper.Section4RationalCluster.fixed_denominator_separation
#print axioms LeanPaper.Section4RationalCluster.bounded_denominator_separation
#print axioms LeanPaper.Section4RationalCluster.cluster_denominator_lower
#print axioms LeanPaper.Section4RationalCluster.eventual_rational_cluster_exclusion
#print axioms LeanPaper.Section4RationalCluster.paper_cluster_denominator_arithmetic
