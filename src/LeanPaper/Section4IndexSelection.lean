import Theorem_4_1_Spectral_Irrationality_Measure_Criterion
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Topology.Algebra.Order.Floor

/-!
# Constructed logarithmic index budgets for Section 4

The index is the actual lattice point d0 * floor(c * log b / d0).
This file supplies the asymptotic index-selection obligation of the spectral
transfer criterion. It does not supply the paper's family-specific decay or
spectral estimates, or a computable modulus for an unspecified eventual bound.
-/
noncomputable section
open Filter Topology
namespace LeanPaper.Section4IndexSelection

def gridIndex (d0 : ℕ) (c : ℝ) (b : ℕ) : ℕ :=
  d0 * ⌊c * Real.log (b : ℝ) / d0⌋₊

theorem gridIndex_dvd (d0 : ℕ) (c : ℝ) (b : ℕ) : d0 ∣ gridIndex d0 c b :=
  ⟨_, rfl⟩

theorem gridIndex_bounds (d0 : ℕ) (hd0 : 0 < d0) (c : ℝ) (hc : 0 < c)
    (b : ℕ) (hb : 0 < b) :
    (gridIndex d0 c b : ℝ) ≤ c * Real.log b ∧
      c * Real.log b < (gridIndex d0 c b : ℝ) + d0 := by
  have hd : (0 : ℝ) < d0 := by exact_mod_cast hd0
  have hlog : 0 ≤ Real.log (b : ℝ) := Real.log_nonneg (by exact_mod_cast (Nat.succ_le_iff.mpr hb))
  have hx : 0 ≤ c * Real.log (b : ℝ) / d0 := by positivity
  have hl := Nat.floor_le hx
  have hu := Nat.lt_floor_add_one (c * Real.log (b : ℝ) / d0)
  dsimp [gridIndex]
  push_cast
  constructor
  · have h := (le_div_iff₀ hd).mp hl
    nlinarith
  · have h := (div_lt_iff₀ hd).mp hu
    nlinarith

theorem gridIndex_tendsto (d0 : ℕ) (hd0 : 0 < d0) (c : ℝ) (hc : 0 < c) :
    Tendsto (gridIndex d0 c) atTop atTop := by
  apply tendsto_atTop.2
  intro N
  have ht : Tendsto (fun b : ℕ => c * Real.log (b : ℝ)) atTop atTop :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).const_mul_atTop hc
  filter_upwards [ht.eventually_ge_atTop ((N : ℝ) + d0), eventually_gt_atTop 0] with b hb hb0
  have hu := (gridIndex_bounds d0 hd0 c hc b hb0).2
  have : (N : ℝ) ≤ gridIndex d0 c b := by linarith
  exact_mod_cast this

/-- A polynomial prefactor is absorbed with any strictly positive exponential
margin. No unproved asymptotic comparison is passed as a premise. -/
theorem eventually_radius_budget (d : ℕ → ℕ) (lam ρ σ : ℝ)
    (hlam : 0 ≤ lam) (hgap : ρ < σ)
    (hdeg : ∀ᶠ K : ℕ in atTop, (d K : ℝ) ≤ lam * K) :
    ∀ᶠ K : ℕ in atTop,
      Real.exp (-σ * K) ≤
        ManuscriptChain.Spectral.comparisonRadius (d K) (Real.exp (ρ * K)) := by
  have hg : 0 < σ - ρ := sub_pos.mpr hgap
  have ht1 : Tendsto (fun K : ℕ => (K : ℝ) * Real.exp (-(σ - ρ) * K)) atTop (𝓝 0) := by
    simpa only [Real.rpow_one] using
      (Real.tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 (σ - ρ) hg).comp
        tendsto_natCast_atTop_atTop
  have ht0 : Tendsto (fun K : ℕ => Real.exp (-(σ - ρ) * K)) atTop (𝓝 0) := by
    simpa only [neg_mul] using Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (tendsto_natCast_atTop_atTop.const_mul_atTop hg)
  have ht : Tendsto (fun K : ℕ => 8 * ((lam * K + 1) * Real.exp (-(σ - ρ) * K)))
      atTop (𝓝 0) := by
    convert ((ht1.const_mul lam).add ht0).const_mul 8 using 1
    · ext K
      ring
    · simp
  filter_upwards [hdeg, ht.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))] with K hK hsmall
  unfold ManuscriptChain.Spectral.comparisonRadius
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < 8 * ((d K : ℝ) + 1) * Real.exp (ρ * K))).2
  have he : Real.exp (-σ * (K : ℝ)) * Real.exp (ρ * K) =
      Real.exp (-(σ - ρ) * K) := by rw [← Real.exp_add]; congr 1; ring
  calc
    Real.exp (-σ * K) * (8 * ((d K : ℝ) + 1) * Real.exp (ρ * K))
        = 8 * ((d K : ℝ) + 1) * Real.exp (-(σ - ρ) * K) := by rw [← he]; ring
    _ ≤ 8 * (lam * K + 1) * Real.exp (-(σ - ρ) * K) := by gcongr
    _ ≤ 1 := by linarith

/-- For a positive quadratic decay gap, the denominator cost at the chosen
logarithmic index tends to zero. -/
theorem eventually_denominator_budget (d : ℕ → ℕ) (d0 : ℕ) (hd0 : 0 < d0)
    (lam ε c : ℝ) (hlam : 0 ≤ lam) (hc : 0 < c) (hgap : lam / c < ε)
    (hdeg : ∀ᶠ K : ℕ in atTop, (d K : ℝ) ≤ lam * K) :
    ∀ᶠ b : ℕ in atTop,
      2 * (b : ℝ) ^ d (gridIndex d0 c b) *
        Real.exp (-ε * (gridIndex d0 c b : ℝ) ^ 2) < 1 := by
  let a := ε - lam / c
  have ha : 0 < a := sub_pos.mpr hgap
  have htK := gridIndex_tendsto d0 hd0 c hc
  have hquadratic : ∀ᶠ K : ℕ in atTop,
      lam / c * (K : ℝ) * (K + d0) - ε * K ^ 2 ≤ -(K : ℝ) := by
    filter_upwards [eventually_ge_atTop (⌈(lam / c * d0 + 1) / a⌉₊)] with K hK
    have hbound : (lam / c * d0 + 1) / a ≤ (K : ℝ) :=
      (Nat.le_ceil _).trans (by exact_mod_cast hK)
    have hbound' := (div_le_iff₀ ha).mp hbound
    have hm := mul_le_mul_of_nonneg_right hbound' (Nat.cast_nonneg K : (0 : ℝ) ≤ K)
    dsimp [a] at hm
    nlinarith
  have hsmall : ∀ᶠ K : ℕ in atTop, 2 * Real.exp (-(K : ℝ)) < 1 :=
    ((Real.tendsto_exp_neg_atTop_nhds_zero.comp tendsto_natCast_atTop_atTop).const_mul 2).eventually
      (by simpa using gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [eventually_gt_atTop 0, htK.eventually hdeg,
    htK.eventually hquadratic, htK.eventually hsmall] with b hb hdegB hquadB hsmallB
  set K := gridIndex d0 c b
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hlog : 0 ≤ Real.log (b : ℝ) := Real.log_nonneg (by exact_mod_cast (Nat.succ_le_iff.mpr hb))
  have hupper : Real.log (b : ℝ) ≤ ((K : ℝ) + d0) / c := by
    apply (le_div_iff₀ hc).2
    have := (gridIndex_bounds d0 hd0 c hc b hb).2
    dsimp [K]
    nlinarith
  have hexponent : (d K : ℝ) * Real.log (b : ℝ) - ε * (K : ℝ) ^ 2 ≤ -(K : ℝ) := by
    have h1 := mul_le_mul_of_nonneg_right hdegB hlog
    have h2 := mul_le_mul_of_nonneg_left hupper (mul_nonneg hlam (Nat.cast_nonneg K))
    have heq : lam * (K : ℝ) * (((K : ℝ) + d0) / c) = lam / c * K * (K + d0) := by ring
    rw [heq] at h2
    nlinarith
  calc
    2 * (b : ℝ) ^ d K * Real.exp (-ε * (K : ℝ) ^ 2)
        = 2 * Real.exp ((d K : ℝ) * Real.log b - ε * (K : ℝ) ^ 2) := by
          rw [sub_eq_add_neg, Real.exp_add, Real.exp_nat_mul, Real.exp_log hbR]
          ring
    _ ≤ 2 * Real.exp (-(K : ℝ)) := by gcongr
    _ < 1 := hsmallB

/-- The former `IndexBudget` input is now constructed from the rate gaps.
The positive lattice spacing is arbitrary. -/
theorem exists_indexBudget_of_rates
    (Q : ℕ → Polynomial ℤ) (n₀ μ d0 : ℕ) (hd0 : 0 < d0)
    (lam ε ρ c σ : ℝ) (hlam : 0 ≤ lam) (hc : 0 < c) (hσ : 0 < σ)
    (hdecay : lam / c < ε) (hρσ : ρ < σ) (hμ : σ * c ≤ (μ : ℝ))
    (hdegree : ∀ᶠ K : ℕ in atTop, ((Q K).natDegree : ℝ) ≤ lam * K) :
    ∃ b₀ : ℕ, ManuscriptChain.RealTransfer.IndexBudget Q
      (fun K => ManuscriptChain.Spectral.comparisonRadius (Q K).natDegree
        (Real.exp (ρ * K)))
      (fun K => Real.exp (-ε * (K : ℝ) ^ 2)) n₀ μ b₀ := by
  have ht := gridIndex_tendsto d0 hd0 c hc
  have hrad := eventually_radius_budget (fun K => (Q K).natDegree) lam ρ σ hlam hρσ hdegree
  have hbud := eventually_denominator_budget (fun K => (Q K).natDegree) d0 hd0
    lam ε c hlam hc hdecay hdegree
  have hall : ∀ᶠ b : ℕ in atTop, n₀ ≤ gridIndex d0 c b ∧
      Real.exp (-σ * gridIndex d0 c b) ≤
        ManuscriptChain.Spectral.comparisonRadius (Q (gridIndex d0 c b)).natDegree
          (Real.exp (ρ * gridIndex d0 c b)) ∧
      2 * (b : ℝ) ^ (Q (gridIndex d0 c b)).natDegree *
        Real.exp (-ε * (gridIndex d0 c b : ℝ) ^ 2) < 1 :=
    (ht.eventually_ge_atTop n₀).and ((ht.eventually hrad).and hbud)
  obtain ⟨b₀, hb₀⟩ := eventually_atTop.1 hall
  refine ⟨b₀, ⟨?_⟩⟩
  intro b hb hbb
  obtain ⟨hn, hr, hd⟩ := hb₀ b hbb
  refine ⟨gridIndex d0 c b, hn, ?_, hd⟩
  apply le_trans _ hr
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hlog : 0 ≤ Real.log (b : ℝ) := Real.log_nonneg (by exact_mod_cast (Nat.succ_le_iff.mpr hb))
  have hK := (gridIndex_bounds d0 hd0 c hc b hb).1
  have hσK := mul_le_mul_of_nonneg_left hK hσ.le
  have hμlog := mul_le_mul_of_nonneg_right hμ hlog
  have hexp : -(μ : ℝ) * Real.log b ≤ -σ * (gridIndex d0 c b : ℝ) := by nlinarith
  calc
    1 / (b : ℝ) ^ μ = Real.exp (-(μ : ℝ) * Real.log b) := by
      rw [neg_mul, Real.exp_neg, Real.exp_nat_mul, Real.exp_log hbR, one_div]
    _ ≤ Real.exp (-σ * gridIndex d0 c b) := Real.exp_le_exp.mpr hexp

/-- Rational approximation transfer with the logarithmic index obligation
fully discharged. The actual local comparison and decay hypotheses retain
exactly their explicit mathematical content. -/
theorem measure_of_rates
    (Q : ℕ → Polynomial ℤ) (ξ : ℝ) (n₀ μ d0 : ℕ) (hd0 : 0 < d0)
    (lam ε ρ c σ : ℝ) (hlam : 0 ≤ lam) (hc : 0 < c) (hσ : 0 < σ)
    (hdecay : lam / c < ε) (hρσ : ρ < σ) (hμ : σ * c ≤ (μ : ℝ))
    (hdegree : ∀ᶠ K : ℕ in atTop, ((Q K).natDegree : ℝ) ≤ lam * K)
    (hcomparison : ManuscriptChain.RealTransfer.LocalComparison Q ξ
      (fun K => ManuscriptChain.Spectral.comparisonRadius (Q K).natDegree
        (Real.exp (ρ * K))) n₀)
    (hvalues : ManuscriptChain.RealTransfer.Decay Q ξ
      (fun K => Real.exp (-ε * (K : ℝ) ^ 2)) n₀) :
    ∃ b₀ : ℕ, ManuscriptChain.RealTransfer.RationalMeasure ξ μ b₀ := by
  obtain ⟨b₀, hbudget⟩ := exists_indexBudget_of_rates Q n₀ μ d0 hd0
    lam ε ρ c σ hlam hc hσ hdecay hρσ hμ hdegree
  exact ⟨b₀, ManuscriptChain.RealTransfer.conditional_measure hcomparison hvalues hbudget⟩

#print axioms exists_indexBudget_of_rates
#print axioms measure_of_rates

end LeanPaper.Section4IndexSelection
