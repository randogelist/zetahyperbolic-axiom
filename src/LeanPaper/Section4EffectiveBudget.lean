import LeanPaper.Section4ComplexComparison
import LeanPaper.Section4IndexSelection
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Data.Rat.Floor

/-!
# Explicit threshold with effective input data

The printed effectiveness clause requires certified rational rate data and a
known onset. The natural-number threshold below is computed using rational
arithmetic, ceilings, maxima and an integer power; no real logarithm or
exponential occurs in its definition. The proof may of course use real analysis.
-/
open Polynomial
namespace LeanPaper.Section4EffectiveBudget

def indexThreshold (n₀ : ℕ) (lam ε ρ c σ : ℚ) : ℕ :=
  max n₀ (max 2 (max ⌈(lam/c + 1)/(ε-lam/c)⌉₊ ⌈16*(lam+1)/(σ-ρ)^2⌉₊))

def denominatorThreshold (n₀ : ℕ) (lam ε ρ c σ : ℚ) : ℕ :=
  3 ^ ⌈((indexThreshold n₀ lam ε ρ c σ : ℚ)+1)/c⌉₊ + 1

noncomputable section
open ManuscriptChain.RealTransfer Section4IndexSelection Section4ComplexComparison

private theorem rational_exp_le_pow_three (t : ℚ) :
    Real.exp (t : ℝ) ≤ ((3 : ℕ)^⌈t⌉₊ : ℕ) := by
  have ht : (t : ℝ) ≤ (⌈t⌉₊ : ℕ) := by exact_mod_cast (Nat.le_ceil t)
  calc
    Real.exp (t : ℝ) ≤ Real.exp ((⌈t⌉₊ : ℕ) : ℝ) := Real.exp_le_exp.mpr ht
    _ = (Real.exp 1)^⌈t⌉₊ := by simpa using Real.exp_nat_mul 1 (⌈t⌉₊)
    _ ≤ (3 : ℝ)^⌈t⌉₊ := pow_le_pow_left₀ (Real.exp_pos _).le Real.exp_one_lt_three.le _
    _ = _ := by push_cast; rfl

/-- The explicit threshold puts the selected logarithmic index beyond every
required polynomial/exponential absorption bound. -/
theorem index_above_threshold (n₀ : ℕ) (lam ε ρ c σ : ℚ) (hc : 0 < c)
    (b : ℕ) (hb : denominatorThreshold n₀ lam ε ρ c σ ≤ b) :
    indexThreshold n₀ lam ε ρ c σ ≤ gridIndex 1 (c : ℝ) b := by
  let N := indexThreshold n₀ lam ε ρ c σ
  have hbpos : 0 < b := by
    have : 0 < denominatorThreshold n₀ lam ε ρ c σ := by unfold denominatorThreshold; omega
    omega
  have hbR : (0 : ℝ) < b := by exact_mod_cast hbpos
  have hcR : (0 : ℝ) < c := by exact_mod_cast hc
  have he := rational_exp_le_pow_three (((N : ℚ)+1)/c)
  have hpow : (((3 : ℕ)^⌈((N : ℚ)+1)/c⌉₊ : ℕ) : ℝ) ≤ b := by
    exact_mod_cast (show (3 : ℕ)^⌈((N : ℚ)+1)/c⌉₊ ≤ b by
      change 3 ^ ⌈((N : ℚ)+1)/c⌉₊ + 1 ≤ b at hb
      omega)
  have hlog : ((N : ℝ)+1)/(c : ℝ) ≤ Real.log b := by
    apply (Real.le_log_iff_exp_le hbR).2
    exact (by simpa using he).trans hpow
  have hmul := (div_le_iff₀ hcR).1 hlog
  have hu := (gridIndex_bounds 1 (by omega) c hcR b hbpos).2
  have hn : (N : ℝ) ≤ gridIndex 1 (c : ℝ) b := by norm_num at hu; nlinarith
  exact_mod_cast hn

/-- Both numerical budgets are certified at the explicit index threshold. -/
theorem explicit_budgets (n₀ μ : ℕ) (lam ε ρ c σ : ℚ)
    (hlam : 0 ≤ lam) (hc : 0 < c) (hσ : 0 < σ)
    (hgap : lam/c < ε) (hr : ρ < σ) (hμ : σ*c ≤ μ)
    (b d : ℕ) (hb : denominatorThreshold n₀ lam ε ρ c σ ≤ b)
    (hd : (d : ℝ) ≤ (lam : ℝ) * gridIndex 1 (c : ℝ) b) :
    1/(b : ℝ)^μ ≤ ManuscriptChain.Spectral.comparisonRadius d
        (Real.exp ((ρ : ℝ)*gridIndex 1 (c : ℝ) b)) ∧
      2*(b : ℝ)^d * Real.exp (-(ε : ℝ)*(gridIndex 1 (c : ℝ) b : ℝ)^2) < 1 := by
  let K := gridIndex 1 (c : ℝ) b
  have hNK := index_above_threshold n₀ lam ε ρ c σ hc b hb
  have hK0 : 2 ≤ K := by
    have h : 2 ≤ indexThreshold n₀ lam ε ρ c σ := by unfold indexThreshold; omega
    exact h.trans hNK
  have hb0 : 0 < b := by
    have h : 0 < denominatorThreshold n₀ lam ε ρ c σ := by unfold denominatorThreshold; omega
    omega
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb0
  have hcR : (0 : ℝ) < c := by exact_mod_cast hc
  have hσR : (0 : ℝ) < σ := by exact_mod_cast hσ
  have hlamR : (0 : ℝ) ≤ lam := by exact_mod_cast hlam
  have hgR : 0 < (σ : ℝ)-ρ := by exact_mod_cast (sub_pos.mpr hr)
  have haR : 0 < (ε : ℝ)-lam/c := by exact_mod_cast (sub_pos.mpr hgap)
  have hμR : (σ : ℝ)*c ≤ μ := by exact_mod_cast hμ
  have hK2 : (2 : ℝ) ≤ K := by exact_mod_cast hK0
  have hlog := Real.log_nonneg (show (1 : ℝ) ≤ b by exact_mod_cast (Nat.succ_le_iff.mpr hb0))
  have hbounds := gridIndex_bounds 1 (by omega) c hcR b hb0
  have hceil1 : ⌈(lam/c+1)/(ε-lam/c)⌉₊ ≤ K := by
    have h : ⌈(lam/c+1)/(ε-lam/c)⌉₊ ≤ indexThreshold n₀ lam ε ρ c σ := by unfold indexThreshold; omega
    exact h.trans hNK
  have hceil2 : ⌈16*(lam+1)/(σ-ρ)^2⌉₊ ≤ K := by
    have h : ⌈16*(lam+1)/(σ-ρ)^2⌉₊ ≤ indexThreshold n₀ lam ε ρ c σ := by unfold indexThreshold; omega
    exact h.trans hNK
  have ht1 : ((lam : ℝ)/c+1)/((ε : ℝ)-lam/c) ≤ K := by
    exact_mod_cast (Nat.le_ceil ((lam/c+1)/(ε-lam/c))).trans (by exact_mod_cast hceil1)
  have ht2 : 16*((lam : ℝ)+1)/((σ : ℝ)-ρ)^2 ≤ K := by
    exact_mod_cast (Nat.le_ceil (16*(lam+1)/(σ-ρ)^2)).trans (by exact_mod_cast hceil2)
  have ht1' := (div_le_iff₀ haR).1 ht1
  have ht2' := (div_le_iff₀ (sq_pos_of_pos hgR)).1 ht2
  have hm1 := mul_le_mul_of_nonneg_right ht1' (show (0 : ℝ) ≤ K by positivity)
  have hm2 := mul_le_mul_of_nonneg_right ht2' (show (0 : ℝ) ≤ K by positivity)
  have he := Real.pow_div_factorial_le_exp
    (show 0 ≤ ((σ : ℝ)-ρ)*(K : ℝ) by positivity) 2
  norm_num at he
  have hexp : 8*((d : ℝ)+1) ≤ Real.exp (((σ : ℝ)-ρ)*K) := by
    have hlamK := mul_le_mul_of_nonneg_left (show (1 : ℝ) ≤ K by linarith) (hlamR.add (by norm_num))
    nlinarith
  have hradius : Real.exp (-(σ : ℝ)*K) ≤
      ManuscriptChain.Spectral.comparisonRadius d (Real.exp ((ρ : ℝ)*K)) := by
    unfold ManuscriptChain.Spectral.comparisonRadius
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < 8*((d : ℝ)+1)*Real.exp ((ρ : ℝ)*K))).2
    have hprod : Real.exp (-(σ : ℝ)*K) * Real.exp ((ρ : ℝ)*K) =
        (Real.exp (((σ : ℝ)-ρ)*K))⁻¹ := by rw [← Real.exp_add, ← Real.exp_neg]; congr 1; ring
    have hx : 8*((d : ℝ)+1) / Real.exp (((σ : ℝ)-ρ)*K) ≤ 1 :=
      (div_le_one (Real.exp_pos _)).2 hexp
    calc
      _ = 8*((d : ℝ)+1) / Real.exp (((σ : ℝ)-ρ)*K) := by rw [div_eq_mul_inv, ← hprod]; ring
      _ ≤ 1 := hx
  constructor
  · apply le_trans _ hradius
    have hσK := mul_le_mul_of_nonneg_left hbounds.1 hσR.le
    have hμlog := mul_le_mul_of_nonneg_right hμR hlog
    have hx : -(μ : ℝ)*Real.log b ≤ -(σ : ℝ)*K := by dsimp [K]; nlinarith
    rw [one_div, ← Real.exp_log (pow_pos hbR μ), Real.log_pow, ← Real.exp_neg]
    exact Real.exp_le_exp.mpr (by simpa only [neg_mul] using hx)
  · have hupper : Real.log (b : ℝ) ≤ ((K : ℝ)+1)/(c : ℝ) := by
      apply (le_div_iff₀ hcR).2
      have := hbounds.2
      dsimp [K]
      norm_num at this
      nlinarith
    have h1 := mul_le_mul_of_nonneg_right hd hlog
    have h2 := mul_le_mul_of_nonneg_left hupper (mul_nonneg hlamR (Nat.cast_nonneg K))
    have heq : (lam : ℝ)*K*(((K : ℝ)+1)/c) = ((lam : ℝ)/c)*K*(K+1) := by ring
    rw [heq] at h2
    have hneg : (d : ℝ)*Real.log b -(ε : ℝ)*(K : ℝ)^2 ≤ -(K : ℝ) := by nlinarith
    have htwo : 2 * Real.exp (-(K : ℝ)) < 1 := by
      have hh : 2 < Real.exp (K : ℝ) := by linarith [Real.add_one_le_exp (K : ℝ)]
      rw [Real.exp_neg, ← div_eq_mul_inv]
      exact (div_lt_one (Real.exp_pos _)).2 hh
    calc
      2*(b : ℝ)^d * Real.exp (-(ε : ℝ)*(K : ℝ)^2)
          = 2*Real.exp ((d : ℝ)*Real.log b -(ε : ℝ)*(K : ℝ)^2) := by
            rw [sub_eq_add_neg, Real.exp_add, Real.exp_nat_mul, Real.exp_log hbR]; ring
      _ ≤ 2*Real.exp (-(K : ℝ)) := by gcongr
      _ < 1 := htwo

/-- Correct effective version with explicit rational rates and a certified
onset. The threshold is the computable natural definition above. -/
theorem effective_spectral_measure
    (Q : ℕ → ℤ[X]) (ξ : ℝ) (n₀ μ : ℕ) (lam ε ρ c σ : ℚ)
    (hlam : 0 ≤ lam) (hc : 0 < c) (hσ : 0 < σ)
    (hgap : lam/c < ε) (hr : ρ < σ) (hμ : σ*c ≤ μ)
    (hdegree : ∀ K, n₀ ≤ K → ((Q K).natDegree : ℝ) ≤ (lam : ℝ)*K)
    (hvalues : ∀ K, n₀ ≤ K → evalReal (Q K) ξ ≠ 0 ∧
      |evalReal (Q K) ξ| ≤ Real.exp (-(ε : ℝ)*(K : ℝ)^2))
    (hroots : ∀ K, n₀ ≤ K → ∀ r ∈ ((Q K).map (algebraMap ℤ ℂ)).roots,
      Real.exp (-(ρ : ℝ)*K) ≤ ‖(ξ : ℂ)-r‖) :
    RationalMeasure ξ μ (denominatorThreshold n₀ lam ε ρ c σ) := by
  intro a b hb hbb
  let K := gridIndex 1 (c : ℝ) b
  have hK : n₀ ≤ K := by
    have hn : n₀ ≤ indexThreshold n₀ lam ε ρ c σ := Nat.le_max_left _ _
    exact hn.trans (index_above_threshold n₀ lam ε ρ c σ hc b hbb)
  obtain ⟨hradius, hbudget⟩ := explicit_budgets n₀ μ lam ε ρ c σ
    hlam hc hσ hgap hr hμ b (Q K).natDegree hbb (hdegree K hK)
  obtain ⟨hne, hvalue⟩ := hvalues K hK
  by_contra hnot
  have hclose : |(a : ℝ)/b - ξ| ≤
      ManuscriptChain.Spectral.comparisonRadius (Q K).natDegree (Real.exp ((ρ : ℝ)*K)) := by
    rw [abs_sub_comm]
    exact (le_of_not_gt hnot).trans hradius
  obtain ⟨hqx, hcomp⟩ := integer_comparison (Q K) ξ ((a : ℝ)/b) ρ K hne (hroots K hK) hclose
  apply polynomial_integer_squeeze (Q K) a b hb hqx
  calc
    (b : ℝ)^(Q K).natDegree * |evalReal (Q K) ((a : ℝ)/b)|
        ≤ (b : ℝ)^(Q K).natDegree * (2*|evalReal (Q K) ξ|) := by gcongr
    _ ≤ (b : ℝ)^(Q K).natDegree * (2*Real.exp (-(ε : ℝ)*(K : ℝ)^2)) := by gcongr
    _ = 2*(b : ℝ)^(Q K).natDegree * Real.exp (-(ε : ℝ)*(K : ℝ)^2) := by ring
    _ < 1 := hbudget

/-- A rational margin choice for the manuscript exponent. This proves the
parameter arithmetic, not the missing family-specific bounds. -/
theorem manuscript_effective_rate_margins :
    (9/10 : ℚ) / 2251 < 1/2500 ∧
    (11411/1000 : ℚ) < 114113/10000 ∧
    (114113/10000 : ℚ)*2251 ≤ 25687 := by norm_num

#print axioms explicit_budgets
#print axioms effective_spectral_measure

end LeanPaper.Section4EffectiveBudget
