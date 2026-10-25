import LeanPaper.Section4IndexSelection
import LeanPaper.Section4ComplexComparison

/-!
# Section 4.1: transfer with no assumed index budget

For arbitrary integer-polynomial families, quadratic nonzero decay and
exponential separation of every complex root yield the printed irrationality
exponent lambda*rho/epsilon, for every real exponent above it. The threshold
is existential; effective computability requires effective onsets for the
input eventual estimates.
-/
noncomputable section
open Filter Topology Polynomial
open ManuscriptChain.RealTransfer
namespace LeanPaper.Section4TransferComplete
open Section4IndexSelection Section4ComplexComparison

theorem spectral_transfer_real_exponent
    (Q : ℕ → ℤ[X]) (ξ lam ε ρ μ : ℝ)
    (hlam : 0 < lam) (hε : 0 < ε) (hρ : 0 < ρ)
    (hμ : lam * ρ / ε < μ)
    (hdegree : ∀ᶠ K : ℕ in atTop, ((Q K).natDegree : ℝ) ≤ lam * K)
    (hvalues : ∀ᶠ K : ℕ in atTop,
      evalReal (Q K) ξ ≠ 0 ∧ |evalReal (Q K) ξ| ≤ Real.exp (-ε * (K : ℝ)^2))
    (hroots : ∀ᶠ K : ℕ in atTop,
      ∀ r ∈ ((Q K).map (algebraMap ℤ ℂ)).roots,
        Real.exp (-ρ * K) ≤ ‖(ξ : ℂ) - r‖) :
    ∃ b₀ : ℕ, ∀ a : ℤ, ∀ b : ℕ, 0 < b → b₀ ≤ b →
      (b : ℝ) ^ (-μ) < |ξ - (a : ℝ) / b| := by
  have hinter : lam / ε < μ / ρ :=
    (div_lt_div_iff₀ hε hρ).2 ((div_lt_iff₀ hε).1 hμ)
  obtain ⟨c, hcL, hcR⟩ := exists_between hinter
  have hc : 0 < c := (div_pos hlam hε).trans hcL
  have hdecay : lam / c < ε := by
    apply (div_lt_iff₀ hc).2
    have h := (div_lt_iff₀ hε).1 hcL
    nlinarith
  have hρc : ρ < μ / c := by
    apply (lt_div_iff₀ hc).2
    have h := (lt_div_iff₀ hρ).1 hcR
    nlinarith
  obtain ⟨σ, hσL, hσR⟩ := exists_between hρc
  have hσ : 0 < σ := hρ.trans hσL
  have hσc : σ * c ≤ μ := ((lt_div_iff₀ hc).1 hσR).le
  have hindex := gridIndex_tendsto 1 (by omega) c hc
  have hrad := eventually_radius_budget (fun K => (Q K).natDegree) lam ρ σ
    hlam.le hσL hdegree
  have hbud := eventually_denominator_budget (fun K => (Q K).natDegree) 1
    (by omega) lam ε c hlam.le hc hdecay hdegree
  have hall : ∀ᶠ b : ℕ in atTop,
      (evalReal (Q (gridIndex 1 c b)) ξ ≠ 0 ∧
        |evalReal (Q (gridIndex 1 c b)) ξ| ≤ Real.exp (-ε * (gridIndex 1 c b : ℝ)^2)) ∧
      (∀ r ∈ ((Q (gridIndex 1 c b)).map (algebraMap ℤ ℂ)).roots,
        Real.exp (-ρ * gridIndex 1 c b) ≤ ‖(ξ : ℂ) - r‖) ∧
      Real.exp (-σ * gridIndex 1 c b) ≤
        ManuscriptChain.Spectral.comparisonRadius (Q (gridIndex 1 c b)).natDegree
          (Real.exp (ρ * gridIndex 1 c b)) ∧
      2 * (b : ℝ) ^ (Q (gridIndex 1 c b)).natDegree *
        Real.exp (-ε * (gridIndex 1 c b : ℝ)^2) < 1 :=
    (hindex.eventually hvalues).and ((hindex.eventually hroots).and
      ((hindex.eventually hrad).and hbud))
  obtain ⟨b₀, hb₀⟩ := eventually_atTop.1 hall
  refine ⟨b₀, ?_⟩
  intro a b hb hbb
  obtain ⟨⟨hne, hval⟩, hsep, hradius, hbudget⟩ := hb₀ b hbb
  set K := gridIndex 1 c b
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hlog : 0 ≤ Real.log (b : ℝ) := Real.log_nonneg (by exact_mod_cast (Nat.succ_le_iff.mpr hb))
  have hK := (gridIndex_bounds 1 (by omega) c hc b hb).1
  have hσK := mul_le_mul_of_nonneg_left hK hσ.le
  have hμlog := mul_le_mul_of_nonneg_right hσc hlog
  have hexp : Real.log b * (-μ) ≤ -σ * (K : ℝ) := by dsimp [K]; nlinarith
  have hpow : (b : ℝ)^(-μ) ≤ Real.exp (-σ * K) := by
    rw [Real.rpow_def_of_pos hbR]
    exact Real.exp_le_exp.mpr hexp
  by_contra hn
  have hclose : |(a : ℝ)/b - ξ| ≤
      ManuscriptChain.Spectral.comparisonRadius (Q K).natDegree (Real.exp (ρ * K)) := by
    rw [abs_sub_comm]
    exact (le_of_not_gt hn).trans (hpow.trans hradius)
  obtain ⟨hqx, hbound⟩ := integer_comparison (Q K) ξ ((a : ℝ)/b) ρ K hne hsep hclose
  apply polynomial_integer_squeeze (Q K) a b hb hqx
  calc
    (b : ℝ)^(Q K).natDegree * |evalReal (Q K) ((a : ℝ)/b)|
        ≤ (b : ℝ)^(Q K).natDegree * (2 * |evalReal (Q K) ξ|) := by gcongr
    _ ≤ (b : ℝ)^(Q K).natDegree * (2 * Real.exp (-ε * (K : ℝ)^2)) := by gcongr
    _ = 2 * (b : ℝ)^(Q K).natDegree * Real.exp (-ε * (K : ℝ)^2) := by ring
    _ < 1 := hbudget

/-- The paper's family indexed by positive multiples of an arbitrary fixed
integer `d0`. This reindexing preserves the exponent lambda*rho/epsilon. -/
theorem spectral_transfer_lattice
    (Q : ℕ → ℤ[X]) (d0 : ℕ) (hd0 : 0 < d0) (ξ lam ε ρ μ : ℝ)
    (hlam : 0 < lam) (hε : 0 < ε) (hρ : 0 < ρ)
    (hμ : lam * ρ / ε < μ)
    (hdegree : ∀ᶠ n : ℕ in atTop,
      ((Q (d0*n)).natDegree : ℝ) ≤ lam * (d0*n : ℕ))
    (hvalues : ∀ᶠ n : ℕ in atTop,
      evalReal (Q (d0*n)) ξ ≠ 0 ∧
      |evalReal (Q (d0*n)) ξ| ≤ Real.exp (-ε * ((d0*n : ℕ) : ℝ)^2))
    (hroots : ∀ᶠ n : ℕ in atTop,
      ∀ r ∈ ((Q (d0*n)).map (algebraMap ℤ ℂ)).roots,
        Real.exp (-ρ * (d0*n : ℕ)) ≤ ‖(ξ : ℂ) - r‖) :
    ∃ b₀ : ℕ, ∀ a : ℤ, ∀ b : ℕ, 0 < b → b₀ ≤ b →
      (b : ℝ) ^ (-μ) < |ξ - (a : ℝ) / b| := by
  have hd : (0 : ℝ) < d0 := by exact_mod_cast hd0
  have hrate : (lam * d0) * (ρ * d0) / (ε * (d0 : ℝ)^2) = lam*ρ/ε := by
    field_simp
    <;> ring
  apply spectral_transfer_real_exponent (fun n => Q (d0*n)) ξ
    (lam*d0) (ε*(d0 : ℝ)^2) (ρ*d0) μ (by positivity) (by positivity) (by positivity)
    (by simpa only [hrate] using hμ)
  · filter_upwards [hdegree] with n hn
    simpa only [Nat.cast_mul, mul_assoc] using hn
  · filter_upwards [hvalues] with n hn
    convert hn using 1 <;> push_cast <;> ring
  · filter_upwards [hroots] with n hn
    simpa only [Nat.cast_mul, mul_assoc, neg_mul] using hn

#print axioms spectral_transfer_lattice

#print axioms spectral_transfer_real_exponent
end LeanPaper.Section4TransferComplete
