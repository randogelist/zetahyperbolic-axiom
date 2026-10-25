import LeanPaper.Section4AlgebraicBudget
import LeanPaper.Section4ComplexComparison

/-! # Proposition 4.2: transfer to algebraic approximants

Approximants are represented by an actual integer polynomial irreducible over
Q together with its complex root. Requiring primitivity is unnecessary for the
proved bound; in particular the statement applies to the primitive minimal
polynomial whose coefficient height is the manuscript's naive height.
-/
noncomputable section
open Filter Topology Polynomial
namespace LeanPaper.Section4AlgebraicTransfer
open Section4Resultant Section4ConjugateBounds Section4IndexSelection
open Section4AlgebraicBudget Section4ComplexComparison

lemma complex_norm_eval_real (P : ℤ[X]) (x : ℝ) :
    ‖(complexPolynomial P).eval (x : ℂ)‖ =
      |ManuscriptChain.RealTransfer.evalReal P x| := by
  have hmap : (P.map (algebraMap ℤ ℝ)).map Complex.ofRealHom = complexPolynomial P := by
    rw [complexPolynomial, Polynomial.map_map]
    congr 1
  have he : ((P.map (algebraMap ℤ ℝ)).map Complex.ofRealHom).eval (x : ℂ) =
      (ManuscriptChain.RealTransfer.evalReal P x : ℂ) :=
    Polynomial.eval_map_apply Complex.ofRealHom x
  rw [← hmap, he]
  exact Complex.norm_real _

/-- Algebraic approximation transfer with an explicit eventual height rate.
The conclusion is uniform over every irreducible approximation polynomial of
bounded degree, not a hypothesis about its resultant. -/
theorem algebraic_transfer_rates
    (Q : ℕ → ℤ[X]) (d : ℕ) (ξ lam ε ρ L μ : ℝ)
    (hlam : 0 < lam) (hρ : 0 < ρ) (hL : 0 ≤ L)
    (hgap : ((d-1 : ℕ) : ℝ)*L < ε)
    (hμ : lam*ρ/(ε-((d-1 : ℕ) : ℝ)*L) < μ)
    (hdegree : ∀ᶠ K : ℕ in atTop, ((Q K).natDegree : ℝ) ≤ lam*K)
    (hvalues : ∀ᶠ K : ℕ in atTop,
      0 < ‖(complexPolynomial (Q K)).eval (ξ : ℂ)‖ ∧
      ‖(complexPolynomial (Q K)).eval (ξ : ℂ)‖ ≤ Real.exp (-ε*(K : ℝ)^2))
    (hroots : ∀ᶠ K : ℕ in atTop, ∀ r ∈ (complexPolynomial (Q K)).roots,
      Real.exp (-ρ*K) ≤ ‖(ξ : ℂ)-r‖)
    (hheight : ∀ᶠ K : ℕ in atTop, naiveHeight (Q K) ≤ Real.exp (L*(K : ℝ)^2)) :
    ∃ B₀ : ℕ, ∀ f : ℤ[X], Irreducible (rationalPolynomial f) →
      f.natDegree ≤ d → (B₀ : ℝ) ≤ naiveHeight f →
      ∀ α : ℂ, (complexPolynomial f).eval α = 0 →
        (naiveHeight f)^(-μ) < ‖(ξ : ℂ)-α‖ := by
  have hg : 0 < ε-((d-1 : ℕ) : ℝ)*L := sub_pos.mpr hgap
  have hint : lam/(ε-((d-1 : ℕ) : ℝ)*L) < μ/ρ :=
    (div_lt_div_iff₀ hg hρ).2 ((div_lt_iff₀ hg).1 hμ)
  obtain ⟨c, hcL, hcR⟩ := exists_between hint
  have hc : 0 < c := (div_pos hlam hg).trans hcL
  have hdecay : ((d-1 : ℕ) : ℝ)*L+lam/c < ε := by
    have hh := (div_lt_iff₀ hg).1 hcL
    have hh' : lam/c < ε-((d-1 : ℕ) : ℝ)*L :=
      (div_lt_iff₀ hc).2 (by nlinarith)
    linarith
  have hρc : ρ < μ/c := by
    apply (lt_div_iff₀ hc).2
    have hh := (lt_div_iff₀ hρ).1 hcR
    nlinarith
  obtain ⟨σ, hσL, hσR⟩ := exists_between hρc
  have hσ : 0 < σ := hρ.trans hσL
  have hσc : σ*c ≤ μ := ((lt_div_iff₀ hc).1 hσR).le
  have hindex := gridIndex_tendsto 1 (by omega) c hc
  have hradius := eventually_radius_budget (fun K => (Q K).natDegree) lam ρ σ
    hlam.le hσL hdegree
  have hbudget := eventually_conjugate_budget Q d lam ε L c hlam.le hL hc hdecay hdegree hheight
  have hall : ∀ᶠ B : ℕ in atTop,
      (0 < ‖(complexPolynomial (Q (gridIndex 1 c B))).eval (ξ : ℂ)‖ ∧
        ‖(complexPolynomial (Q (gridIndex 1 c B))).eval (ξ : ℂ)‖ ≤
          Real.exp (-ε*(gridIndex 1 c B : ℝ)^2)) ∧
      (∀ r ∈ (complexPolynomial (Q (gridIndex 1 c B))).roots,
        Real.exp (-ρ*gridIndex 1 c B) ≤ ‖(ξ : ℂ)-r‖) ∧
      Real.exp (-σ*gridIndex 1 c B) ≤
        ManuscriptChain.Spectral.comparisonRadius (Q (gridIndex 1 c B)).natDegree
          (Real.exp (ρ*gridIndex 1 c B)) ∧
      (∀ m : ℕ, m ≤ d →
        2*Real.exp (-ε*(gridIndex 1 c B : ℝ)^2) *
          ((((Q (gridIndex 1 c B)).natDegree : ℝ)+1)*naiveHeight (Q (gridIndex 1 c B)))^(m-1) *
          (Real.sqrt ((m : ℝ)+1)*(B : ℝ))^(Q (gridIndex 1 c B)).natDegree < 1) :=
    (hindex.eventually hvalues).and ((hindex.eventually hroots).and
      ((hindex.eventually hradius).and hbudget))
  obtain ⟨B₀,hB₀⟩ := eventually_atTop.1 hall
  refine ⟨max 1 B₀, ?_⟩
  intro f hf hfd hfheight α hα
  obtain ⟨B,hB⟩ := naiveHeight_is_nat f
  have hBlarge : max 1 B₀ ≤ B := by rw [hB] at hfheight; exact_mod_cast hfheight
  have hBpos : 0 < B := by omega
  have hBR : (0 : ℝ) < B := by exact_mod_cast hBpos
  obtain ⟨⟨hQpos,hQval⟩,hsep,hrad,hbud⟩ := hB₀ B (by omega)
  let K := gridIndex 1 c B
  have hlog := Real.log_nonneg (show (1 : ℝ) ≤ B by exact_mod_cast (Nat.succ_le_iff.mpr hBpos))
  have hK := (gridIndex_bounds 1 (by omega) c hc B hBpos).1
  have hσK := mul_le_mul_of_nonneg_left hK hσ.le
  have hμlog := mul_le_mul_of_nonneg_right hσc hlog
  have hpow : (B : ℝ)^(-μ) ≤ Real.exp (-σ*K) := by
    rw [Real.rpow_def_of_pos hBR]
    apply Real.exp_le_exp.mpr
    dsimp [K]
    nlinarith
  by_contra hnot
  have hclose : ‖α-(ξ : ℂ)‖ ≤
      Real.exp (-ρ*K)/(8*(((complexPolynomial (Q K)).natDegree : ℝ)+1)) := by
    rw [norm_sub_rev]
    have hnat : (complexPolynomial (Q K)).natDegree = (Q K).natDegree :=
      Polynomial.natDegree_map_eq_of_injective
        (show Function.Injective (algebraMap ℤ ℂ) from Int.cast_injective) _
    rw [hnat]
    have heq : Real.exp (-ρ*K)/(8*(((Q K).natDegree : ℝ)+1)) =
        ManuscriptChain.Spectral.comparisonRadius (Q K).natDegree (Real.exp (ρ*K)) := by
      unfold ManuscriptChain.Spectral.comparisonRadius
      rw [neg_mul, Real.exp_neg]
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    rw [heq]
    rw [hB] at hnot
    exact (le_of_not_gt hnot).trans (hpow.trans hrad)
  obtain ⟨hQα,hcomp⟩ := polynomial_comparison (complexPolynomial (Q K)) ξ α
    (Real.exp (-ρ*K)) (Real.exp_pos _) (norm_pos_iff.mp hQpos) hsep hclose
  have hlower := algebraic_approximation_barrier f (Q K) α hf hα hQα
  have hHnon : 0 ≤ naiveHeight (Q K) := (complexPolynomial (Q K)).supNorm_nonneg
  have hu : ‖(complexPolynomial (Q K)).eval α‖ ≤ 2*Real.exp (-ε*(K : ℝ)^2) :=
    hcomp.trans (mul_le_mul_of_nonneg_left hQval (by norm_num))
  have hupper : ‖(complexPolynomial (Q K)).eval α‖ *
      ((((Q K).natDegree : ℝ)+1)*naiveHeight (Q K))^(f.natDegree-1) *
      (Real.sqrt ((f.natDegree : ℝ)+1)*naiveHeight f)^(Q K).natDegree < 1 := by
    rw [hB]
    apply lt_of_le_of_lt _ (hbud f.natDegree hfd)
    gcongr
  exact (not_lt_of_ge hlower) hupper

#print axioms algebraic_transfer_rates
end LeanPaper.Section4AlgebraicTransfer
