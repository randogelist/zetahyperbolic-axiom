import LeanPaper.Section4AlgebraicTransfer
import Mathlib.Topology.Instances.EReal.Lemmas

/-! # The complete limsup height hypothesis of Proposition 4.2

The extended-real limsup expresses the manuscript's finite upper limsup without
the default-value convention of an unbounded real supremum. The natural number
height is constructed from the coefficients, and the approximation statement
is uniform over all integer minimal-polynomial representatives.
-/
noncomputable section
open Filter Topology Polynomial
namespace LeanPaper.Section4AlgebraicLimsup
open Section4Resultant Section4ConjugateBounds Section4AlgebraicTransfer

/-- The upper-limsup growth assertion in eventual-bound form. -/
def UpperQuadraticHeight (Q : ℕ → ℤ[X]) (Λ : ℝ) : Prop :=
  ∀ L : ℝ, Λ < L → ∀ᶠ K : ℕ in atTop, naiveHeight (Q K) ≤ Real.exp (L*(K : ℝ)^2)

lemma eventual_height_of_limsup (Q : ℕ → ℤ[X]) (I : ℕ → ℕ) (Λ L : ℝ)
    (hIL : ∀ᶠ n : ℕ in atTop, 0 < I n)
    (hQ : ∀ᶠ n : ℕ in atTop, Q n ≠ 0)
    (hh : Filter.limsup (fun n => ((Real.log (naiveHeight (Q n))/(I n : ℝ)^2 : ℝ) : EReal))
      atTop ≤ (Λ : EReal)) (hL : Λ < L) :
    ∀ᶠ n : ℕ in atTop, naiveHeight (Q n) ≤ Real.exp (L*(I n : ℝ)^2) := by
  have hlim : Filter.limsup (fun n => ((Real.log (naiveHeight (Q n))/(I n : ℝ)^2 : ℝ) : EReal))
      atTop < (L : EReal) := hh.trans_lt (by exact_mod_cast hL)
  have hb := eventually_lt_of_limsup_lt hlim
  filter_upwards [hIL,hQ,hb] with n hIn hQn hbn
  have hi : (0 : ℝ) < I n := by exact_mod_cast hIn
  have hH : 0 < naiveHeight (Q n) := lt_of_lt_of_le (by norm_num) (one_le_naiveHeight _ hQn)
  have he : Real.log (naiveHeight (Q n))/(I n : ℝ)^2 < L := by exact_mod_cast hbn
  have hlog : Real.log (naiveHeight (Q n)) ≤ L*(I n : ℝ)^2 :=
    ((div_lt_iff₀ (sq_pos_of_pos hi)).1 he).le
  rw [← Real.exp_log hH]
  exact Real.exp_le_exp.mpr hlog

lemma upperHeight_of_limsup (Q : ℕ → ℤ[X]) (Λ : ℝ)
    (hQ : ∀ᶠ K : ℕ in atTop, Q K ≠ 0)
    (hh : Filter.limsup (fun K => ((Real.log (naiveHeight (Q K))/(K : ℝ)^2 : ℝ) : EReal))
      atTop ≤ (Λ : EReal)) : UpperQuadraticHeight Q Λ := by
  intro L hL
  exact eventual_height_of_limsup Q id Λ L (eventually_gt_atTop 0) hQ hh hL

lemma upperHeight_nonneg (Q : ℕ → ℤ[X]) (Λ : ℝ)
    (hQ : ∀ᶠ K : ℕ in atTop, Q K ≠ 0)
    (hh : UpperQuadraticHeight Q Λ) : 0 ≤ Λ := by
  by_contra hn
  have hn' : Λ < 0 := lt_of_not_ge hn
  obtain ⟨K,hK,hQK,hHK⟩ := ((eventually_gt_atTop 0).and (hQ.and (hh (Λ/2) (by linarith)))).exists
  have hKR : (0 : ℝ) < K := by exact_mod_cast hK
  have hneg : Λ/2*(K : ℝ)^2 < 0 := mul_neg_of_neg_of_pos (by linarith) (sq_pos_of_pos hKR)
  have hlt : naiveHeight (Q K) < 1 := hHK.trans_lt (by simpa using Real.exp_lt_exp.mpr hneg)
  exact (not_lt_of_ge (one_le_naiveHeight _ hQK)) hlt

/-- The manuscript exponent, with its full upper-height-limsup content. -/
theorem algebraic_transfer_upperHeight
    (Q : ℕ → ℤ[X]) (d : ℕ) (hd : 1 ≤ d) (ξ lam ε ρ Λ μ : ℝ)
    (hlam : 0 < lam) (hρ : 0 < ρ)
    (hgap : ((d-1 : ℕ) : ℝ)*Λ < ε)
    (hμ : lam*ρ*(d : ℝ)/(ε-((d-1 : ℕ) : ℝ)*Λ) < μ)
    (hdegree : ∀ᶠ K : ℕ in atTop, ((Q K).natDegree : ℝ) ≤ lam*K)
    (hvalues : ∀ᶠ K : ℕ in atTop,
      0 < ‖(complexPolynomial (Q K)).eval (ξ : ℂ)‖ ∧
      ‖(complexPolynomial (Q K)).eval (ξ : ℂ)‖ ≤ Real.exp (-ε*(K : ℝ)^2))
    (hroots : ∀ᶠ K : ℕ in atTop, ∀ r ∈ (complexPolynomial (Q K)).roots,
      Real.exp (-ρ*K) ≤ ‖(ξ : ℂ)-r‖)
    (hheight : UpperQuadraticHeight Q Λ) :
    ∃ B₀ : ℕ, ∀ f : ℤ[X], Irreducible (rationalPolynomial f) →
      f.natDegree ≤ d → (B₀ : ℝ) ≤ naiveHeight f →
      ∀ α : ℂ, (complexPolynomial f).eval α = 0 →
        (naiveHeight f)^(-μ) < ‖(ξ : ℂ)-α‖ := by
  have hQ : ∀ᶠ K : ℕ in atTop, Q K ≠ 0 := by
    filter_upwards [hvalues] with K hK
    intro hz
    simp [hz, complexPolynomial] at hK
  have hΛ := upperHeight_nonneg Q Λ hQ hheight
  have hg : 0 < ε-((d-1 : ℕ) : ℝ)*Λ := sub_pos.mpr hgap
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hμ' : lam*ρ/(ε-((d-1 : ℕ) : ℝ)*Λ) < μ := by
    apply lt_of_le_of_lt _ hμ
    exact div_le_div_of_nonneg_right (by nlinarith [mul_pos hlam hρ]) hg.le
  have hμpos : 0 < μ := (div_pos (mul_pos hlam hρ) hg).trans hμ'
  have hfrac : lam*ρ/μ < ε-((d-1 : ℕ) : ℝ)*Λ := by
    apply (div_lt_iff₀ hμpos).2
    have hh := (div_lt_iff₀ hg).1 hμ'
    nlinarith
  have hfracpos : 0 < lam*ρ/μ := div_pos (mul_pos hlam hρ) hμpos
  obtain ⟨L,hL,hLg,hLμ⟩ : ∃ L : ℝ, Λ < L ∧
      ((d-1 : ℕ) : ℝ)*L < ε ∧ lam*ρ/(ε-((d-1 : ℕ) : ℝ)*L) < μ := by
    by_cases hd1 : d=1
    · refine ⟨Λ+1, by linarith, ?_, ?_⟩
      · simpa [hd1] using hgap
      · simpa [hd1] using hμ'
    · have hD : (0 : ℝ) < ((d-1 : ℕ) : ℝ) := by exact_mod_cast (show 0 < d-1 by omega)
      have hinterval : Λ < (ε-lam*ρ/μ)/((d-1 : ℕ) : ℝ) :=
        (lt_div_iff₀ hD).2 (by nlinarith)
      obtain ⟨L,hL,hLU⟩ := exists_between hinterval
      have hDL := (lt_div_iff₀ hD).1 hLU
      have hLg : ((d-1 : ℕ) : ℝ)*L < ε := by nlinarith
      refine ⟨L,hL,hLg,?_⟩
      apply (div_lt_iff₀ (sub_pos.mpr hLg)).2
      have hh : lam*ρ/μ < ε-((d-1 : ℕ) : ℝ)*L := by nlinarith
      have hh' := (div_lt_iff₀ hμpos).1 hh
      nlinarith
  exact algebraic_transfer_rates Q d ξ lam ε ρ L μ hlam hρ (hΛ.trans hL.le)
    hLg hLμ hdegree hvalues hroots (hheight L hL)

/-- Proposition 4.2 for its actual finite upper limsup. -/
theorem algebraic_transfer_limsup
    (Q : ℕ → ℤ[X]) (d : ℕ) (hd : 1 ≤ d) (ξ lam ε ρ Λ μ : ℝ)
    (hlam : 0 < lam) (hρ : 0 < ρ)
    (hgap : ((d-1 : ℕ) : ℝ)*Λ < ε)
    (hμ : lam*ρ*(d : ℝ)/(ε-((d-1 : ℕ) : ℝ)*Λ) < μ)
    (hdegree : ∀ᶠ K : ℕ in atTop, ((Q K).natDegree : ℝ) ≤ lam*K)
    (hvalues : ∀ᶠ K : ℕ in atTop,
      0 < ‖(complexPolynomial (Q K)).eval (ξ : ℂ)‖ ∧
      ‖(complexPolynomial (Q K)).eval (ξ : ℂ)‖ ≤ Real.exp (-ε*(K : ℝ)^2))
    (hroots : ∀ᶠ K : ℕ in atTop, ∀ r ∈ (complexPolynomial (Q K)).roots,
      Real.exp (-ρ*K) ≤ ‖(ξ : ℂ)-r‖)
    (hheight : Filter.limsup (fun K => ((Real.log (naiveHeight (Q K))/(K : ℝ)^2 : ℝ) : EReal))
      atTop ≤ (Λ : EReal)) :
    ∃ B₀ : ℕ, ∀ f : ℤ[X], Irreducible (rationalPolynomial f) →
      f.natDegree ≤ d → (B₀ : ℝ) ≤ naiveHeight f →
      ∀ α : ℂ, (complexPolynomial f).eval α = 0 →
        (naiveHeight f)^(-μ) < ‖(ξ : ℂ)-α‖ := by
  apply algebraic_transfer_upperHeight Q d hd ξ lam ε ρ Λ μ hlam hρ hgap hμ hdegree hvalues hroots
  apply upperHeight_of_limsup Q Λ _ hheight
  filter_upwards [hvalues] with K hK
  intro hz
  simp [hz, complexPolynomial] at hK

#print axioms algebraic_transfer_limsup
end LeanPaper.Section4AlgebraicLimsup
