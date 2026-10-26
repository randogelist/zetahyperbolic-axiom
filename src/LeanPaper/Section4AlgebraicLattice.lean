import LeanPaper.Section4AlgebraicLimsup

/-! # Proposition 4.2 on the manuscript lattice

This wrapper has the original real-valued evaluation hypotheses, arbitrary
positive lattice spacing, finite upper limsup of normalized logarithmic
height, and the printed exponent lambda*rho*d/(epsilon-(d-1)*Lambda).
Every algebraic approximant is represented by its irreducible integer minimal
polynomial and its chosen complex root, with the actual coefficient height.
-/
noncomputable section
open Filter Topology Polynomial
namespace LeanPaper.Section4AlgebraicLattice
open Section4Resultant Section4AlgebraicTransfer Section4AlgebraicLimsup
open ManuscriptChain.RealTransfer

/-- The full arithmetic conclusion of Proposition 4.2, uniformly for every
irreducible integer-polynomial representation of an algebraic number. -/
theorem proposition_4_2
    (Q : ℕ → ℤ[X]) (d0 d : ℕ) (hd0 : 0 < d0) (hd : 1 ≤ d)
    (ξ lam ε ρ Λ μ : ℝ) (hlam : 0 < lam) (hρ : 0 < ρ)
    (hgap : ((d-1 : ℕ) : ℝ)*Λ < ε)
    (hμ : lam*ρ*(d : ℝ)/(ε-((d-1 : ℕ) : ℝ)*Λ) < μ)
    (hdegree : ∀ᶠ n : ℕ in atTop, ((Q (d0*n)).natDegree : ℝ) ≤ lam*(d0*n : ℕ))
    (hvalues : ∀ᶠ n : ℕ in atTop, 0 < |evalReal (Q (d0*n)) ξ| ∧
      |evalReal (Q (d0*n)) ξ| ≤ Real.exp (-ε*((d0*n : ℕ) : ℝ)^2))
    (hroots : ∀ᶠ n : ℕ in atTop, ∀ r ∈ (complexPolynomial (Q (d0*n))).roots,
      Real.exp (-ρ*(d0*n : ℕ)) ≤ ‖(ξ : ℂ)-r‖)
    (hheight : Filter.limsup
      (fun n => ((Real.log (naiveHeight (Q (d0*n)))/((d0*n : ℕ) : ℝ)^2 : ℝ) : EReal))
      atTop ≤ (Λ : EReal)) :
    ∃ B₀ : ℕ, ∀ f : ℤ[X], Irreducible (rationalPolynomial f) →
      f.natDegree ≤ d → (B₀ : ℝ) ≤ naiveHeight f →
      ∀ α : ℂ, (complexPolynomial f).eval α = 0 →
        (naiveHeight f)^(-μ) < ‖(ξ : ℂ)-α‖ := by
  have hD : (0 : ℝ) < d0 := by exact_mod_cast hd0
  have hD2 : (0 : ℝ) < (d0 : ℝ)^2 := sq_pos_of_pos hD
  have hQ : ∀ᶠ n : ℕ in atTop, Q (d0*n) ≠ 0 := by
    filter_upwards [hvalues] with n hn
    intro hz
    simp [hz, evalReal] at hn
  have hgap' : ((d-1 : ℕ) : ℝ)*(Λ*(d0 : ℝ)^2) < ε*(d0 : ℝ)^2 := by
    nlinarith [mul_lt_mul_of_pos_right hgap hD2]
  have hrate : (lam*d0)*(ρ*d0)*(d : ℝ)/
      (ε*(d0 : ℝ)^2-((d-1 : ℕ) : ℝ)*(Λ*(d0 : ℝ)^2)) =
      lam*ρ*(d : ℝ)/(ε-((d-1 : ℕ) : ℝ)*Λ) := by
    rw [show ε*(d0 : ℝ)^2-((d-1 : ℕ) : ℝ)*(Λ*(d0 : ℝ)^2) =
      (ε-((d-1 : ℕ) : ℝ)*Λ)*(d0 : ℝ)^2 by ring]
    field_simp
    <;> ring
  apply algebraic_transfer_upperHeight (fun n => Q (d0*n)) d hd ξ
    (lam*d0) (ε*(d0 : ℝ)^2) (ρ*d0) (Λ*(d0 : ℝ)^2) μ
    (by positivity) (by positivity) hgap' (by simpa only [hrate] using hμ)
  · filter_upwards [hdegree] with n hn
    simpa only [Nat.cast_mul, mul_assoc] using hn
  · filter_upwards [hvalues] with n hn
    rw [complex_norm_eval_real]
    convert hn using 1 <;> push_cast <;> ring
  · filter_upwards [hroots] with n hn
    simpa only [Nat.cast_mul, mul_assoc, neg_mul] using hn
  · intro L hL
    have hLL : Λ < L/(d0 : ℝ)^2 := (lt_div_iff₀ hD2).2 hL
    have hIL : ∀ᶠ n : ℕ in atTop, 0 < d0*n := by
      filter_upwards [eventually_gt_atTop 0] with n hn
      exact Nat.mul_pos hd0 hn
    have hh := eventual_height_of_limsup (fun n => Q (d0*n)) (fun n => d0*n)
      Λ (L/(d0 : ℝ)^2) hIL hQ hheight hLL
    filter_upwards [hh] with n hn
    convert hn using 1
    congr 1
    push_cast
    field_simp

#print axioms proposition_4_2
end LeanPaper.Section4AlgebraicLattice
