import LeanPaper.Section4AlgebraicLattice
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

/-! # Constructed naive height of an algebraic number

Clear the denominators of the rational minimal polynomial, then remove its
integer content. The resulting primitive polynomial has the same degree and
root. The final transfer corollary therefore quantifies directly over all
algebraic complex numbers, using their extension degree and naive height.
-/
noncomputable section
open Polynomial Filter Topology
namespace ManuscriptChain.Section4AlgebraicHeight
open LeanPaper.Section4Resultant LeanPaper.Section4AlgebraicLattice

/-- A primitive integer minimal polynomial, unique up to sign. -/
def integerMinimalPolynomial (α : ℂ) : ℤ[X] :=
  (IsLocalization.integerNormalization (nonZeroDivisors ℤ) (minpoly ℚ α)).primPart

def algebraicHeight (α : ℂ) : ℝ := naiveHeight (integerMinimalPolynomial α)

theorem integerMinimalPolynomial_spec (α : ℂ) (hα : IsAlgebraic ℚ α) :
    (integerMinimalPolynomial α).IsPrimitive ∧
    Irreducible (rationalPolynomial (integerMinimalPolynomial α)) ∧
    (complexPolynomial (integerMinimalPolynomial α)).eval α = 0 ∧
    (integerMinimalPolynomial α).natDegree = (minpoly ℚ α).natDegree := by
  let g : ℤ[X] := IsLocalization.integerNormalization (nonZeroDivisors ℤ) (minpoly ℚ α)
  have hmin := minpoly.irreducible hα.isIntegral
  obtain ⟨c,hc0,hc⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors ℤ) (minpoly ℚ α)
  have hcne : c ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hc0
  have hcQ : (c : ℚ) ≠ 0 := by exact_mod_cast hcne
  have hcmap : rationalPolynomial g = C (c : ℚ)*minpoly ℚ α := by
    simpa only [rationalPolynomial, g, Algebra.smul_def, Polynomial.algebraMap_apply, eq_intCast, Polynomial.C_eq_intCast] using hc
  have hcu : IsUnit (C (c : ℚ) : ℚ[X]) := Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr hcQ)
  have hgi : Irreducible (rationalPolynomial g) := by
    rw [hcmap]
    exact (irreducible_isUnit_mul hcu).mpr hmin
  have hg0 : g ≠ 0 := by intro hz; simp [rationalPolynomial,hz] at hgi
  have hcont0 : g.content ≠ 0 := fun hz => hg0 (Polynomial.content_eq_zero_iff.mp hz)
  have hcontQ : (g.content : ℚ) ≠ 0 := by exact_mod_cast hcont0
  have hcu' : IsUnit (C (g.content : ℚ) : ℚ[X]) :=
    Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr hcontQ)
  have hfac : rationalPolynomial g = C (g.content : ℚ)*rationalPolynomial g.primPart := by
    conv_lhs => rw [g.eq_C_content_mul_primPart]
    simp only [rationalPolynomial, Polynomial.map_mul, Polynomial.map_C, eq_intCast,
      Polynomial.map_intCast, Polynomial.C_eq_intCast]
  have hfi : Irreducible (rationalPolynomial g.primPart) := by
    rw [hfac] at hgi
    exact (irreducible_isUnit_mul hcu').mp hgi
  have hgeval : (complexPolynomial g).eval α = 0 := by
    rw [← complexPolynomial_from_rational, Polynomial.eval_map_algebraMap, hcmap,
      map_mul, Polynomial.aeval_C, minpoly.aeval, mul_zero]
  have hfeval : (complexPolynomial g.primPart).eval α = 0 := by
    simp only [complexPolynomial, Polynomial.eval_map] at hgeval ⊢
    apply Polynomial.eval₂_primPart_eq_zero
      (show Function.Injective (algebraMap ℤ ℂ) from Int.cast_injective) hg0
    exact hgeval
  have hdegree : g.primPart.natDegree = (minpoly ℚ α).natDegree := by
    rw [g.natDegree_primPart]
    have hn : (rationalPolynomial g).natDegree = g.natDegree :=
      Polynomial.natDegree_map_eq_of_injective
        (show Function.Injective (algebraMap ℤ ℚ) from Int.cast_injective) _
    rw [← hn, hcmap, Polynomial.natDegree_C_mul hcQ]
  exact ⟨g.isPrimitive_primPart,hfi,hfeval,hdegree⟩

/-- The constructed degree is exactly the extension degree `[Q(alpha):Q]`. -/
theorem integerMinimalPolynomial_degree (α : ℂ) (hα : IsAlgebraic ℚ α) :
    (integerMinimalPolynomial α).natDegree =
      Module.finrank ℚ (IntermediateField.adjoin ℚ {α}) := by
  rw [(integerMinimalPolynomial_spec α hα).2.2.2]
  exact (IntermediateField.adjoin.finrank hα.isIntegral).symm

/-- Proposition 4.2 directly for algebraic numbers, their extension degrees,
and the naive height of their constructed primitive integer minimal polynomial. -/
theorem proposition_4_2_algebraic_numbers
    (Q : ℕ → ℤ[X]) (d0 d : ℕ) (hd0 : 0 < d0) (hd : 1 ≤ d)
    (ξ lam ε ρ Λ μ : ℝ) (hlam : 0 < lam) (hρ : 0 < ρ)
    (hgap : ((d-1 : ℕ) : ℝ)*Λ < ε)
    (hμ : lam*ρ*(d : ℝ)/(ε-((d-1 : ℕ) : ℝ)*Λ) < μ)
    (hdegree : ∀ᶠ n : ℕ in atTop, ((Q (d0*n)).natDegree : ℝ) ≤ lam*(d0*n : ℕ))
    (hvalues : ∀ᶠ n : ℕ in atTop, 0 < |ManuscriptChain.RealTransfer.evalReal (Q (d0*n)) ξ| ∧
      |ManuscriptChain.RealTransfer.evalReal (Q (d0*n)) ξ| ≤ Real.exp (-ε*((d0*n : ℕ) : ℝ)^2))
    (hroots : ∀ᶠ n : ℕ in atTop, ∀ r ∈ (complexPolynomial (Q (d0*n))).roots,
      Real.exp (-ρ*(d0*n : ℕ)) ≤ ‖(ξ : ℂ)-r‖)
    (hheight : Filter.limsup
      (fun n => ((Real.log (naiveHeight (Q (d0*n)))/((d0*n : ℕ) : ℝ)^2 : ℝ) : EReal))
      atTop ≤ (Λ : EReal)) :
    ∃ B₀ : ℕ, ∀ α : ℂ, IsAlgebraic ℚ α →
      Module.finrank ℚ (IntermediateField.adjoin ℚ {α}) ≤ d →
      (B₀ : ℝ) ≤ algebraicHeight α →
      (algebraicHeight α)^(-μ) < ‖(ξ : ℂ)-α‖ := by
  obtain ⟨B₀,hB₀⟩ := proposition_4_2 Q d0 d hd0 hd ξ lam ε ρ Λ μ
    hlam hρ hgap hμ hdegree hvalues hroots hheight
  refine ⟨B₀,?_⟩
  intro α hα hdegreeα hheightα
  obtain ⟨hprim,hirr,hroot,hdeg⟩ := integerMinimalPolynomial_spec α hα
  apply hB₀ (integerMinimalPolynomial α) hirr _ hheightα α hroot
  rw [integerMinimalPolynomial_degree α hα]
  exact hdegreeα

#print axioms proposition_4_2_algebraic_numbers

#print axioms integerMinimalPolynomial_spec
#print axioms integerMinimalPolynomial_degree
end ManuscriptChain.Section4AlgebraicHeight
