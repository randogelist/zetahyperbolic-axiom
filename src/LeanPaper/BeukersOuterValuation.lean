import LeanPaper.BeukersIntegralPencil
import Mathlib.NumberTheory.Padics.PadicVal.Basic

/-!
# Theorem 6.1(2): the actual outer-prime off-diagonal valuation

The harmonic difference has a unique denominator divisible by the outer
prime. Its valuation is proved from the actual finite sum, then the extra
divided-difference denominator supplies the seventh negative power.
No valuation or nonvanishing hypothesis on a moment is assumed.
-/

noncomputable section
open scoped BigOperators
open MeasureTheory

namespace ManuscriptChain.Beukers

lemma harmonic_difference_eq_shifted_sum (s r p : ℕ) :
    Real.harmonic s (r + p) - Real.harmonic s r =
      ∑ i ∈ Finset.range p, 1 / ((r + i + 1 : ℕ) : ℚ) ^ s := by
  unfold Real.harmonic
  rw [Finset.sum_range_add]
  ring

/-- A positive interval of length p crossing p has exactly one p-pole. -/
theorem harmonic_difference_outer_valuation (p r s : ℕ) [Fact p.Prime]
    (hr : r < p) (hs : 0 < s) :
    padicValRat p (Real.harmonic s (r + p) - Real.harmonic s r) = -(s : ℤ) := by
  classical
  have hp : p.Prime := Fact.out
  let F : ℕ → ℚ := fun i => 1 / ((r + i + 1 : ℕ) : ℚ) ^ s
  let j : ℕ := p - r - 1
  have hj : j ∈ Finset.range p := by
    apply Finset.mem_range.mpr
    dsimp [j]
    omega
  have hindex : r + j + 1 = p := by dsimp [j]; omega
  have hpos (i : ℕ) : 0 < F i := by dsimp [F]; positivity
  have hjval : padicValRat p (F j) = -(s : ℤ) := by
    dsimp [F]
    rw [hindex, one_div]
    exact padicValRat.self_pow_inv s
  have hother (i : ℕ) (hi : i ∈ (Finset.range p).erase j) :
      padicValRat p (F i) = 0 := by
    have hir : i < p := Finset.mem_range.mp (Finset.mem_of_mem_erase hi)
    have hij : i ≠ j := Finset.ne_of_mem_erase hi
    have hne : r + i + 1 ≠ p := by
      intro he
      apply hij
      dsimp [j]
      omega
    have hnd : ¬p ∣ r + i + 1 := by
      rintro ⟨k, hk⟩
      have hk2 : k < 2 := by
        apply (Nat.mul_lt_mul_left hp.pos).mp
        rw [← hk]
        omega
      have hk0 : k ≠ 0 := by
        intro hk0
        simp [hk0] at hk
      have hk1 : k = 1 := by omega
      apply hne
      simpa [hk1] using hk
    simp only [F, one_div, padicValRat.inv, padicValRat.pow,
      padicValRat.of_nat, padicValNat.eq_zero_of_not_dvd hnd,
      Nat.cast_zero, mul_zero, neg_zero]
  rw [harmonic_difference_eq_shifted_sum]
  change padicValRat p (∑ i ∈ Finset.range p, F i) = _
  rw [← Finset.sum_erase_add _ _ hj, add_comm]
  by_cases he : (Finset.range p).erase j = ∅
  · simpa [he] using hjval
  · have hnonempty := Finset.nonempty_iff_ne_empty.mpr he
    have hsumpos : 0 < ∑ i ∈ (Finset.range p).erase j, F i :=
      Finset.sum_pos (fun i _ => hpos i) hnonempty
    have hlt : padicValRat p (F j) <
        padicValRat p (∑ i ∈ (Finset.range p).erase j, F i) := by
      apply padicValRat.lt_sum_of_lt hnonempty
      · intro i hi
        rw [hjval, hother i hi]
        exact neg_neg_of_pos (by exact_mod_cast hs)
      · exact hpos
    rw [padicValRat.add_eq_of_lt
      (ne_of_gt (add_pos (hpos j) hsumpos)) (ne_of_gt (hpos j))
      (ne_of_gt hsumpos) hlt]
    exact hjval

/-- The actual rational moment of r and r+p has exact valuation -7. -/
theorem dualConstant_outer_valuation (p r : ℕ) [Fact p.Prime]
    (hp11 : 11 ≤ p) (hr : r < p) :
    padicValRat p (Real.dualConstant 7 r (r + p)) = -7 := by
  have hp : p.Prime := Fact.out
  have hpq : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hne : r ≠ r + p := by omega
  have hformula : Real.dualConstant 7 r (r + p) =
      (Real.harmonic 6 (r + p) - Real.harmonic 6 r) / (6 * (p : ℚ)) := by
    simp only [Real.dualConstant, hne, if_false]
    norm_num only [Nat.reduceSub, Nat.cast_ofNat]
    push_cast
    rw [show (r : ℚ) - ((r : ℚ) + (p : ℚ)) = -(p : ℚ) by ring,
      mul_neg, div_neg]
    ring
  have hval := harmonic_difference_outer_valuation p r 6 hr (by norm_num)
  have hnum : Real.harmonic 6 (r + p) - Real.harmonic 6 r ≠ 0 := by
    intro hz
    rw [hz, padicValRat.zero] at hval
    norm_num at hval
  have hp6 : ¬p ∣ 6 := Nat.not_dvd_of_pos_of_lt (by norm_num) (by omega)
  have hv6 : padicValRat p (6 : ℚ) = 0 := by
    change padicValRat p ((6 : ℕ) : ℚ) = 0
    rw [padicValRat.of_nat, padicValNat.eq_zero_of_not_dvd hp6]
    norm_num
  rw [hformula, padicValRat.div hnum (mul_ne_zero (by norm_num) hpq),
    padicValRat.mul (by norm_num : (6 : ℚ) ≠ 0) hpq,
    hv6, padicValRat.self hp.one_lt, hval]
  norm_num

/-- The original outer-window and congruence conditions force r₂=r₁+p. -/
lemma outer_congruent_indices (p K r₁ r₂ : ℕ)
    (hK : K < 2 * p) (h₁ : r₁ < p) (h₂ : p ≤ r₂) (h₂K : r₂ ≤ K)
    (hcong : Nat.ModEq p r₁ r₂) : r₂ = r₁ + p := by
  change r₁ % p = r₂ % p at hcong
  rw [Nat.mod_eq_of_lt h₁, Nat.mod_eq_sub_mod h₂,
    Nat.mod_eq_of_lt (show r₂ - p < p by omega)] at hcong
  omega

/-- Exact Theorem 6.1(2) off-diagonal valuation under its outer-range indices. -/
theorem theorem_6_1_offdiagonal_valuation (p K r₁ r₂ : ℕ) [Fact p.Prime]
    (hp11 : 11 ≤ p) (hK : K < 2 * p) (h₁ : r₁ < p)
    (h₂ : p ≤ r₂) (h₂K : r₂ ≤ K) (hcong : Nat.ModEq p r₁ r₂) :
    padicValRat p (Real.dualConstant 7 r₁ r₂) = -7 := by
  rw [outer_congruent_indices p K r₁ r₂ hK h₁ h₂ h₂K hcong]
  exact dualConstant_outer_valuation p r₁ hp11 h₁

/-- The valuation is attached to the actual square integral, not a formal symbol. -/
theorem actual_outer_moment_valuation (p K r₁ r₂ : ℕ) [Fact p.Prime]
    (hp11 : 11 ≤ p) (hK : K < 2 * p) (h₁ : r₁ < p)
    (h₂ : p ≤ r₂) (h₂K : r₂ ≤ K) (hcong : Nat.ModEq p r₁ r₂) :
    ∃ q : ℚ, (∫ z, z.1 ^ r₁ * z.2 ^ r₂ ∂beukersMeasure) = (q : ℝ) ∧
      padicValRat p q = -7 := by
  refine ⟨Real.dualConstant 7 r₁ r₂, ?_,
    theorem_6_1_offdiagonal_valuation p K r₁ r₂ hp11 hK h₁ h₂ h₂K hcong⟩
  rw [integral_beukersMeasure, moment_eq_dualConstant]
  have hne : r₁ ≠ r₂ := by omega
  simp only [hne, if_false, add_zero]

end ManuscriptChain.Beukers

#print axioms ManuscriptChain.Beukers.harmonic_difference_outer_valuation
#print axioms ManuscriptChain.Beukers.theorem_6_1_offdiagonal_valuation
#print axioms ManuscriptChain.Beukers.actual_outer_moment_valuation
