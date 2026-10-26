import LeanPaper.ImportedSection56.DualMoments
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic

/-!
# Theorem 6.2: exact common denominator of the rational dual moments

The common denominator is the least common multiple `d_K` of `1,...,K`.
The construction proves the exact `6*d_K^7` bound without postulating
integral moments. The separate two-variable integral realization is not
used or claimed by this arithmetic statement.
-/
noncomputable section
open Finset
namespace LeanPaper.BeukersDenominator
open ManuscriptChain.Real

def commonDenominator (K : ℕ) : ℕ := (Finset.range K).lcm (fun j => j+1)
def integerRationals : Subring ℚ := (Int.castRingHom ℚ).range

lemma commonDenominator_dvd {K n : ℕ} (hn : 0<n) (hK : n≤K) :
    n ∣ commonDenominator K := by
  simpa [commonDenominator, Nat.sub_add_cancel hn] using
    (Finset.dvd_lcm (f := fun j : ℕ => j+1)
      (Finset.mem_range.mpr (show n-1<K by omega)))

lemma commonDenominator_ne_zero (K : ℕ) : commonDenominator K ≠ 0 := by
  apply Finset.lcm_ne_zero_iff.mpr
  intro j hj
  omega

lemma nat_div_mem {d n : ℕ} (h : n∣d) : (d : ℚ)/n ∈ integerRationals := by
  refine ⟨(d/n : ℕ), ?_⟩
  change ((d/n : ℕ) : ℚ) = (d : ℚ)/n
  exact Rat.natCast_div d n h

lemma nat_mem (n : ℕ) : (n : ℚ) ∈ integerRationals := by
  exact ⟨(n : ℤ), by simp⟩

/-- Harmonic denominators require precisely the `s`-th power of `d_K`. -/
theorem harmonic_denominator (s K r : ℕ) (hr : r≤K) :
    (commonDenominator K : ℚ)^s * harmonic s r ∈ integerRationals := by
  unfold harmonic
  rw [Finset.mul_sum]
  apply Subring.sum_mem
  intro j hj
  have hdiv := commonDenominator_dvd (show 0<j+1 by omega)
    (show j+1≤K by have := Finset.mem_range.mp hj; omega)
  have h := Subring.pow_mem integerRationals (nat_div_mem hdiv) s
  simpa only [div_pow, mul_one_div] using h

lemma difference_div_mem (K r t : ℕ) (hr : r≤K) (ht : t≤K) (hne : r≠t) :
    (commonDenominator K : ℚ)/((r : ℚ)-t) ∈ integerRationals := by
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hd := commonDenominator_dvd (show 0<t-r by omega) (show t-r≤K by omega)
    have h := (integerRationals).neg_mem (nat_div_mem hd)
    have he : ((t-r : ℕ) : ℚ) = (t : ℚ)-r := by exact_mod_cast Nat.cast_sub hlt.le
    rw [he] at h
    have hsign : (r : ℚ)-t = -((t : ℚ)-r) := by ring
    rw [hsign, div_neg]
    exact h
  · have hd := commonDenominator_dvd (show 0<r-t by omega) (show r-t≤K by omega)
    have h := nat_div_mem hd
    have he : ((r-t : ℕ) : ℚ) = (r : ℚ)-t := by exact_mod_cast Nat.cast_sub hgt.le
    simpa only [he] using h

/-- The extra divided-difference denominator costs exactly one additional power. -/
theorem harmonic_difference_denominator (s K r t : ℕ)
    (hr : r≤K) (ht : t≤K) (hne : r≠t) :
    (commonDenominator K : ℚ)^(s+1) *
      ((harmonic s r-harmonic s t)/((r : ℚ)-t)) ∈ integerRationals := by
  have h₁ := (integerRationals).sub_mem
    (harmonic_denominator s K r hr) (harmonic_denominator s K t ht)
  have h₂ := difference_div_mem K r t hr ht hne
  have h := (integerRationals).mul_mem h₁ h₂
  convert h using 1 <;> simp [pow_succ] <;> ring

/-- Every rational weight-seven moment has the printed common denominator. -/
theorem dualConstant_seven_denominator (K r t : ℕ) (hr : r≤K) (ht : t≤K) :
    6*(commonDenominator K : ℚ)^7 * dualConstant 7 r t ∈ integerRationals := by
  by_cases he : r=t
  · subst t
    simp only [dualConstant, ↓reduceIte]
    have h := (integerRationals).mul_mem (nat_mem 6)
      ((integerRationals).neg_mem (harmonic_denominator 7 K r hr))
    convert h using 1 <;> ring
  · simp only [dualConstant, if_neg he]
    have h := harmonic_difference_denominator 6 K r t hr ht he
    norm_num only [Nat.reduceSub, Nat.cast_ofNat] at *
    convert h using 1 <;> field_simp <;> ring

/-- The adjacent off-diagonal value in Theorem 6.2(1) is exact. -/
theorem adjacent_dualConstant (m : ℕ) :
    dualConstant 7 m (m+1) = 1/(6*((m+1 : ℕ) : ℚ)^6) := by
  have hne : m≠m+1 := by omega
  simp only [dualConstant, if_neg hne, harmonic, Finset.sum_range_succ]
  push_cast
  field_simp
  <;> ring

end LeanPaper.BeukersDenominator
