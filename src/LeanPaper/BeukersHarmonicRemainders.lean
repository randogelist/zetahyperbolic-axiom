import LeanPaper.BeukersOuterValuation
import Mathlib.NumberTheory.Padics.PadicNorm

/-!
# Actual harmonic remainders for the Aq Beukers matrix

Removing the unique q-divisible summand below 2q leaves a q-adic integer.
The diagonal congruence is deliberately stated AFTER multiplication by q^7:
the unscaled diagonal error need not itself be q-adically integral.
-/

noncomputable section
open scoped BigOperators

namespace ManuscriptChain.Beukers

lemma padicNorm_nat_pow (q : ℕ) [Fact q.Prime] (x : ℚ) (s : ℕ) :
    padicNorm q (x^s) = (padicNorm q x)^s := by
  induction s with
  | zero => simp [padicNorm.one]
  | succ s ih => rw [pow_succ, padicNorm.mul, ih, pow_succ]

lemma reciprocal_power_norm_one (q m s : ℕ) [Fact q.Prime] (hm : ¬q ∣ m) :
    padicNorm q (1/(m : ℚ)^s) = 1 := by
  rw [padicNorm.div, padicNorm.one, padicNorm_nat_pow,
    (padicNorm.nat_eq_one_iff m).mpr hm]
  simp

lemma reciprocal_prime_power_norm (q s : ℕ) [Fact q.Prime] :
    padicNorm q (1/(q : ℚ)^s) = (q : ℚ)^s := by
  rw [padicNorm.div, padicNorm.one, padicNorm_nat_pow, padicNorm.padicNorm_p_of_prime]
  simp only [inv_pow, one_div, inv_inv]

private lemma not_dvd_below_twice_prime (q m : ℕ) [Fact q.Prime]
    (hm0 : 0 < m) (hm2 : m < 2*q) (hmq : m ≠ q) : ¬q ∣ m := by
  have hq : q.Prime := Fact.out
  rintro ⟨k, hk⟩
  have hk2 : k < 2 := by
    apply (Nat.mul_lt_mul_left hq.pos).mp
    rw [← hk]
    omega
  have hk0 : k ≠ 0 := by
    intro hz
    simp [hz] at hk
    omega
  have hk1 : k = 1 := by omega
  apply hmq
  simpa [hk1] using hk

/-- All harmonic denominators below q are units at q. -/
theorem harmonic_below_prime_norm_le (q s r : ℕ) [Fact q.Prime] (hr : r < q) :
    padicNorm q (Real.harmonic s r) ≤ 1 := by
  unfold Real.harmonic
  apply padicNorm.sum_le' _ (by norm_num)
  intro i hi
  have hiq : i+1 < q := by have := Finset.mem_range.mp hi; omega
  rw [reciprocal_power_norm_one q (i+1) s
    (Nat.not_dvd_of_pos_of_lt (by omega) hiq)]
  all_goals exact le_rfl

/-- At the shifted index r+q, the only nonintegral summand is q^(-s). -/
theorem harmonic_shift_sub_pole_norm_le (q s r : ℕ) [Fact q.Prime] (hr : r < q) :
    padicNorm q (Real.harmonic s (r+q) - 1/(q : ℚ)^s) ≤ 1 := by
  classical
  have hq : q.Prime := Fact.out
  have hj : q-1 ∈ Finset.range (r+q) := by
    apply Finset.mem_range.mpr
    omega
  have hi : q-1+1 = q := by omega
  have he : Real.harmonic s (r+q) - 1/(q : ℚ)^s =
      ∑ i ∈ (Finset.range (r+q)).erase (q-1), 1/((i+1 : ℕ) : ℚ)^s := by
    unfold Real.harmonic
    rw [← Finset.sum_erase_add _ _ hj, hi]
    ring
  rw [he]
  apply padicNorm.sum_le' _ (by norm_num)
  intro i hi_mem
  have hir : i < r+q := Finset.mem_range.mp (Finset.mem_of_mem_erase hi_mem)
  have hneq : i+1 ≠ q := by
    have := Finset.ne_of_mem_erase hi_mem
    omega
  rw [reciprocal_power_norm_one q (i+1) s
    (not_dvd_below_twice_prime q (i+1) (by omega) (by omega) hneq)]
  all_goals exact le_rfl

/-- A uniform bound retaining the one possible prime-pole contribution. -/
theorem harmonic_below_twice_prime_norm_le (q s n : ℕ) [Fact q.Prime]
    (hn : n < 2*q) : padicNorm q (Real.harmonic s n) ≤ (q : ℚ)^s := by
  have hq : q.Prime := Fact.out
  unfold Real.harmonic
  apply padicNorm.sum_le' _ (by positivity)
  intro i hi
  have hin : i < n := Finset.mem_range.mp hi
  by_cases he : i+1 = q
  · rw [he, reciprocal_prime_power_norm] <;> exact le_rfl
  · rw [reciprocal_power_norm_one q (i+1) s
      (not_dvd_below_twice_prime q (i+1) (by omega) (by omega) he)]
    exact one_le_pow₀ (by exact_mod_cast hq.one_le)

lemma padicNorm_three_eq_one (q : ℕ) [Fact q.Prime] (hq5 : 5 ≤ q) :
    padicNorm q (3 : ℚ) = 1 :=
  (padicNorm.nat_eq_one_iff 3).mpr
    (Nat.not_dvd_of_pos_of_lt (by norm_num) (by omega))

lemma padicNorm_two_eq_one (q : ℕ) [Fact q.Prime] (hq5 : 5 ≤ q) :
    padicNorm q (2 : ℚ) = 1 :=
  (padicNorm.nat_eq_one_iff 2).mpr
    (Nat.not_dvd_of_pos_of_lt (by norm_num) (by omega))

lemma padicNorm_negative_two_thirds_eq_one (q : ℕ) [Fact q.Prime]
    (hq5 : 5 ≤ q) : padicNorm q (-2/3 : ℚ) = 1 := by
  rw [padicNorm.div, padicNorm.neg, padicNorm_two_eq_one q hq5,
    padicNorm_three_eq_one q hq5]
  norm_num

lemma padicNorm_six_eq_one (q : ℕ) [Fact q.Prime] (hq5 : 5 ≤ q) :
    padicNorm q (6 : ℚ) = 1 := by
  have h2 : padicNorm q (2 : ℚ) = 1 :=
    (padicNorm.nat_eq_one_iff 2).mpr
      (Nat.not_dvd_of_pos_of_lt (by norm_num) (by omega))
  calc
    padicNorm q (6 : ℚ) = padicNorm q ((2 : ℚ)*3) := by norm_num
    _ = padicNorm q (2 : ℚ)*padicNorm q (3 : ℚ) := padicNorm.mul _ _
    _ = 1 := by rw [h2, padicNorm_three_eq_one q hq5]; norm_num

/-- Multiplication by a positive power of q makes every q-integral rational small. -/
lemma prime_power_mul_norm_lt_one (q k : ℕ) [Fact q.Prime] (hk : 0 < k)
    (x : ℚ) (hx : padicNorm q x ≤ 1) : padicNorm q ((q : ℚ)^k*x) < 1 := by
  have hq : q.Prime := Fact.out
  rw [padicNorm.mul, padicNorm_nat_pow, padicNorm.padicNorm_p_of_prime]
  calc
    ((q : ℚ)⁻¹)^k * padicNorm q x ≤ ((q : ℚ)⁻¹)^k * 1 :=
      mul_le_mul_of_nonneg_left hx (by positivity)
    _ < 1 := by
      rw [mul_one]
      exact pow_lt_one₀ (by positivity)
        (by simpa only [padicNorm.padicNorm_p_of_prime] using
          (padicNorm.padicNorm_p_lt_one hq.one_lt)) (by omega)

lemma scaled_integral_two_mul_norm_lt (q : ℕ) [Fact q.Prime] (hq5 : 5 ≤ q)
    (X : ℚ) (hX : padicNorm q X ≤ 1) :
    padicNorm q ((q : ℚ)^7 * (2*X)) < 1 := by
  apply prime_power_mul_norm_lt_one q 7 (by norm_num)
  rw [padicNorm.mul, padicNorm_two_eq_one q hq5, one_mul]
  exact hX

lemma padicNorm_index_difference_eq_one (q r t : ℕ) [Fact q.Prime]
    (hne : r % q ≠ t % q) : padicNorm q ((r : ℚ)-(t : ℚ)) = 1 := by
  have hd : ¬(q : ℤ) ∣ ((r : ℤ)-(t : ℤ)) := by
    intro hd
    have hm : Nat.ModEq q t r := Nat.modEq_iff_dvd.mpr hd
    exact hne hm.symm
  have h := (padicNorm.int_eq_one_iff ((r : ℤ)-(t : ℤ))).mpr hd
  simpa only [Int.cast_sub, Int.cast_natCast] using h

/-- Different residue classes have no divided-difference prime pole. -/
theorem scaled_dualConstant_distinct_residues_norm_lt (q r t : ℕ) [Fact q.Prime]
    (hq5 : 5 ≤ q) (hr : r < 2*q) (ht : t < 2*q) (hne : r % q ≠ t % q) :
    padicNorm q ((q : ℚ)^7 * Real.dualConstant 7 r t) < 1 := by
  have hq : q.Prime := Fact.out
  have hq0 : (q : ℚ) ≠ 0 := by exact_mod_cast hq.ne_zero
  have hrt : r ≠ t := by intro h; exact hne (congrArg (fun i => i % q) h)
  have hh : padicNorm q (Real.harmonic 6 r - Real.harmonic 6 t) ≤ (q : ℚ)^6 :=
    padicNorm.sub.trans (max_le (harmonic_below_twice_prime_norm_le q 6 r hr)
      (harmonic_below_twice_prime_norm_le q 6 t ht))
  have hc : padicNorm q (Real.dualConstant 7 r t) ≤ (q : ℚ)^6 := by
    simp only [Real.dualConstant, hrt, if_false]
    norm_num only [Nat.reduceSub, Nat.cast_ofNat]
    rw [padicNorm.div, padicNorm.mul, padicNorm_six_eq_one q hq5,
      padicNorm_index_difference_eq_one q r t hne]
    simpa using hh
  rw [padicNorm.mul, padicNorm_nat_pow, padicNorm.padicNorm_p_of_prime]
  calc
    ((q : ℚ)⁻¹)^7 * padicNorm q (Real.dualConstant 7 r t) ≤
        ((q : ℚ)⁻¹)^7 * (q : ℚ)^6 := mul_le_mul_of_nonneg_left hc (by positivity)
    _ = (q : ℚ)⁻¹ := by field_simp [hq0] <;> ring
    _ < 1 := by
      rw [← padicNorm.padicNorm_p hq.one_lt]
      exact padicNorm.padicNorm_p_lt_one hq.one_lt

/-- The actual Aq diagonal has leading coefficient -2/3 after scaling by q^7.
No claim of q-integrality of its unscaled error is made. -/
theorem scaled_Aq_diagonal_remainder_norm_lt (q r : ℕ) [Fact q.Prime]
    (hq5 : 5 ≤ q) (hr : r < q) :
    padicNorm q ((q : ℚ)^7 *
      (-Real.harmonic 7 r - Real.harmonic 7 (r+q) +
        (Real.harmonic 6 r - Real.harmonic 6 (r+q))/(3*(-(q : ℚ)))) + 2/3) < 1 := by
  have hq : q.Prime := Fact.out
  have hq0 : (q : ℚ) ≠ 0 := by exact_mod_cast hq.ne_zero
  let a : ℚ := Real.harmonic 7 r + (Real.harmonic 7 (r+q) - 1/(q : ℚ)^7)
  let b : ℚ := (Real.harmonic 6 r - (Real.harmonic 6 (r+q) - 1/(q : ℚ)^6))/3
  have ha : padicNorm q a ≤ 1 :=
    padicNorm.nonarchimedean.trans (max_le (harmonic_below_prime_norm_le q 7 r hr)
      (harmonic_shift_sub_pole_norm_le q 7 r hr))
  have hb : padicNorm q b ≤ 1 := by
    dsimp [b]
    rw [padicNorm.div, padicNorm_three_eq_one q hq5, div_one]
    exact padicNorm.sub.trans (max_le (harmonic_below_prime_norm_le q 6 r hr)
      (harmonic_shift_sub_pole_norm_le q 6 r hr))
  have he : (q : ℚ)^7 *
      (-Real.harmonic 7 r - Real.harmonic 7 (r+q) +
        (Real.harmonic 6 r - Real.harmonic 6 (r+q))/(3*(-(q : ℚ)))) + 2/3 =
      -((q : ℚ)^7*a) - (q : ℚ)^6*b := by
    dsimp [a, b]
    field_simp [hq0] <;> ring
  rw [he]
  apply lt_of_le_of_lt padicNorm.sub
  apply max_lt
  · rw [padicNorm.neg]
    exact prime_power_mul_norm_lt_one q 7 (by norm_num) a ha
  · exact prime_power_mul_norm_lt_one q 6 (by norm_num) b hb

end ManuscriptChain.Beukers

#print axioms ManuscriptChain.Beukers.harmonic_shift_sub_pole_norm_le
#print axioms ManuscriptChain.Beukers.scaled_dualConstant_distinct_residues_norm_lt
#print axioms ManuscriptChain.Beukers.scaled_Aq_diagonal_remainder_norm_lt
