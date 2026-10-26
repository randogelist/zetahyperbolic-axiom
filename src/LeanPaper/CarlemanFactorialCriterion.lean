import Mathlib

/-!
# Theorem 3.3: abstract factorial-growth Carleman criterion

Isolated from the unverified `snditeration` CarlemanDivergence development.
The factorial majorant is retained from the donor. The remaining statements
are constructed for an arbitrary strictly positive moment sequence and use
only an explicit factorial growth bound. In particular, they DO NOT assert
that the manuscript's actual moments satisfy that upper estimate.

The missing identification with the actual positive moment measure, and the
Stieltjes uniqueness theorem, are separate open endpoints of manuscript 3.3.
-/

noncomputable section
open scoped BigOperators

namespace LeanPaper.CarlemanFactorialCriterion

/-- An elementary factorial-to-root bound, deliberately with loose constants. -/
theorem factorial_majorant_le_power {C : ℝ} (hC : 0 ≤ C) (A r : ℕ) (hr : 1 ≤ r) :
    C * (Nat.factorial (2 * r + A) : ℝ) ≤
      (((C + 1) * ((A : ℝ) + 2) ^ (A + 2) * (2 : ℝ) ^ A) * r) ^ (2 * r) := by
  have hrR : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hAR : (0 : ℝ) ≤ A := Nat.cast_nonneg A
  have hb : (1 : ℝ) ≤ (A : ℝ) + 2 := by
    linarith
  have hbase : ((2 * r + A : ℕ) : ℝ) ≤ ((A : ℝ) + 2) * r := by
    push_cast
    nlinarith [mul_nonneg hAR (sub_nonneg.mpr hrR)]
  have hfact : (Nat.factorial (2 * r + A) : ℝ) ≤
      (((2 * r + A : ℕ) : ℝ)) ^ (2 * r + A) := by
    exact_mod_cast Nat.factorial_le_pow (2 * r + A)
  have hpower := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ ((2 * r + A : ℕ) : ℝ))
    hbase (2 * r + A)
  have hc : C ≤ (C + 1) ^ (2 * r) :=
    (by linarith : C ≤ C + 1).trans (le_self_pow₀ (by linarith) (by omega))
  have hbpow : ((A : ℝ) + 2) ^ (2 * r + A) ≤
      ((A : ℝ) + 2) ^ ((A + 2) * (2 * r)) := by
    apply pow_le_pow_right₀ hb
    have hAr : A ≤ A * r := by simpa using Nat.mul_le_mul_left A hr
    nlinarith [Nat.zero_le (A * r)]
  have hrpow : (r : ℝ) ^ A ≤ (2 : ℝ) ^ (A * (2 * r)) := by
    calc
      _ ≤ ((2 : ℝ) ^ r) ^ A := by
        apply pow_le_pow_left₀ (by positivity)
        have hnat : r ≤ 2 ^ r := (Nat.lt_two_pow_self).le
        exact_mod_cast hnat
      _ = (2 : ℝ) ^ (r * A) := (pow_mul _ _ _).symm
      _ ≤ _ := pow_le_pow_right₀ (by norm_num) (by
        simpa only [Nat.mul_comm r A] using
          Nat.mul_le_mul_left A (show r ≤ 2 * r by omega))
  calc
    _ ≤ C * (((A : ℝ) + 2) * r) ^ (2 * r + A) :=
      mul_le_mul_of_nonneg_left (hfact.trans hpower) hC
    _ = (C * ((A : ℝ) + 2) ^ (2 * r + A) * (r : ℝ) ^ A) *
        (r : ℝ) ^ (2 * r) := by
      rw [mul_pow, pow_add, pow_add]
      ring
    _ ≤ ((C + 1) ^ (2 * r) * ((A : ℝ) + 2) ^ ((A + 2) * (2 * r)) *
        (2 : ℝ) ^ (A * (2 * r))) * (r : ℝ) ^ (2 * r) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      apply mul_le_mul _ hrpow (by positivity) (by positivity)
      exact mul_le_mul hc hbpow (by positivity) (by positivity)
    _ = _ := by simp only [mul_pow, pow_mul]


def growthConstant (C : ℝ) (A : ℕ) : ℝ :=
  (C + 1) * ((A : ℝ) + 2) ^ (A + 2) * (2 : ℝ) ^ A

theorem growthConstant_pos (C : ℝ) (A : ℕ) (hC : 0 ≤ C) :
    0 < growthConstant C A := by
  unfold growthConstant
  positivity

def carlemanTerm (M : ℕ → ℝ) (r : ℕ) : ℝ :=
  (M r) ^ (-(((2 * r : ℕ) : ℝ))⁻¹)

/-- A uniform bound on the 2r-th moment roots implies a harmonic lower
bound on every corresponding Carleman summand. -/
theorem carlemanTerm_lower_bound_of_power
    (M : ℕ → ℝ) (B : ℝ) (hB : 0 < B)
    (hM : ∀ r : ℕ, 1 ≤ r → 0 < M r)
    (hbound : ∀ r : ℕ, 1 ≤ r → M r ≤ (B * r) ^ (2 * r))
    (r : ℕ) (hr : 1 ≤ r) :
    1 / (B * r) ≤ carlemanTerm M r := by
  have hp := hM r hr
  have hle := hbound r hr
  have h := Real.rpow_le_rpow_of_nonpos hp hle
    (by exact neg_nonpos.mpr (inv_nonneg.mpr (by positivity : (0 : ℝ) ≤ ((2 * r : ℕ) : ℝ))) :
      -(((2 * r : ℕ) : ℝ))⁻¹ ≤ 0)
  rw [Real.rpow_neg (by positivity),
    Real.pow_rpow_inv_natCast (by positivity) (by omega)] at h
  simpa only [one_div, carlemanTerm] using h

/-- Purely analytic divergence transfer, independent of the actual ζ moment
measure. This is A-Tier only as the displayed conditional implication. -/
theorem carleman_not_summable_of_power
    (M : ℕ → ℝ) (B : ℝ) (hB : 0 < B)
    (hM : ∀ r : ℕ, 1 ≤ r → 0 < M r)
    (hbound : ∀ r : ℕ, 1 ≤ r → M r ≤ (B * r) ^ (2 * r)) :
    ¬ Summable (fun n : ℕ => carlemanTerm M (n + 1)) := by
  intro hs
  have hsmall : Summable (fun n : ℕ => 1 / (B * (n + 1))) := by
    apply Summable.of_nonneg_of_le (fun n => by positivity) _ hs
    intro n
    simpa only [Nat.cast_add, Nat.cast_one] using
      carlemanTerm_lower_bound_of_power M B hB hM hbound (n + 1) (by omega)
  have heq : (fun n : ℕ => 1 / (B * (n + 1))) =
      (fun n : ℕ => B⁻¹ * (1 / ((n + 1 : ℕ) : ℝ))) := by
    funext n
    simp [one_div, mul_inv_rev, mul_comm]
  rw [heq] at hsmall
  have hsum := (summable_mul_left_iff (inv_ne_zero hB.ne')).1 hsmall
  exact Real.not_summable_one_div_natCast ((summable_nat_add_iff 1).1 hsum)

/-- Donor factorial estimate implies the abstract Carleman divergence.
The supplied bound on M is NOT proved for the manuscript data here. -/
theorem carleman_not_summable_of_factorial_growth
    (M : ℕ → ℝ) (C : ℝ) (A : ℕ) (hC : 0 ≤ C)
    (hM : ∀ r : ℕ, 1 ≤ r → 0 < M r)
    (hbound : ∀ r : ℕ, 1 ≤ r →
       M r ≤ C * (Nat.factorial (2 * r + A) : ℝ)) :
    ¬ Summable (fun n : ℕ => carlemanTerm M (n + 1)) := by
  apply carleman_not_summable_of_power M (growthConstant C A)
    (growthConstant_pos C A hC) hM
  intro r hr
  exact (hbound r hr).trans (factorial_majorant_le_power hC A r hr)

#print axioms factorial_majorant_le_power
#print axioms carleman_not_summable_of_power
#print axioms carleman_not_summable_of_factorial_growth

end LeanPaper.CarlemanFactorialCriterion
