import LeanPaper.PullbackReflection

/-!
Complete polynomial-plus-simple-pole finite-span difference identity for the
actual Bernoulli/harmonic functional. The polynomial term is proved from the
existing Bernoulli convolution, and is retained in the combined identity.
This is a finite-normal-form result, not arbitrary RatFunc independence.
-/

noncomputable section
open scoped BigOperators
open Polynomial

namespace LeanPaper.Section2FiniteDifference
open Zetahyperbolic LeanPaper.PullbackReflection

theorem tau_monomial_difference (k d : ℕ) (hk : 1 ≤ k) :
    (∑ i ∈ Finset.range (d + 1), (Nat.choose d i : ℚ) * tauMonomial k i) -
      tauMonomial k d = if d = 2 * k then 1 else 0 := by
  by_cases hd : 2 * k - 1 ≤ d
  · rw [tauMonomial_binomial_convolution k d hk hd,
      tauMonomial_eq_choose k d hk, if_pos hd]
    by_cases heq : d = 2 * k
    · subst d
      have hsub : 2 * k - (2 * k - 1) = 1 := by omega
      have hchoose : Nat.choose (2 * k) (2 * k - 1) = 2 * k := by
        rw [Nat.choose_symm (by omega : 1 ≤ 2 * k), Nat.choose_one_right]
      rw [if_pos rfl, hsub, hchoose, _root_.bernoulli'_one, _root_.bernoulli_one]
      have h2k : (2 * k : ℚ) ≠ 0 := by positivity
      push_cast
      field_simp [h2k]
      norm_num
    · have hsub : d - (2 * k - 1) ≠ 1 := by omega
      rw [if_neg heq, bernoulli_eq_bernoulli'_of_ne_one hsub]
      ring
  · have heq : d ≠ 2 * k := by omega
    rw [if_neg heq]
    have hsum : (∑ i ∈ Finset.range (d + 1),
        (Nat.choose d i : ℚ) * tauMonomial k i) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      have hcut : ¬ 2 * k - 1 ≤ i := by
        have := Finset.mem_range.mp hi
        omega
      simp [tauMonomial, hcut]
    rw [hsum]
    simp [tauMonomial, hd]

def translatedMoment (k : ℕ) (es : Finset ℕ) (u : ℕ → ℚ)
    (rs : Finset ℤ) (v : ℤ → ℚ) : ℚ[X] :=
  (∑ d ∈ es, C (u d *
    (∑ i ∈ Finset.range (d + 1), (Nat.choose d i : ℚ) * tauMonomial k i))) +
  ∑ r ∈ rs, C (v r) * tauPolePoly k (r - 1)

theorem finite_span_difference (k : ℕ) (hk : 1 ≤ k)
    (es : Finset ℕ) (u : ℕ → ℚ) (rs : Finset ℤ) (v : ℤ → ℚ)
    (hr : ∀ r ∈ rs, r ≠ 0 ∧ r ≠ 1) :
    translatedMoment k es u rs v - tauFiniteSpan k es u rs v =
      (∑ d ∈ es, C (u d * (if d = 2 * k then 1 else 0))) +
        ∑ r ∈ rs, C (v r * (-((r : ℚ) ^ (2 * k + 1))⁻¹)) := by
  unfold translatedMoment tauFiniteSpan
  have hpoly :
      (∑ d ∈ es, C (u d *
        (∑ i ∈ Finset.range (d + 1), (Nat.choose d i : ℚ) * tauMonomial k i))) -
      (∑ d ∈ es, C (u d * tauMonomial k d)) =
      ∑ d ∈ es, C (u d * (if d = 2 * k then 1 else 0)) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro d hd
    rw [← Polynomial.C_sub, ← mul_sub, tau_monomial_difference k d hk]
  have hpole :
      (∑ r ∈ rs, C (v r) * tauPolePoly k (r - 1)) -
      (∑ r ∈ rs, C (v r) * tauPolePoly k r) =
      ∑ r ∈ rs, C (v r * (-((r : ℚ) ^ (2 * k + 1))⁻¹)) := by
    rw [← Finset.sum_sub_distrib]
    simp_rw [← mul_sub]
    exact finite_pole_difference k rs v hr
  calc
    _ = ((∑ d ∈ es, C (u d *
        (∑ i ∈ Finset.range (d + 1), (Nat.choose d i : ℚ) * tauMonomial k i))) -
      (∑ d ∈ es, C (u d * tauMonomial k d))) +
      ((∑ r ∈ rs, C (v r) * tauPolePoly k (r - 1)) -
      (∑ r ∈ rs, C (v r) * tauPolePoly k r)) := by ring
    _ = _ := by rw [hpoly, hpole]

theorem finite_span_difference_coefficient (k : ℕ) (hk : 1 ≤ k)
    (es : Finset ℕ) (u : ℕ → ℚ) (rs : Finset ℤ) (v : ℤ → ℚ)
    (hr : ∀ r ∈ rs, r ≠ 0 ∧ r ≠ 1) :
    translatedMoment k es u rs v - tauFiniteSpan k es u rs v =
      C (if 2 * k ∈ es then u (2 * k) else 0) +
        ∑ r ∈ rs, C (v r * (-((r : ℚ) ^ (2 * k + 1))⁻¹)) := by
  rw [finite_span_difference k hk es u rs v hr]
  congr 1
  classical
  rw [← map_sum]
  congr 1
  simp [mul_ite]

/-- The actual finite rational span, evaluated using the rational field. -/
def finiteSpanValue (es : Finset ℕ) (u : ℕ → ℚ)
    (rs : Finset ℤ) (v : ℤ → ℚ) (x : ℚ) : ℚ :=
  (∑ d ∈ es, u d * x ^ d) + ∑ r ∈ rs, v r * (x - (r : ℚ))⁻¹

/-- The translated polynomial and integer-pole expression. -/
def translatedSpanValue (es : Finset ℕ) (u : ℕ → ℚ)
    (rs : Finset ℤ) (v : ℤ → ℚ) (x : ℚ) : ℚ :=
  (∑ d ∈ es, u d *
    (∑ i ∈ Finset.range (d + 1), (Nat.choose d i : ℚ) * x ^ i)) +
  ∑ r ∈ rs, v r * (x - ((r - 1 : ℤ) : ℚ))⁻¹

/-- Exact function-level translation; on the pole complement this is the
usual identity for the finite rational span. -/
theorem finite_span_translation (es : Finset ℕ) (u : ℕ → ℚ)
    (rs : Finset ℤ) (v : ℤ → ℚ) (x : ℚ) :
    finiteSpanValue es u rs v (x + 1) = translatedSpanValue es u rs v x := by
  unfold finiteSpanValue translatedSpanValue
  apply congrArg₂ (fun a b : ℚ => a + b)
  · apply Finset.sum_congr rfl
    intro d hd
    congr 1
    simpa [mul_comm] using (add_pow x (1 : ℚ) d)
  · apply Finset.sum_congr rfl
    intro r hr
    congr 2
    push_cast
    ring

/-- The same finite input has the pointwise translated expression and the
complete Bernoulli/harmonic moment difference, including its polynomial term. -/
theorem function_and_moment_difference (k : ℕ) (hk : 1 ≤ k)
    (es : Finset ℕ) (u : ℕ → ℚ) (rs : Finset ℤ) (v : ℤ → ℚ)
    (hr : ∀ r ∈ rs, r ≠ 0 ∧ r ≠ 1) (x : ℚ) :
    (finiteSpanValue es u rs v (x + 1) = translatedSpanValue es u rs v x) ∧
    (translatedMoment k es u rs v - tauFiniteSpan k es u rs v =
      C (if 2 * k ∈ es then u (2 * k) else 0) +
        ∑ r ∈ rs, C (v r * (-((r : ℚ) ^ (2 * k + 1))⁻¹))) :=
  ⟨finite_span_translation es u rs v x,
    finite_span_difference_coefficient k hk es u rs v hr⟩

end LeanPaper.Section2FiniteDifference
