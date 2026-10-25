import Zetahyperbolic.Section2Checked

/-!
# Function-level pullback and full finite-span tau identities

This increment uses the canonical `Zetahyperbolic.RatMomentElem`, and reuses
its actual Bernoulli/harmonic moments. The polynomial quotient in the odd
square-pole substitution is retained. Its lower terms are proved to have
zero tau moment, instead of being omitted from the definition.

The pointwise theorem is on the complement of the actual finite pole set.
The moment theorem is on finite partial-fraction normal forms. Independence
under equality of arbitrary `RatFunc` representations remains a separate
obligation. These statements do not assert analytic or arithmetic closure.

Source adaptation: attached archive 19, Section2FunctionLevelPullback;
commit-pinned cross-base FullNormalForm sources recorded in provenance.
No new mathematical axioms, proof fields, or witness admissions are used.
-/

noncomputable section
open scoped BigOperators
open Polynomial

namespace LeanPaper.PullbackReflection
open Zetahyperbolic

/-- Numerical polynomial quotient for division by `j^2-x^2`. -/
def oddQuotient (j x : ℚ) : ℕ → ℚ
  | 0 => 0
  | n + 1 => x ^ (2 * n + 1) + j ^ 2 * oddQuotient j x n

/-- Applying the manuscript monomial moments to every quotient term. -/
def quotientMoment (k : ℕ) (j : ℚ) : ℕ → ℚ
  | 0 => 0
  | n + 1 => tauMonomial k (2 * n + 1) + j ^ 2 * quotientMoment k j n

/-- Every term strictly below the weight cutoff vanishes. -/
theorem quotientMoment_below (k n : ℕ) (j : ℚ) :
    n < k → quotientMoment k j n = 0 := by
  induction n with
  | zero => intro _; rfl
  | succ n ih =>
      intro hn
      have ht : 2 * n + 1 < 2 * k - 1 := by omega
      have hq : quotientMoment k j n = 0 := ih (by omega)
      simp [quotientMoment, tauMonomial, Nat.not_le_of_gt ht, hq]

/-- The full quotient contributes its top monomial, with no discarded terms. -/
theorem quotientMoment_top (k : ℕ) (hk : 1 ≤ k) (j : ℚ) :
    quotientMoment k j k = tauMonomial k (2 * k - 1) := by
  cases k with
  | zero => omega
  | succ n =>
      have hq : quotientMoment (n + 1) j n = 0 :=
        quotientMoment_below (n + 1) n j (by omega)
      have he : 2 * (n + 1) - 1 = 2 * n + 1 := by omega
      simp [quotientMoment, hq, he]

/-- Exact division identity, including the zero-weight case. -/
theorem oddQuotient_division (j x : ℚ) (k : ℕ) :
    (j ^ 2 - x ^ 2) * oddQuotient j x k + x ^ (2 * k + 1) =
      j ^ (2 * k) * x := by
  induction k with
  | zero => simp [oddQuotient]
  | succ k ih =>
      change (j ^ 2 - x ^ 2) *
          (x ^ (2 * k + 1) + j ^ 2 * oddQuotient j x k) +
          x ^ (2 * (k + 1) + 1) = j ^ (2 * (k + 1)) * x
      have hx : x ^ (2 * (k + 1) + 1) = x ^ (2 * k + 1) * x ^ 2 := by
        rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 2 by omega, pow_add]
      have hj : j ^ (2 * (k + 1)) = j ^ (2 * k) * j ^ 2 := by
        rw [show 2 * (k + 1) = 2 * k + 2 by omega, pow_add]
      rw [hx, hj]
      calc
        _ = j ^ 2 * ((j ^ 2 - x ^ 2) * oddQuotient j x k +
          x ^ (2 * k + 1)) := by ring
        _ = j ^ 2 * (j ^ (2 * k) * x) := by rw [ih]
        _ = _ := by ring

private theorem squareDenom_ne_zero (j x : ℚ)
    (hm : x ≠ j) (hp : x ≠ -j) : j ^ 2 - x ^ 2 ≠ 0 := by
  have hm0 : x - j ≠ 0 := sub_ne_zero.mpr hm
  have hp0 : x + j ≠ 0 := by
    intro h
    apply hp
    linear_combination h
  have hf : j ^ 2 - x ^ 2 = -((x - j) * (x + j)) := by ring
  rw [hf]
  exact neg_ne_zero.mpr (mul_ne_zero hm0 hp0)

/-- Partial fractions at the actual pair of poles `x=±j`. -/
theorem square_pole_pointwise (k : ℕ) (j x : ℚ)
    (hm : x ≠ j) (hp : x ≠ -j) :
    x ^ (2 * k + 1) * (j ^ 2 - x ^ 2)⁻¹ =
      -oddQuotient j x k -
        (j ^ (2 * k) / 2) * ((x - j)⁻¹ + (x + j)⁻¹) := by
  have hm0 : x - j ≠ 0 := sub_ne_zero.mpr hm
  have hp0 : x + j ≠ 0 := by
    intro h
    apply hp
    linear_combination h
  have hd := squareDenom_ne_zero j x hm hp
  have hs : x * (j ^ 2 - x ^ 2)⁻¹ =
      -(1 / 2 : ℚ) * ((x - j)⁻¹ + (x + j)⁻¹) := by
    field_simp [hm0, hp0, hd] <;> ring
  have hn : x ^ (2 * k + 1) =
      -(j ^ 2 - x ^ 2) * oddQuotient j x k + j ^ (2 * k) * x := by
    linear_combination oddQuotient_division j x k
  calc
    _ = (-(j ^ 2 - x ^ 2) * oddQuotient j x k +
      j ^ (2 * k) * x) * (j ^ 2 - x ^ 2)⁻¹ := by rw [hn]
    _ = -oddQuotient j x k + j ^ (2 * k) * (x * (j ^ 2 - x ^ 2)⁻¹) := by
      field_simp [hd] <;> ring
    _ = _ := by rw [hs]; ring

/-- Exact polynomial generator substitution. -/
theorem monomial_pointwise (k e : ℕ) (c x : ℚ) :
    x ^ (2 * k + 1) * (c * (-x ^ 2) ^ e) =
      c * (-1 : ℚ) ^ e * x ^ (2 * e + 2 * k + 1) := by
  have hn : (-x ^ 2 : ℚ) = (-1 : ℚ) * x ^ 2 := by ring
  rw [hn, mul_pow]
  have he : (x ^ 2) ^ e = x ^ (2 * e) := by rw [pow_mul]
  rw [he]
  rw [show 2 * e + 2 * k + 1 = (2 * k + 1) + 2 * e by omega, pow_add]
  ring

/-- The original rational function of the canonical normal form. -/
def rationalValue (R : RatMomentElem) (t : ℚ) : ℚ :=
  R.polyPart.eval t + ∑ j ∈ Finset.Icc 1 R.maxPole,
    R.poleRes j * (t + (j : ℚ) ^ 2)⁻¹

/-- The expanded substituted function, including the whole quotient. -/
def pulledValue (k : ℕ) (R : RatMomentElem) (x : ℚ) : ℚ :=
  (∑ e ∈ Finset.range (R.polyPart.natDegree + 1),
    R.polyPart.coeff e * (-1 : ℚ) ^ e * x ^ (2 * e + 2 * k + 1)) +
  ∑ j ∈ Finset.Icc 1 R.maxPole, R.poleRes j *
    (-oddQuotient (j : ℚ) x k -
      ((j : ℚ) ^ (2 * k) / 2) * ((x - (j : ℚ))⁻¹ + (x + (j : ℚ))⁻¹))

/-- Actual function-level substitution for every canonical normal form. -/
theorem rationalValue_pullback (k : ℕ) (R : RatMomentElem) (x : ℚ)
    (hAvoid : ∀ j ∈ Finset.Icc 1 R.maxPole,
      x ≠ (j : ℚ) ∧ x ≠ -(j : ℚ)) :
    x ^ (2 * k + 1) * rationalValue R (-x ^ 2) = pulledValue k R x := by
  unfold rationalValue pulledValue
  rw [mul_add, Polynomial.eval_eq_sum_range, Finset.mul_sum, Finset.mul_sum]
  apply congrArg₂ (fun a b : ℚ => a + b)
  · apply Finset.sum_congr rfl
    intro e he
    exact monomial_pointwise k e (R.polyPart.coeff e) x
  · apply Finset.sum_congr rfl
    intro j hj
    have hd : -x ^ 2 + (j : ℚ) ^ 2 = (j : ℚ) ^ 2 - x ^ 2 := by ring
    rw [hd]
    calc
      _ = R.poleRes j * (x ^ (2 * k + 1) * ((j : ℚ) ^ 2 - x ^ 2)⁻¹) := by ring
      _ = _ := by rw [square_pole_pointwise k (j : ℚ) x (hAvoid j hj).1 (hAvoid j hj).2]

/-- Tau applied to the complete expanded normal form. The quotient is
computed independently and is not replaced by its top term by definition. -/
def pulledMoment (k : ℕ) (R : RatMomentElem) : ℚ[X] :=
  (∑ e ∈ Finset.range (R.polyPart.natDegree + 1),
    C (R.polyPart.coeff e *
      ((-1 : ℚ) ^ e * tauMonomial k (2 * e + 2 * k + 1)))) +
  ∑ j ∈ Finset.Icc 1 R.maxPole, C (R.poleRes j) *
    (C (-quotientMoment k (j : ℚ) k) - C ((j : ℚ) ^ (2 * k) / 2) *
      (tauPolePoly k (j : ℤ) + tauPolePoly k (-(j : ℤ))))

/-- Full finite normal-form moment equality, including quotient annihilation. -/
theorem muFunctionalPoly_eq_pulledMoment
    (k : ℕ) (hk : 1 ≤ k) (R : RatMomentElem) :
    muFunctionalPoly k R = pulledMoment k R := by
  unfold muFunctionalPoly pulledMoment
  apply congrArg₂ (fun a b : ℚ[X] => a + b)
  · apply Finset.sum_congr rfl
    intro e he
    rw [pullback_identity_monomial k e hk]
  · apply Finset.sum_congr rfl
    intro j hj
    rw [quotientMoment_top k hk, pullback_identity_pole k j hk (Finset.mem_Icc.mp hj).1]

/-- The same canonical input has both the exact pointwise substitution and
its Bernoulli/harmonic moment identity. This is not a RatFunc quotient proof. -/
theorem function_and_moment_pullback
    (k : ℕ) (hk : 1 ≤ k) (R : RatMomentElem) (x : ℚ)
    (hAvoid : ∀ j ∈ Finset.Icc 1 R.maxPole,
      x ≠ (j : ℚ) ∧ x ≠ -(j : ℚ)) :
    (x ^ (2 * k + 1) * rationalValue R (-x ^ 2) = pulledValue k R x) ∧
    (muFunctionalPoly k R = pulledMoment k R) :=
  ⟨rationalValue_pullback k R x hAvoid, muFunctionalPoly_eq_pulledMoment k hk R⟩

/-- Tau on a finite span of the actual monomial and integer-pole generators. -/
def tauFiniteSpan (k : ℕ) (es : Finset ℕ) (u : ℕ → ℚ)
    (rs : Finset ℤ) (v : ℤ → ℚ) : ℚ[X] :=
  (∑ d ∈ es, C (u d * tauMonomial k d)) +
    ∑ r ∈ rs, C (v r) * tauPolePoly k r

/-- The binomial and reflected-pole expansion of tau at `g(-1-x)`. -/
def reflectedMoment (k : ℕ) (es : Finset ℕ) (u : ℕ → ℚ)
    (rs : Finset ℤ) (v : ℤ → ℚ) : ℚ[X] :=
  (∑ d ∈ es, C (u d * ((-1 : ℚ) ^ d *
    (∑ i ∈ Finset.range (d + 1), (Nat.choose d i : ℚ) * tauMonomial k i)))) +
  ∑ r ∈ rs, C (v r) * (-tauPolePoly k (-1 - r))

/-- Reflection assembled over both complete finite generator families. -/
theorem finite_span_reflection (k : ℕ) (hk : 1 ≤ k)
    (es : Finset ℕ) (u : ℕ → ℚ) (rs : Finset ℤ) (v : ℤ → ℚ) :
    reflectedMoment k es u rs v = -tauFiniteSpan k es u rs v := by
  unfold reflectedMoment tauFiniteSpan
  have hm : (∑ d ∈ es, C (u d * ((-1 : ℚ) ^ d *
      (∑ i ∈ Finset.range (d + 1), (Nat.choose d i : ℚ) * tauMonomial k i)))) =
      -(∑ d ∈ es, C (u d * tauMonomial k d)) := by
    calc
      _ = ∑ d ∈ es, -(C (u d * tauMonomial k d)) := by
        apply Finset.sum_congr rfl
        intro d hd
        rw [tau_reflection_monomial k d hk]
        simp only [mul_neg, Polynomial.C_neg]
      _ = _ := by rw [Finset.sum_neg_distrib]
  have hp : (∑ r ∈ rs, C (v r) * (-tauPolePoly k (-1 - r))) =
      -(∑ r ∈ rs, C (v r) * tauPolePoly k r) := by
    calc
      _ = ∑ r ∈ rs, -(C (v r) * tauPolePoly k r) := by
        apply Finset.sum_congr rfl
        intro r hr
        rw [tauPolePoly_reflect k r]
        ring
      _ = _ := by rw [Finset.sum_neg_distrib]
  rw [hm, hp]
  ring

/-- Difference identity on all finite sums of admissible simple poles.
The excluded labels are retained verbatim from the manuscript. -/
theorem finite_pole_difference (k : ℕ) (rs : Finset ℤ) (v : ℤ → ℚ)
    (hr : ∀ r ∈ rs, r ≠ 0 ∧ r ≠ 1) :
    (∑ r ∈ rs, C (v r) * (tauPolePoly k (r - 1) - tauPolePoly k r)) =
      ∑ r ∈ rs, C (v r * (-((r : ℚ) ^ (2 * k + 1))⁻¹)) := by
  apply Finset.sum_congr rfl
  intro r hrs
  rw [tau_difference_pole k r (hr r hrs).1 (hr r hrs).2]
  rw [← Polynomial.C_mul]

end LeanPaper.PullbackReflection
