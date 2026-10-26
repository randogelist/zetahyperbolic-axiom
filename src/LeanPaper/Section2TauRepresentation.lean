import LeanPaper.Section2RepresentationIndependence
import LeanPaper.Section2FiniteDifference

/-!
The Bernoulli/integer-pole τ functional is well-defined on actual rational
functions represented by finite simple integer-pole expressions. This includes
the previously proved reflection and admissible difference moment formulas:
their values do not depend on the chosen finite monomial or pole support.
-/

noncomputable section
open scoped BigOperators
open Polynomial

namespace LeanPaper.Section2TauRepresentation
open Zetahyperbolic PullbackReflection Section2FiniteDifference
open Section2RepresentationIndependence

def tauPolynomial (k : ℕ) : ℚ[X] →ₗ[ℚ] ℚ[X] :=
  Polynomial.lsum fun d =>
    (LinearMap.id : ℚ →ₗ[ℚ] ℚ).smulRight (C (tauMonomial k d))

theorem tauPolynomial_monomial (k d : ℕ) (c : ℚ) :
    tauPolynomial k (Polynomial.monomial d c) = C (c * tauMonomial k d) := by
  change (Polynomial.monomial d c).sum
    (fun n a => a • C (tauMonomial k n)) = _
  rw [Polynomial.sum_monomial_index _ _ (by simp)]
  simp [Polynomial.smul_C, smul_eq_mul]

def finiteForm (es : Finset ℕ) (u : ℕ → ℚ) (rs : Finset ℤ) (v : ℤ → ℚ) :
    SimplePoleForm ℤ :=
  ⟨∑ d ∈ es, Polynomial.monomial d (u d), rs, v⟩

def finiteSpanRatFunc (es : Finset ℕ) (u : ℕ → ℚ)
    (rs : Finset ℤ) (v : ℤ → ℚ) : RatFunc ℚ :=
  realization (fun r : ℤ => (r : ℚ)) (finiteForm es u rs v)

theorem finiteForm_coefficient (es : Finset ℕ) (u : ℕ → ℚ)
    (rs : Finset ℤ) (v : ℤ → ℚ) (d : ℕ) :
    (finiteForm es u rs v).polynomial.coeff d = if d ∈ es then u d else 0 := by
  classical
  simp [finiteForm, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial]

theorem tauFiniteSpan_eq_moment (k : ℕ) (es : Finset ℕ) (u : ℕ → ℚ)
    (rs : Finset ℤ) (v : ℤ → ℚ) :
    tauFiniteSpan k es u rs v =
      moment (tauPolynomial k) (tauPolePoly k) (finiteForm es u rs v) := by
  simp only [moment, finiteForm, map_sum, tauPolynomial_monomial, tauFiniteSpan]

theorem tauFiniteSpan_representation_independent (k : ℕ)
    (es fs : Finset ℕ) (u w : ℕ → ℚ) (rs ts : Finset ℤ) (v z : ℤ → ℚ)
    (h : finiteSpanRatFunc es u rs v = finiteSpanRatFunc fs w ts z) :
    tauFiniteSpan k es u rs v = tauFiniteSpan k fs w ts z := by
  rw [tauFiniteSpan_eq_moment, tauFiniteSpan_eq_moment]
  exact moment_representation_independent (fun r : ℤ => (r : ℚ))
    Int.cast_injective (tauPolynomial k) (tauPolePoly k)
    (finiteForm es u rs v) (finiteForm fs w ts z) h

/-- Actual rational-function domain of polynomial plus finite simple integer
poles. The representation witness concerns only algebraic form. -/
def TauDomain := Set.range (realization (fun r : ℤ => (r : ℚ)))

def tauOnDomain (k : ℕ) (f : TauDomain) : ℚ[X] :=
  moment (tauPolynomial k) (tauPolePoly k) (Classical.choose f.property)

theorem tauOnDomain_eq (k : ℕ) (F : SimplePoleForm ℤ) :
    tauOnDomain k ⟨realization (fun r : ℤ => (r : ℚ)) F, ⟨F, rfl⟩⟩ =
      moment (tauPolynomial k) (tauPolePoly k) F := by
  apply moment_representation_independent (fun r : ℤ => (r : ℚ)) Int.cast_injective
  exact Classical.choose_spec
    (show realization (fun r : ℤ => (r : ℚ)) F ∈ TauDomain from ⟨F, rfl⟩)

theorem tauOnDomain_eq_finiteSpan (k : ℕ) (es : Finset ℕ) (u : ℕ → ℚ)
    (rs : Finset ℤ) (v : ℤ → ℚ) :
    tauOnDomain k ⟨finiteSpanRatFunc es u rs v, ⟨finiteForm es u rs v, rfl⟩⟩ =
      tauFiniteSpan k es u rs v := by
  rw [tauFiniteSpan_eq_moment]
  exact tauOnDomain_eq k (finiteForm es u rs v)

theorem reflectedMoment_representation_independent (k : ℕ) (hk : 1 ≤ k)
    (es fs : Finset ℕ) (u w : ℕ → ℚ) (rs ts : Finset ℤ) (v z : ℤ → ℚ)
    (h : finiteSpanRatFunc es u rs v = finiteSpanRatFunc fs w ts z) :
    reflectedMoment k es u rs v = reflectedMoment k fs w ts z := by
  rw [finite_span_reflection k hk es u rs v, finite_span_reflection k hk fs w ts z]
  exact congrArg Neg.neg (tauFiniteSpan_representation_independent k es fs u w rs ts v z h)

def differenceCorrection (k : ℕ) (es : Finset ℕ) (u : ℕ → ℚ)
    (rs : Finset ℤ) (v : ℤ → ℚ) : ℚ[X] :=
  C (if 2 * k ∈ es then u (2 * k) else 0) +
    ∑ r ∈ rs, C (v r * (-((r : ℚ) ^ (2 * k + 1))⁻¹))

theorem differenceCorrection_eq_moment (k : ℕ) (es : Finset ℕ) (u : ℕ → ℚ)
    (rs : Finset ℤ) (v : ℤ → ℚ) :
    differenceCorrection k es u rs v =
      moment (fun p => C (p.coeff (2 * k)))
        (fun r : ℤ => C (-((r : ℚ) ^ (2 * k + 1))⁻¹))
        (finiteForm es u rs v) := by
  unfold differenceCorrection moment
  dsimp only
  rw [finiteForm_coefficient]
  simp only [finiteForm, map_mul]

theorem differenceCorrection_representation_independent (k : ℕ)
    (es fs : Finset ℕ) (u w : ℕ → ℚ) (rs ts : Finset ℤ) (v z : ℤ → ℚ)
    (h : finiteSpanRatFunc es u rs v = finiteSpanRatFunc fs w ts z) :
    differenceCorrection k es u rs v = differenceCorrection k fs w ts z := by
  rw [differenceCorrection_eq_moment, differenceCorrection_eq_moment]
  exact moment_representation_independent (fun r : ℤ => (r : ℚ)) Int.cast_injective
    _ _ (finiteForm es u rs v) (finiteForm fs w ts z) h

theorem translatedMoment_representation_independent (k : ℕ) (hk : 1 ≤ k)
    (es fs : Finset ℕ) (u w : ℕ → ℚ) (rs ts : Finset ℤ) (v z : ℤ → ℚ)
    (hr : ∀ r ∈ rs, r ≠ 0 ∧ r ≠ 1) (ht : ∀ r ∈ ts, r ≠ 0 ∧ r ≠ 1)
    (h : finiteSpanRatFunc es u rs v = finiteSpanRatFunc fs w ts z) :
    translatedMoment k es u rs v = translatedMoment k fs w ts z := by
  have hF := finite_span_difference_coefficient k hk es u rs v hr
  have hG := finite_span_difference_coefficient k hk fs w ts z ht
  change translatedMoment k es u rs v - tauFiniteSpan k es u rs v =
    differenceCorrection k es u rs v at hF
  change translatedMoment k fs w ts z - tauFiniteSpan k fs w ts z =
    differenceCorrection k fs w ts z at hG
  rw [tauFiniteSpan_representation_independent k es fs u w rs ts v z h,
    differenceCorrection_representation_independent k es fs u w rs ts v z h] at hF
  have hc := congrArg (fun p : ℚ[X] => p + tauFiniteSpan k fs w ts z)
    (hF.trans hG.symm)
  simpa only [sub_add_cancel] using hc

end LeanPaper.Section2TauRepresentation
