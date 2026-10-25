import LeanPaper.Section2TauLinear
import Mathlib.Algebra.Algebra.Hom.Rat
import Mathlib.Analysis.Calculus.Deriv.ZPow

/-! Literal x ↦ x+1 substitution on the tau rational-function domain and the
finite-difference law, with its actual analytic derivative for simple poles. -/
noncomputable section
open scoped BigOperators
open Polynomial
namespace LeanPaper.Section2RatFuncTranslation
open Section2RepresentationIndependence Section2PoleLinearSpace
open Section2TauRepresentation Section2TauLinear Zetahyperbolic

def translatePolynomial (p : ℚ[X]) : ℚ[X] := p.comp (X + 1)

def translatePolyHom : ℚ[X] →+* RatFunc ℚ :=
  (algebraMap ℚ[X] (RatFunc ℚ)).comp (Polynomial.compRingHom (X + 1))

theorem translatePolyHom_injective : Function.Injective translatePolyHom := by
  intro p q hpq
  have h : p.comp (X+1) = q.comp (X+1) := (RatFunc.algebraMap_injective ℚ) hpq
  have hh := congrArg (fun p : ℚ[X] => p.comp (X-1)) h
  have hinner : (X+1 : ℚ[X]).comp (X-1) = X := by simp
  simpa only [Polynomial.comp_assoc, hinner, Polynomial.comp_X] using hh

def translate : RatFunc ℚ →ₐ[ℚ] RatFunc ℚ :=
  (RatFunc.liftRingHom translatePolyHom
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _ translatePolyHom_injective)).toRatAlgHom

@[simp] theorem translate_polynomial (p : ℚ[X]) :
    translate (algebraMap ℚ[X] (RatFunc ℚ) p) =
      algebraMap ℚ[X] (RatFunc ℚ) (translatePolynomial p) := by
  exact RatFunc.liftRingHom_algebraMap _ _ p

@[simp] theorem translate_pole (r : ℤ) :
    translate (pole r : RatFunc ℚ) = (pole (r-1) : RatFunc ℚ) := by
  change translate ((algebraMap ℚ[X] (RatFunc ℚ) (X - C (r : ℚ)))⁻¹) = _
  rw [map_inv₀, translate_polynomial]
  have h : translatePolynomial (X - C (r : ℚ)) = X - C ((r-1 : ℤ) : ℚ) := by
    simp only [translatePolynomial, sub_comp, X_comp, C_comp, Int.cast_sub,
      Int.cast_one, map_sub, map_one]
    ring
  rw [h]
  rfl

theorem translate_mem (f : TauSpace) : translate (f : RatFunc ℚ) ∈ TauSpace := by
  obtain ⟨F, hF⟩ := f.property
  have hf : f = polynomial F.polynomial + ∑ r ∈ F.support, F.residue r • pole r := by
    exact (Subtype.ext hF.symm).trans (representation_decomposition F)
  rw [hf]
  simp only [Submodule.coe_add, Submodule.coe_sum, Submodule.coe_smul,
    map_add, map_sum, map_smul]
  apply Submodule.add_mem
  · change translate (algebraMap ℚ[X] (RatFunc ℚ) F.polynomial) ∈ TauSpace
    rw [translate_polynomial]
    exact (polynomial (translatePolynomial F.polynomial)).property
  · apply Submodule.sum_mem
    intro r hr
    rw [translate_pole]
    exact TauSpace.smul_mem _ (pole (r-1)).property

def translation : TauSpace →ₗ[ℚ] TauSpace where
  toFun f := ⟨translate f, translate_mem f⟩
  map_add' f g := Subtype.ext (map_add translate (f : RatFunc ℚ) (g : RatFunc ℚ))
  map_smul' c f := Subtype.ext (map_smul translate c (f : RatFunc ℚ))

@[simp] theorem translation_polynomial (p : ℚ[X]) :
    translation (polynomial p) = polynomial (translatePolynomial p) :=
  Subtype.ext (translate_polynomial p)

private theorem tauPolynomial_C_mul (k : ℕ) (c : ℚ) (p : ℚ[X]) :
    tauPolynomial k (C c * p) = C c * tauPolynomial k p := by
  simpa only [Polynomial.smul_eq_C_mul] using (tauPolynomial k).map_smul c p

private theorem tauPolynomial_add_one_pow (k d : ℕ) :
    tauPolynomial k ((X+1)^d) =
      C (∑ i ∈ Finset.range (d+1), (Nat.choose d i : ℚ) * tauMonomial k i) := by
  rw [add_pow, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [one_pow, mul_one]
  rw [show (Nat.choose d i : ℚ[X]) = C (Nat.choose d i : ℚ) by simp,
    mul_comm, C_mul_X_pow_eq_monomial, tauPolynomial_monomial]

theorem tauPolynomial_difference (k : ℕ) (hk : 1 ≤ k) (p : ℚ[X]) :
    tauPolynomial k (translatePolynomial p) - tauPolynomial k p = C (p.coeff (2*k)) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      simp only [translatePolynomial, add_comp, map_add, coeff_add] at *
      rw [map_add]
      linear_combination hp + hq
  | monomial d c =>
      change tauPolynomial k ((monomial d c).comp (X+1)) - _ = _
      rw [monomial_comp, tauPolynomial_C_mul, tauPolynomial_add_one_pow,
        tauPolynomial_monomial, ← map_mul, ← map_sub, ← mul_sub,
        Section2FiniteDifference.tau_monomial_difference k d hk]
      by_cases h : d = 2*k
      · simp [h]
      · simp [h, Ne.symm h]

@[simp] theorem translation_pole (r : ℤ) : translation (pole r) = pole (r-1) :=
  Subtype.ext (translate_pole r)

/-- Manuscript Lemma 2.3(2) on its exact admissible pole set. -/
theorem tau_difference_pole (k : ℕ) (r : ℤ) (hr0 : r ≠ 0) (hr1 : r ≠ 1) :
    tau k (translation (pole r) - pole r) = C (-((r : ℚ)^(2*k+1))⁻¹) := by
  rw [map_sub, translation_pole, tau_pole, tau_pole]
  exact Zetahyperbolic.tau_difference_pole k r hr0 hr1

/-- The simple-pole finite-difference identity extends to its full rational span. -/
theorem tau_difference_span (k : ℕ) (s : Finset ℤ) (c : ℤ → ℚ)
    (hs : ∀ r ∈ s, r ≠ 0 ∧ r ≠ 1) :
    tau k (translation (∑ r ∈ s, c r • pole r) - ∑ r ∈ s, c r • pole r) =
      C (∑ r ∈ s, c r * (-((r : ℚ)^(2*k+1))⁻¹)) := by
  have he : translation (∑ r ∈ s, c r • pole r) - ∑ r ∈ s, c r • pole r =
      ∑ r ∈ s, c r • (translation (pole r) - pole r) := by
    simp only [map_sum, map_smul, smul_sub, Finset.sum_sub_distrib]
  rw [he, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro r hr
  rw [map_smul, tau_difference_pole k r (hs r hr).1 (hs r hr).2]
  simp [Polynomial.smul_C, smul_eq_mul]

/-- The correction is the actual normalized even derivative of the pole. -/
theorem pole_even_derivative (k : ℕ) (r : ℝ) :
    (deriv^[2*k] (fun x : ℝ => (x-r)⁻¹)) 0 / ((2*k).factorial : ℝ) =
      -(r^(2*k+1))⁻¹ := by
  have h := congrFun (iter_deriv_inv_linear_sub (2*k) (1 : ℝ) r) 0
  simp only [one_mul, mul_zero, zero_sub, one_pow, mul_one] at h
  have he : (-1 - ((2*k : ℕ) : ℤ)) = -((2*k+1 : ℕ) : ℤ) := by omega
  have hs : (-1 : ℝ)^(2*k) = 1 := by simp [pow_mul]
  rw [hs, one_mul, he, zpow_neg, zpow_natCast] at h
  have hn : (-r)^(2*k+1) = -(r^(2*k+1)) := by
    simp [pow_succ, pow_mul]
  rw [hn, inv_neg] at h
  rw [h]
  have hf : ((2*k).factorial : ℝ) ≠ 0 := by positivity
  field_simp [hf] <;> ring

/-- Function-level difference and actual calculus derivative, exactly as (2.7). -/
theorem tau_difference_derivative (k : ℕ) (r : ℤ)
    (hr0 : r ≠ 0) (hr1 : r ≠ 1) (x : ℝ) :
    ((tau k (translation (pole r) - pole r)).map (algebraMap ℚ ℝ)).eval x =
      (deriv^[2*k] (fun y : ℝ => (y-(r : ℝ))⁻¹)) 0 /
        ((2*k).factorial : ℝ) := by
  rw [tau_difference_pole k r hr0 hr1, pole_even_derivative]
  simp

end LeanPaper.Section2RatFuncTranslation
