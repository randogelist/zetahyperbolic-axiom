import LeanPaper.Section2TauLinear
import Mathlib.Algebra.Algebra.Hom.Rat

/-! Actual rational-function substitution x ↦ -1-x and its tau reflection law. -/
noncomputable section
open scoped BigOperators
open Polynomial
namespace LeanPaper.Section2RatFuncReflection
open Section2RepresentationIndependence Section2PoleLinearSpace
open Section2TauRepresentation Section2TauLinear Zetahyperbolic

def reflectPolynomial (p : ℚ[X]) : ℚ[X] := p.comp (-1 - X)

theorem reflectPolynomial_involutive : Function.Involutive reflectPolynomial := by
  intro p
  simp only [reflectPolynomial, Polynomial.comp_assoc]
  have h : (-1 - X : ℚ[X]).comp (-1 - X) = X := by simp
  rw [h, Polynomial.comp_X]

def reflectPolyHom : ℚ[X] →+* RatFunc ℚ :=
  (algebraMap ℚ[X] (RatFunc ℚ)).comp (Polynomial.compRingHom (-1 - X))

theorem reflectPolyHom_injective : Function.Injective reflectPolyHom :=
  (RatFunc.algebraMap_injective ℚ).comp reflectPolynomial_involutive.injective

def reflect : RatFunc ℚ →ₐ[ℚ] RatFunc ℚ :=
  (RatFunc.liftRingHom reflectPolyHom
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _ reflectPolyHom_injective)).toRatAlgHom

@[simp] theorem reflect_scalar (c : ℚ) :
    reflect ((algebraMap ℚ (RatFunc ℚ)) c) = (algebraMap ℚ (RatFunc ℚ)) c := by
  have hc : (algebraMap ℚ (RatFunc ℚ)) c = (c : RatFunc ℚ) :=
    map_ratCast (algebraMap ℚ (RatFunc ℚ)) c
  rw [hc]
  exact map_ratCast reflect.toRingHom c

@[simp] theorem reflect_polynomial (p : ℚ[X]) :
    reflect (algebraMap ℚ[X] (RatFunc ℚ) p) =
      algebraMap ℚ[X] (RatFunc ℚ) (reflectPolynomial p) := by
  exact RatFunc.liftRingHom_algebraMap _ _ p

@[simp] theorem reflect_pole (r : ℤ) :
    reflect (pole r : RatFunc ℚ) = -(pole (-1-r) : RatFunc ℚ) := by
  change reflect ((algebraMap ℚ[X] (RatFunc ℚ) (X - C (r : ℚ)))⁻¹) = _
  rw [map_inv₀, reflect_polynomial]
  have h : reflectPolynomial (X - C (r : ℚ)) = -(X - C ((-1-r : ℤ) : ℚ)) := by
    simp only [reflectPolynomial, sub_comp, X_comp, C_comp, Int.cast_sub, Int.cast_neg,
      Int.cast_one, map_sub, map_neg, map_one]
    ring
  rw [h, map_neg, inv_neg]
  rfl

private theorem polynomial_C_mul (k : ℕ) (c : ℚ) (p : ℚ[X]) :
    tauPolynomial k (C c * p) = C c * tauPolynomial k p := by
  simpa only [Polynomial.smul_eq_C_mul] using (tauPolynomial k).map_smul c p

private theorem polynomial_X_pow (k d : ℕ) :
    tauPolynomial k (X ^ d) = C (tauMonomial k d) := by
  rw [← Polynomial.monomial_one_right_eq_X_pow]
  simpa using tauPolynomial_monomial k d 1

private theorem polynomial_add_one_pow (k d : ℕ) :
    tauPolynomial k ((X + 1)^d) =
      C (∑ i ∈ Finset.range (d + 1), (Nat.choose d i : ℚ) * tauMonomial k i) := by
  rw [add_pow, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [one_pow, mul_one]
  rw [show (Nat.choose d i : ℚ[X]) = C (Nat.choose d i : ℚ) by simp,
    mul_comm, C_mul_X_pow_eq_monomial, tauPolynomial_monomial]

theorem tauPolynomial_reflection (k : ℕ) (hk : 1 ≤ k) (p : ℚ[X]) :
    tauPolynomial k (reflectPolynomial p) = -tauPolynomial k p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      simp only [reflectPolynomial, add_comp, map_add] at *
      rw [hp, hq]
      abel
  | monomial d c =>
      have heq : reflectPolynomial (monomial d c) =
          C (c * (-1 : ℚ)^d) * (X+1)^d := by
        simp only [reflectPolynomial, monomial_comp, map_mul, map_pow, map_neg, map_one]
        rw [show (-1-X : ℚ[X]) = -1*(X+1) by ring, mul_pow]
        ring
      rw [heq, polynomial_C_mul, polynomial_add_one_pow, ← map_mul,
        tauPolynomial_monomial]
      rw [mul_assoc, tau_reflection_monomial k d hk]
      simp

/-- Actual substitution preserves the complete simple-integer-pole subspace. -/
theorem reflect_mem (f : TauSpace) : reflect (f : RatFunc ℚ) ∈ TauSpace := by
  obtain ⟨F, hF⟩ := f.property
  have hf : f = polynomial F.polynomial + ∑ r ∈ F.support, F.residue r • pole r := by
    exact (Subtype.ext hF.symm).trans (representation_decomposition F)
  rw [hf]
  simp only [Submodule.coe_add, Submodule.coe_sum, Submodule.coe_smul,
    map_add, map_sum]
  apply Submodule.add_mem
  · change reflect (algebraMap ℚ[X] (RatFunc ℚ) F.polynomial) ∈ TauSpace
    rw [reflect_polynomial]
    exact (polynomial (reflectPolynomial F.polynomial)).property
  · apply Submodule.sum_mem
    intro r hr
    simp only [Algebra.smul_def, map_mul, reflect_scalar, reflect_pole]
    simpa only [Algebra.smul_def, map_ratCast] using
      TauSpace.smul_mem (F.residue r) (TauSpace.neg_mem (pole (-1-r)).property)

/-- Reflection as an operator on actual rational functions in the tau domain. -/
def reflection : TauSpace →ₗ[ℚ] TauSpace where
  toFun f := ⟨reflect f, reflect_mem f⟩
  map_add' f g := Subtype.ext (map_add reflect (f : RatFunc ℚ) (g : RatFunc ℚ))
  map_smul' c f := by
    apply Subtype.ext
    simp only [Submodule.coe_smul, Algebra.smul_def, map_mul, reflect_scalar, RingHom.id_apply]

@[simp] theorem reflection_polynomial (p : ℚ[X]) :
    reflection (polynomial p) = polynomial (reflectPolynomial p) := by
  apply Subtype.ext
  exact reflect_polynomial p

@[simp] theorem reflection_pole (r : ℤ) :
    reflection (pole r) = -pole (-1-r) := by
  apply Subtype.ext
  exact reflect_pole r

/-- Full manuscript Lemma 2.3(1), on the actual RatFunc domain. -/
theorem tau_reflection (k : ℕ) (hk : 1 ≤ k) (f : TauSpace) :
    tau k (reflection f) = -tau k f := by
  obtain ⟨F, hF⟩ := f.property
  have hf : f = polynomial F.polynomial + ∑ r ∈ F.support, F.residue r • pole r := by
    have h := representation_decomposition F
    have hval : f = ⟨realization (fun r : ℤ => (r : ℚ)) F, ⟨F, rfl⟩⟩ :=
      Subtype.ext hF.symm
    exact hval.trans h
  rw [hf]
  simp only [map_add, map_sum, map_smul, reflection_polynomial, reflection_pole,
    map_neg, tau_polynomial, tau_pole, tauPolynomial_reflection k hk,
    tauPolePoly_reflect, smul_neg, Finset.sum_neg_distrib]
  abel

end LeanPaper.Section2RatFuncReflection
