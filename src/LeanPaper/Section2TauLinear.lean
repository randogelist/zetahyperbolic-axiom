import LeanPaper.Section2PoleLinearSpace

/-!
The actual Bernoulli/harmonic tau is a rational linear map on the rational
functions with finite simple integer poles. Its even-pole cancellation is
proved in RatFunc, including the endpoint j=1, directly from harmonic moments.
This proves the statement of manuscript Theorem 5.4 without using the sign
errors in its printed intermediate calculation.
-/
noncomputable section
open scoped BigOperators
open Polynomial
namespace LeanPaper.Section2TauLinear
open Section2RepresentationIndependence Section2PoleLinearSpace
open Section2TauRepresentation Zetahyperbolic

abbrev TauSpace := poleSubmodule (fun r : ℤ => (r : ℚ))

def tau (k : ℕ) : TauSpace →ₗ[ℚ] ℚ[X] :=
  liftMoment (fun r : ℤ => (r : ℚ)) Int.cast_injective (tauPolynomial k) (tauPolePoly k)

def polynomial (p : ℚ[X]) : TauSpace :=
  ⟨algebraMap ℚ[X] (RatFunc ℚ) p, ⟨⟨p, ∅, fun _ => 0⟩, by simp [realization]⟩⟩

def pole (r : ℤ) : TauSpace :=
  ⟨(algebraMap ℚ[X] (RatFunc ℚ) (X - C (r : ℚ)))⁻¹,
    ⟨⟨0, {r}, fun _ => 1⟩, by simp [realization]⟩⟩

theorem tau_polynomial (k : ℕ) (p : ℚ[X]) : tau k (polynomial p) = tauPolynomial k p := by
  have h := liftMoment_eq (fun r : ℤ => (r : ℚ)) Int.cast_injective
    (tauPolynomial k) (tauPolePoly k) (⟨p, ∅, fun _ => 0⟩ : SimplePoleForm ℤ)
  simpa [tau, polynomial, moment, realization] using h

theorem tau_pole (k : ℕ) (r : ℤ) : tau k (pole r) = tauPolePoly k r := by
  have h := liftMoment_eq (fun r : ℤ => (r : ℚ)) Int.cast_injective
    (tauPolynomial k) (tauPolePoly k) (⟨0, {r}, fun _ => 1⟩ : SimplePoleForm ℤ)
  simpa [tau, pole, moment, realization] using h

theorem tau_eq_existing (k : ℕ) (f : TauSpace) :
    tau k f = tauOnDomain k ⟨(f : RatFunc ℚ), f.property⟩ := rfl

theorem tau_representation (k : ℕ) (F : SimplePoleForm ℤ) :
    tau k ⟨realization (fun r : ℤ => (r : ℚ)) F, ⟨F, rfl⟩⟩ =
      moment (tauPolynomial k) (tauPolePoly k) F :=
  liftMoment_eq _ Int.cast_injective _ _ F

def evenPolePair (j : ℕ) : TauSpace := pole (j : ℤ) - pole (-(j : ℤ))

theorem evenPolePair_coe (j : ℕ) :
    (evenPolePair j : RatFunc ℚ) =
      (algebraMap ℚ[X] (RatFunc ℚ) (X - C (j : ℚ)))⁻¹ -
      (algebraMap ℚ[X] (RatFunc ℚ) (X + C (j : ℚ)))⁻¹ := by
  simp [evenPolePair, pole]

theorem evenPolePair_cancellation (k j : ℕ) (hj : 1 ≤ j) :
    tau k (evenPolePair j) = C (((j : ℚ) ^ (2 * k + 1))⁻¹) := by
  rw [evenPolePair, map_sub, tau_pole, tau_pole]
  have hdpos : dIndex (j : ℤ) = j := by
    simp [dIndex, Int.toNat_of_nonneg (by omega : (0 : ℤ) ≤ (j : ℤ))]
  have hdneg : dIndex (-(j : ℤ)) = j - 1 := by
    have hneg : ¬ (0 : ℤ) ≤ -(j : ℤ) := by omega
    unfold dIndex
    rw [if_neg hneg]
    have hcast : -(-(j : ℤ)) - 1 = ((j - 1 : ℕ) : ℤ) := by omega
    rw [hcast]
    simp
  have hidx : j - 1 + 1 = j := by omega
  have hrec := harmonicWeight_succ (2 * k + 1) (j - 1)
  rw [hidx] at hrec
  simp only [tauPolePoly, hdpos, hdneg, hrec, map_add]
  ring

/-- Cancellation extends by the actual lifted rational linear map. -/
theorem finite_evenPolePair_cancellation (k : ℕ) (s : Finset ℕ)
    (c : ℕ → ℚ) (hs : ∀ j ∈ s, 1 ≤ j) :
    tau k (∑ j ∈ s, c j • evenPolePair j) =
      C (∑ j ∈ s, c j * (((j : ℚ) ^ (2 * k + 1))⁻¹)) := by
  rw [map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [map_smul, evenPolePair_cancellation k j (hs j hj)]
  simp [Polynomial.smul_C, smul_eq_mul]

theorem representation_decomposition (F : SimplePoleForm ℤ) :
    (⟨realization (fun r : ℤ => (r : ℚ)) F, ⟨F, rfl⟩⟩ : TauSpace) =
      polynomial F.polynomial + ∑ r ∈ F.support, F.residue r • pole r := by
  apply Subtype.ext
  have hc (c : ℚ) : RatFunc.C c = (algebraMap ℚ (RatFunc ℚ)) c :=
    (map_ratCast (RatFunc.C (K := ℚ)) c).trans (map_ratCast (algebraMap ℚ (RatFunc ℚ)) c).symm
  simp only [Submodule.coe_add, Submodule.coe_sum, Submodule.coe_smul]
  simp only [realization, polynomial, pole, Algebra.smul_def, div_eq_mul_inv,
    RatFunc.algebraMap_C, hc]

/-- Correct sign in the intermediate reflection step of the printed 5.4 proof. -/
theorem evenPolePair_reflection_relation (k : ℕ) (j : ℤ) :
    tau k (pole (-j)) = tau k (pole (j-1)) := by
  rw [tau_pole, tau_pole]
  have h := tauPolePoly_reflect k (j-1)
  simpa only [show (-1-(j-1) : ℤ) = -j by omega] using h

/-- The printed j=1 division step uses the even difference where the sum is
required. Already at k=1 and x=0 that displayed identity is false. The final
cancellation theorem above remains true and is proved independently. -/
theorem printed_evenPair_division_fails_at_zero :
    (0 : ℚ)^3 / (1 - 0^2) ≠
      -(0 : ℚ) - (1/2 : ℚ) * ((0-1)⁻¹ - (0+1)⁻¹) := by
  norm_num

/-- The B₁ exceptional term disproves the printed assertion that only odd
monomial degrees contribute. The reflection theorem itself remains valid. -/
theorem even_monomial_Bernoulli_exception : tauMonomial 1 2 = -(1/2 : ℚ) := by
  norm_num [tauMonomial, _root_.bernoulli_one]

end LeanPaper.Section2TauLinear
