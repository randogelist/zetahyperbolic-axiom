import LeanPaper.Section2TauLinear
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Algebra.Algebra.Hom.Rat

/-! The actual square substitution and weighted pullback from the simple
negative-square-pole domain into the simple-integer-pole domain. -/
noncomputable section
open scoped BigOperators nonZeroDivisors
open Polynomial
namespace LeanPaper.Section2RatFuncPullback
open Section2RepresentationIndependence Section2PoleLinearSpace
open Section2TauRepresentation Section2TauLinear Zetahyperbolic

def substitutionPolynomial : ℚ[X] →ₐ[ℚ] ℚ[X] := aeval (-X^2 : ℚ[X])

theorem substitutionPolynomial_apply (q : ℚ[X]) :
    substitutionPolynomial q = q.comp (-X^2) := rfl

theorem scalar_cast (a : ℚ) : (algebraMap ℚ (RatFunc ℚ)) a = (a : RatFunc ℚ) :=
  map_ratCast (algebraMap ℚ (RatFunc ℚ)) a

theorem substitutionPolynomial_preserves_nonzero :
    (ℚ[X])⁰ ≤ ((ℚ[X])⁰).comap substitutionPolynomial := by
  intro q hq
  change substitutionPolynomial q ∈ (ℚ[X])⁰
  rw [mem_nonZeroDivisors_iff_ne_zero] at hq ⊢
  change q.comp (-X^2) ≠ 0
  intro h
  rcases comp_eq_zero_iff.mp h with hz | ⟨_, hc⟩
  · exact hq hz
  · have hh := congrArg (fun p : ℚ[X] => p.coeff 2) hc
    norm_num at hh

def substitution : RatFunc ℚ →ₐ[ℚ] RatFunc ℚ :=
  (RatFunc.mapRingHom substitutionPolynomial substitutionPolynomial_preserves_nonzero).toRatAlgHom

theorem substitution_polynomial (q : ℚ[X]) :
    substitution (algebraMap ℚ[X] (RatFunc ℚ) q) =
      algebraMap ℚ[X] (RatFunc ℚ) (q.comp (-X^2)) := by
  change RatFunc.map substitutionPolynomial substitutionPolynomial_preserves_nonzero
    (algebraMap ℚ[X] (RatFunc ℚ) q) = _
  simpa only [map_one, div_one, substitutionPolynomial_apply] using
    RatFunc.map_apply_div substitutionPolynomial substitutionPolynomial_preserves_nonzero q 1

def polePolynomial (k : ℕ) (a : ℚ) : ℚ[X] :=
  -∑ e ∈ Finset.range k, monomial (2*e+1) (a^(2*(k-1-e)))

theorem tau_polePolynomial (k : ℕ) (hk : 1 ≤ k) (a : ℚ) :
    tauPolynomial k (polePolynomial k a) = C (-tauMonomial k (2*k-1)) := by
  unfold polePolynomial
  rw [map_neg, map_sum]
  have hsum : (∑ e ∈ Finset.range k,
      tauPolynomial k (monomial (2*e+1) (a^(2*(k-1-e))))) =
      C (tauMonomial k (2*k-1)) := by
    rw [Finset.sum_eq_single (k-1)]
    · rw [tauPolynomial_monomial]
      simp only [Nat.sub_self, mul_zero, pow_zero, one_mul]
      congr 2
      omega
    · intro e he hne
      rw [tauPolynomial_monomial]
      have he' := Finset.mem_range.mp he
      have hcut : ¬ 2*k-1 ≤ 2*e+1 := by omega
      simp [tauMonomial, hcut]
    · intro hn
      exact (hn (Finset.mem_range.mpr (by omega))).elim
  rw [hsum, map_neg]

theorem polePolynomial_eq_geometric (k : ℕ) (a : ℚ) :
    polePolynomial k a =
      -X * ∑ e ∈ Finset.range k, (X^2)^e * (C a^2)^(k-1-e) := by
  unfold polePolynomial
  rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro e he
  have hc : C (a^(2*(k-1-e))) = ((C a)^2)^(k-1-e) := by
    rw [Polynomial.C_pow, pow_mul]
  rw [← C_mul_X_pow_eq_monomial, hc]
  simp only [pow_mul, pow_succ]
  ring

theorem pole_division_identity {K : Type*} [Field K] [CharZero K]
    (k : ℕ) (x a : K) (hminus : x-a ≠ 0) (hplus : x+a ≠ 0) :
    x^(2*k+1) / (a^2-x^2) =
      -x * (∑ e ∈ Finset.range k, (x^2)^e * (a^2)^(k-1-e)) -
        (a^(2*k)/2) * ((x-a)⁻¹ + (x+a)⁻¹) := by
  have hd : a^2-x^2 ≠ 0 := by
    have h : a^2-x^2 = -(x-a)*(x+a) := by ring
    rw [h]
    exact mul_ne_zero (neg_ne_zero.mpr hminus) hplus
  have hg := (Commute.all (x^2) (a^2)).mul_geom_sum₂ k
  have hpoly : -x * (∑ e ∈ Finset.range k, (x^2)^e * (a^2)^(k-1-e)) *
      (a^2-x^2) = x^(2*k+1) - a^(2*k)*x := by
    calc
      _ = x * ((x^2-a^2) * ∑ e ∈ Finset.range k, (x^2)^e * (a^2)^(k-1-e)) := by ring
      _ = x * ((x^2)^k-(a^2)^k) := by rw [hg]
      _ = _ := by rw [← pow_mul, ← pow_mul, pow_succ]; ring
  apply (div_eq_iff hd).2
  have hpole : (a^(2*k)/2) * ((x-a)⁻¹ + (x+a)⁻¹) * (a^2-x^2) =
      -(a^(2*k)*x) := by
    field_simp
    ring
  rw [sub_mul, hpoly, hpole]
  ring

def pulledPole (k j : ℕ) : TauSpace :=
  polynomial (polePolynomial k (j : ℚ)) -
    (((j : ℚ)^(2*k))/2) • (pole (j : ℤ) + pole (-(j : ℤ)))

theorem tau_pulledPole (k j : ℕ) (hk : 1 ≤ k) (hj : 1 ≤ j) :
    tau k (pulledPole k j) = muPolePoly k j := by
  rw [pulledPole, map_sub, map_smul, map_add, tau_polynomial, tau_pole, tau_pole,
    tau_polePolynomial k hk, pullback_identity_pole k j hk hj,
    Polynomial.smul_eq_C_mul]

theorem rational_X_sub_ne_zero (a : ℚ) : (RatFunc.X : RatFunc ℚ) - RatFunc.C a ≠ 0 := by
  rw [← RatFunc.algebraMap_X, ← RatFunc.algebraMap_C, ← map_sub]
  exact RatFunc.algebraMap_ne_zero (X_sub_C_ne_zero a)

theorem rational_X_add_ne_zero (a : ℚ) : (RatFunc.X : RatFunc ℚ) + RatFunc.C a ≠ 0 := by
  simpa only [map_neg, sub_neg_eq_add] using rational_X_sub_ne_zero (-a)

theorem pulledPole_coe (k j : ℕ) :
    (pulledPole k j : RatFunc ℚ) =
      (RatFunc.X : RatFunc ℚ)^(2*k+1) /
        (RatFunc.C ((j : ℚ)^2) - RatFunc.X^2) := by
  have he := pole_division_identity k (RatFunc.X : RatFunc ℚ)
    (RatFunc.C (j : ℚ)) (rational_X_sub_ne_zero _) (rational_X_add_ne_zero _)
  rw [← map_pow] at he
  rw [he]
  simp only [pulledPole, Submodule.coe_sub, Submodule.coe_smul, Submodule.coe_add,
    polynomial, pole, polePolynomial_eq_geometric]
  simp only [map_mul, map_neg, map_sum, map_pow, RatFunc.algebraMap_X,
    RatFunc.algebraMap_C, map_sub, map_add, Int.cast_natCast, Int.cast_neg, sub_neg_eq_add]
  simp only [Algebra.smul_def, scalar_cast, Rat.cast_neg, Rat.cast_div,
    Rat.cast_pow, Rat.cast_ofNat, Rat.cast_natCast]
  have hC (a : ℚ) : RatFunc.C a = (a : RatFunc ℚ) := map_ratCast (RatFunc.C (K := ℚ)) a
  simp only [hC, Rat.cast_neg, Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat, Rat.cast_natCast]

def pulledPolynomial (k : ℕ) (p : ℚ[X]) : ℚ[X] := X^(2*k+1) * p.comp (-X^2)

theorem pulledPolynomial_monomial (k e : ℕ) (c : ℚ) :
    pulledPolynomial k (monomial e c) = monomial (2*e+2*k+1) (c * (-1:ℚ)^e) := by
  unfold pulledPolynomial
  rw [monomial_comp, ← C_mul_X_pow_eq_monomial, neg_pow]
  simp only [map_mul, map_pow, map_neg, map_one, ← pow_mul]
  rw [show 2*e+2*k+1 = (2*k+1)+2*e by omega, pow_add]
  ring

theorem tau_pulledPolynomial (k : ℕ) (hk : 1 ≤ k) (p : ℚ[X]) :
    tauPolynomial k (pulledPolynomial k p) =
      ∑ e ∈ Finset.range (p.natDegree+1), C (p.coeff e * muMonomial k e) := by
  conv_lhs => rw [p.as_sum_range_C_mul_X_pow]
  simp only [pulledPolynomial, sum_comp, Finset.mul_sum, map_sum]
  apply Finset.sum_congr rfl
  intro e he
  change tauPolynomial k (pulledPolynomial k (C (p.coeff e) * X^e)) = _
  rw [C_mul_X_pow_eq_monomial, pulledPolynomial_monomial, tauPolynomial_monomial,
    mul_assoc, ← pullback_identity_monomial k e hk]

/-- A full finite partial-fraction pullback in the actual tau domain. -/
def pullbackForm (k : ℕ) (R : RatMomentElem) : TauSpace :=
  polynomial (pulledPolynomial k R.polyPart) +
    ∑ j ∈ Finset.Icc 1 R.maxPole, R.poleRes j • pulledPole k j

theorem tau_pullbackForm (k : ℕ) (hk : 1 ≤ k) (R : RatMomentElem) :
    tau k (pullbackForm k R) = muFunctionalPoly k R := by
  rw [pullbackForm, map_add, tau_polynomial, tau_pulledPolynomial k hk, map_sum]
  unfold muFunctionalPoly
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  rw [map_smul, tau_pulledPole k j hk (Finset.mem_Icc.mp hj).1,
    Polynomial.smul_eq_C_mul]

theorem pullbackForm_coe (k : ℕ) (R : RatMomentElem) :
    (pullbackForm k R : RatFunc ℚ) =
      (RatFunc.X : RatFunc ℚ)^(2*k+1) * substitution (muRatFunc R) := by
  simp only [pullbackForm, Submodule.coe_add, Submodule.coe_sum, Submodule.coe_smul,
    polynomial, pulledPolynomial, map_mul, map_pow, RatFunc.algebraMap_X,
    muRatFunc, realization, muForm, map_add, map_sum, map_div₀,
    substitution_polynomial, mul_add, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  simp only [Algebra.smul_def, pulledPole_coe, sub_comp, add_comp, pow_comp, X_comp, C_comp,
    map_sub, map_add, map_neg, map_pow, RatFunc.algebraMap_X, RatFunc.algebraMap_C,
    sub_neg_eq_add]
  have hC (a : ℚ) : RatFunc.C a = (a : RatFunc ℚ) := map_ratCast (RatFunc.C (K := ℚ)) a
  simp only [hC, scalar_cast, Rat.cast_natCast]
  ring

/-- The actual domain pullback chooses a presentation only to construct its
membership proof; the underlying rational function is canonical. -/
def weightedPullback (k : ℕ) (f : MuDomain) : TauSpace :=
  pullbackForm k (Classical.choose f.property)

theorem weightedPullback_coe (k : ℕ) (f : MuDomain) :
    (weightedPullback k f : RatFunc ℚ) =
      (RatFunc.X : RatFunc ℚ)^(2*k+1) * substitution (f : RatFunc ℚ) := by
  rw [weightedPullback, pullbackForm_coe, Classical.choose_spec f.property]

/-- Manuscript Lemma 2.2 on its complete rational-function domain. -/
theorem rational_functional_pullback (k : ℕ) (hk : 1 ≤ k) (f : MuDomain) :
    muOnDomain k f = tau k (weightedPullback k f) := by
  exact (tau_pullbackForm k hk (Classical.choose f.property)).symm

end LeanPaper.Section2RatFuncPullback
