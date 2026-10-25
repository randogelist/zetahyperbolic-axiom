import LeanPaper.Section2PoleLinearSpace
import LeanPaper.Section2FunctionalBasis
import Zetahyperbolic.ManuscriptCompatibility
import LeanPaper.Rebuild.PartialFractionsResidues
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# The actual rational-functional Lagrange pencil (Theorem 2.5)

The moment functional is constructed on the simple negative-square-pole
subspace and extended linearly to the field only to simplify its application.
All expressions used below belong to the prescribed simple-pole subspace, so
no value on its chosen complementary subspace is used. The auxiliary value
assigned to the zero pole is likewise never used by a manuscript kernel.
-/

noncomputable section
open scoped BigOperators
open Polynomial
namespace LeanPaper.Section2LagrangeFunctional
open ManuscriptChain Section2RepresentationIndependence Section2PoleLinearSpace
open Section2LagrangeBridge PoleDiagonalization

def polynomialMomentLinear (k : ℕ) : ℚ[X] →ₗ[ℚ] ℚ[X] where
  toFun P := P.sum fun e c => C (c * Real.monomialMoment k e)
  map_add' P Q := Polynomial.sum_add_index P Q _ (by intro e; simp)
    (by intro e a b; simp [add_mul])
  map_smul' c P := by
    rw [Polynomial.sum_smul_index _ _ _ (by intro e; simp), Polynomial.smul_sum]
    simp only [Polynomial.sum_def]
    apply Finset.sum_congr rfl
    intro e he
    simp [Polynomial.smul_eq_C_mul, mul_assoc]

theorem polynomialMomentLinear_eq (k : ℕ) (P : ℚ[X]) :
    polynomialMomentLinear k P = C (Real.polynomialMoment k P) := by
  simp [polynomialMomentLinear, Polynomial.sum_def, Real.polynomialMoment]

def poleMoment (k a : ℕ) : ℚ[X] :=
  C (Real.poleConstant k a) + C ((a : ℚ) ^ (2 * k)) * X

def muSubspace (k : ℕ) :
    poleSubmodule (fun a : ℕ => -((a : ℚ) ^ 2)) →ₗ[ℚ] ℚ[X] :=
  liftMoment _ Section2LagrangeIdentification.negative_square_injective
    (polynomialMomentLinear k) (poleMoment k)

/-- A linear extension; every later evaluation is independently identified
with its canonical simple-pole expansion. -/
def mu (k : ℕ) : RatFunc ℚ →ₗ[ℚ] ℚ[X] :=
  (muSubspace k).comp
    (poleSubmodule (fun a : ℕ => -((a : ℚ) ^ 2))).subtype.leftInverse

theorem mu_realization (k : ℕ) (F : SimplePoleForm ℕ) :
    mu k (realization (fun a : ℕ => -((a : ℚ) ^ 2)) F) =
      C (Real.polynomialMoment k F.polynomial) +
        ∑ a ∈ F.support, C (F.residue a) * poleMoment k a := by
  let S := poleSubmodule (fun a : ℕ => -((a : ℚ) ^ 2))
  let x : S := ⟨realization (fun a : ℕ => -((a : ℚ) ^ 2)) F, ⟨F, rfl⟩⟩
  change muSubspace k (S.subtype.leftInverse (S.subtype x)) = _
  rw [LinearMap.leftInverse_apply_of_inj S.ker_subtype]
  change liftMoment _ _ _ _ x = _
  rw [liftMoment_eq]
  simp only [moment, polynomialMomentLinear_eq]

/-- On the manuscript domain this constructed linear map agrees exactly with
its original finite normal-form definition. -/
theorem mu_eq_existing (k : ℕ) (R : Zetahyperbolic.RatMomentElem) :
    mu k (muRatFunc R) = Zetahyperbolic.muFunctionalPoly k R := by
  rw [muRatFunc, mu_realization]
  unfold Zetahyperbolic.muFunctionalPoly
  rw [Zetahyperbolic.ManuscriptCompatibility.polynomialMoment_sum]
  simp only [muForm, poleMoment,
    Zetahyperbolic.ManuscriptCompatibility.muPolePoly_eq_affine]

theorem mu_polynomial (k : ℕ) (P : ℚ[X]) :
    mu k (algebraMap ℚ[X] (RatFunc ℚ) P) = C (Real.polynomialMoment k P) := by
  have h := mu_realization k (⟨P, ∅, fun _ => 0⟩ : SimplePoleForm ℕ)
  simpa [realization] using h

theorem mu_monomial (k e : ℕ) :
    mu k (algebraMap ℚ[X] (RatFunc ℚ) (X ^ e)) = C (Real.monomialMoment k e) := by
  rw [mu_polynomial]
  simp [Real.polynomialMoment]

theorem mu_simple_pole (k a : ℕ) :
    mu k ((1 : RatFunc ℚ) / algebraMap ℚ[X] (RatFunc ℚ) (X + C ((a : ℚ) ^ 2))) =
      poleMoment k a := by
  have h := mu_realization k (⟨0, {a}, fun _ => 1⟩ : SimplePoleForm ℕ)
  simpa [realization, Real.polynomialMoment] using h

def kernelForm (p : Real.Parameters) (i j : ℕ) : SimplePoleForm ℕ :=
  ⟨Real.quotient p i j, Finset.Icc (p.N + 1) p.K, Real.residue p i j⟩

theorem kernelForm_realization (p : Real.Parameters) (i j : ℕ) :
    realization (fun a : ℕ => -((a : ℚ) ^ 2)) (kernelForm p i j) =
      algebraMap ℚ[X] (RatFunc ℚ) (Real.numerator p i j) /
        algebraMap ℚ[X] (RatFunc ℚ) (Real.tailD p) := by
  let φ := algebraMap ℚ[X] (RatFunc ℚ)
  have hT : φ (Real.tailD p) ≠ 0 := RatFunc.algebraMap_ne_zero
    (monic_prod_of_monic _ _ (fun a _ => monic_X_add_C _)).ne_zero
  apply (eq_div_iff hT).mpr
  rw [PartialFractions.rational_kernel_decomposition]
  simp only [map_add, map_mul, map_sum, realization, kernelForm,
    Polynomial.C_neg, sub_neg_eq_add, add_mul, Finset.sum_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro a ha
  have hfactor : Real.tailD p = (X + C ((a : ℚ) ^ 2)) *
      ∏ b ∈ (Finset.Icc (p.N + 1) p.K).erase a, (X + C ((b : ℚ) ^ 2)) :=
    (Finset.mul_prod_erase _ _ ha).symm
  rw [hfactor, map_mul]
  have hd : φ (X + C ((a : ℚ) ^ 2)) ≠ 0 :=
    RatFunc.algebraMap_ne_zero (monic_X_add_C _).ne_zero
  change (φ (C (Real.residue p i j a)) / φ (X + C ((a : ℚ) ^ 2))) *
      (φ (X + C ((a : ℚ) ^ 2)) * _) = _
  field_simp <;> ring

/-- The residue-defined manuscript matrix is exactly the rational-function
moment matrix, including the polynomial quotient. -/
theorem mu_kernel_eq_pencil (p : Real.Parameters) (i j : Fin p.h) :
    mu p.k (algebraMap ℚ[X] (RatFunc ℚ) (Real.numerator p i.val j.val) /
      algebraMap ℚ[X] (RatFunc ℚ) (Real.tailD p)) = Real.pencil p i j := by
  rw [← kernelForm_realization, mu_realization]
  simp only [kernelForm, Real.pencil, Real.entryA, Real.entryM, poleMoment,
    map_add, map_sum, map_mul, mul_add, Finset.sum_add_distrib, Finset.sum_mul, mul_assoc]
  ring

theorem polePolynomial_expansion (p : Real.Parameters) (a : Fin p.h) :
    polePolynomial p a = ∑ i : Fin p.h,
      (polePolynomial p a).coeff i.val • (X : ℚ[X]) ^ i.val := by
  have hpos : 0 < p.h := Nat.zero_lt_of_lt a.isLt
  rw [Polynomial.as_sum_range_C_mul_X_pow, polePolynomial_natDegree,
    Nat.sub_add_cancel hpos]
  simpa [Polynomial.smul_eq_C_mul] using
    (Fin.sum_univ_eq_sum_range
      (fun i => C ((polePolynomial p a).coeff i) * X ^ i) p.h).symm

def numeratorMoment (p : Real.Parameters) : ℚ[X] →ₗ[ℚ] ℚ[X] where
  toFun Q := mu p.k
    (algebraMap ℚ[X] (RatFunc ℚ) (Real.D p.N ^ (2 * p.m - 1) * Q) /
      algebraMap ℚ[X] (RatFunc ℚ) (Real.tailD p))
  map_add' := by intros; simp [mul_add, map_add, add_div]
  map_smul' := by
    intro c P
    rw [← (mu p.k).map_smul]
    congr 1
    have hc : RatFunc.C c = algebraMap ℚ (RatFunc ℚ) c :=
      (map_ratCast RatFunc.C c).trans (map_ratCast (algebraMap ℚ (RatFunc ℚ)) c).symm
    simp only [Polynomial.smul_eq_C_mul, map_mul, RatFunc.algebraMap_C, Algebra.smul_def]
    rw [hc]
    ring

theorem numeratorMoment_monomial (p : Real.Parameters) (i j : Fin p.h) :
    numeratorMoment p (X ^ i.val * X ^ j.val) = Real.pencil p i j := by
  rw [← pow_add]
  exact mu_kernel_eq_pencil p i j

/-- Exact identification of the rational functional on the Lagrange numerator,
with the reduced tail denominator. -/
theorem lagrange_functional_eq (p : Real.Parameters) (a b : Fin p.h) :
    mu p.k
      (algebraMap ℚ[X] (RatFunc ℚ)
          (Real.D p.N ^ (2 * p.m - 1) * polePolynomial p a * polePolynomial p b) /
        algebraMap ℚ[X] (RatFunc ℚ) (Real.tailD p)) =
      poleDiagonalPencil p a b := by
  rw [mul_assoc (Real.D p.N ^ (2 * p.m - 1))]
  change numeratorMoment p (polePolynomial p a * polePolynomial p b) = _
  rw [polePolynomial_expansion p a, polePolynomial_expansion p b,
    Finset.sum_mul]
  simp only [Finset.mul_sum, smul_mul_assoc, mul_smul_comm, smul_smul,
    map_sum, map_smul, numeratorMoment_monomial, Polynomial.smul_eq_C_mul]
  exact (actual_lagrange_entries p a b).symm

theorem D_eq_Icc (n : ℕ) :
    Real.D n = ∏ a ∈ Finset.Icc 1 n, (X + C ((a : ℚ) ^ 2)) := by
  unfold Real.D
  rw [show Finset.Icc 1 n = Finset.Ico 1 (n + 1) by ext; simp; omega,
    Finset.prod_Ico_eq_prod_range]
  simp [Nat.add_comm]

theorem D_factorization (p : Real.Parameters) (hNK : p.N ≤ p.K) :
    Real.D p.K = Real.D p.N * Real.tailD p := by
  rw [D_eq_Icc, D_eq_Icc]
  have hset : Finset.Icc 1 p.K =
      Finset.Icc 1 p.N ∪ Finset.Icc (p.N + 1) p.K := by
    ext a
    simp only [Finset.mem_Icc, Finset.mem_union]
    omega
  have hdisj : Disjoint (Finset.Icc 1 p.N)
      (Finset.Icc (p.N + 1) p.K) := by
    apply Finset.disjoint_left.mpr
    intro a ha hb
    simp only [Finset.mem_Icc] at ha hb
    omega
  rw [hset, Finset.prod_union hdisj]
  rfl

theorem full_kernel_eq_reduced (p : Real.Parameters) (hm : 0 < p.m)
    (hNK : p.N ≤ p.K) (A B : ℚ[X]) :
    algebraMap ℚ[X] (RatFunc ℚ) (Real.D p.N ^ (2 * p.m) * A * B) /
      algebraMap ℚ[X] (RatFunc ℚ) (Real.D p.K) =
    algebraMap ℚ[X] (RatFunc ℚ) (Real.D p.N ^ (2 * p.m - 1) * A * B) /
      algebraMap ℚ[X] (RatFunc ℚ) (Real.tailD p) := by
  rw [D_factorization p hNK]
  have hD : algebraMap ℚ[X] (RatFunc ℚ) (Real.D p.N) ≠ 0 :=
    RatFunc.algebraMap_ne_zero
      (monic_prod_of_monic _ _ (fun a _ => monic_X_add_C _)).ne_zero
  have hT : algebraMap ℚ[X] (RatFunc ℚ) (Real.tailD p) ≠ 0 :=
    RatFunc.algebraMap_ne_zero
      (monic_prod_of_monic _ _ (fun a _ => monic_X_add_C _)).ne_zero
  have hpow : 2 * p.m = (2 * p.m - 1) + 1 := by omega
  simp only [map_mul, map_pow]
  rw [hpow, pow_succ]
  field_simp <;> ring

/-- The literal Theorem 2.5 matrix identity, with the original full denominator
and the actual moment functional. The nonzero diagonal slopes and the precise
harmonic constants are supplied together. -/
theorem theorem_2_5 (p : Real.Parameters) (hm : 0 < p.m)
    (hNK : p.N ≤ p.K) :
    (∀ a b : Fin p.h,
      mu p.k
        (algebraMap ℚ[X] (RatFunc ℚ)
            (Real.D p.N ^ (2 * p.m) * polePolynomial p a * polePolynomial p b) /
          algebraMap ℚ[X] (RatFunc ℚ) (Real.D p.K)) = poleDiagonalPencil p a b) ∧
    (∀ a b : Fin p.h, a ≠ b →
      poleDiagonalPencil p a b = C (poleConstantMatrix p a b)) ∧
    (∀ a : Fin p.h,
      poleDiagonalPencil p a a =
        C (poleWeight p a) * (X - C (Real.harmonic p.weight (poleIndex p a))) +
          C (poleDiagonalRemainder p a) ∧ poleWeight p a ≠ 0) ∧
    rationalDerivativeMatrix p =
      poleVandermonde p * Matrix.diagonal (poleWeight p) *
        (poleVandermonde p).transpose := by
  refine ⟨?_, poleDiagonalPencil_off_diagonal p,
    fun a => ⟨poleDiagonalPencil_diagonal_harmonic p a, poleWeight_ne_zero p a⟩,
    rationalDerivativeMatrix_factorization p⟩
  intro a b
  rw [full_kernel_eq_reduced p hm hNK]
  exact lagrange_functional_eq p a b

end LeanPaper.Section2LagrangeFunctional
