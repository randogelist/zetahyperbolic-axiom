import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Tactic

/-!
# Proposition 4.3: a genuine ultrametric zero-free disk

Over any nontrivially normed ultrametric field, if all nonconstant
terms at a point are strictly dominated in norm by the constant
coefficient, evaluation has EXACTLY the constant coefficient's norm.

For Z_p-polynomials, translation by an integral center remains a
Z_p-polynomial. All its coefficients have norm <= 1. This proves
pointwise norm preservation and zero-exclusion on the Q_p disk
with radius |Q(center)|_p. The integer-polynomial case follows by
mapping Z[X] into Z_p[X].

Scope limitation: The printed paper states alpha in C_p; the current
formal theorem is for alpha in Q_p. Complex p-adic extension and any
unproved p-adic irrationality statement are NOT asserted here.
-/

noncomputable section
open scoped BigOperators
open Polynomial

namespace PaperAdvances.Proposition4_3_PadicDisk

/-- Finite ultrametric sums of individually strictly dominated terms
are strictly dominated as well, including the empty sum. -/
theorem finite_ultrametric_sum_strict
    {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → K) (B : ℝ)
    (hB : 0 < B) (hf : ∀ i ∈ s, ‖f i‖ < B) :
    ‖∑ i ∈ s, f i‖ < B := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hB
  | @insert i t hit ih =>
      have hi : ‖f i‖ < B := hf i (Finset.mem_insert_self i t)
      have ht : ∀ j ∈ t, ‖f j‖ < B := by
        intro j hj
        exact hf j (Finset.mem_insert_of_mem hj)
      rw [Finset.sum_insert hit]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt
        (max_lt hi (ih ht))

/-- Sharp dominant-constant Gauss bound for a finite polynomial.
No unproved root or spectral hypothesis. -/
theorem ultrametric_eval_norm_eq_constant
    {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
    (P : K[X]) (x : K) (h0 : P.coeff 0 ≠ 0)
    (hterms : ∀ k : ℕ, 0 < k →
      ‖P.coeff k * x ^ k‖ < ‖P.coeff 0‖) :
    ‖P.eval x‖ = ‖P.coeff 0‖ := by
  classical
  let t : K := ∑ j ∈ Finset.range P.natDegree,
    P.coeff (j + 1) * x ^ (j + 1)
  have htail : ‖t‖ < ‖P.coeff 0‖ := by
    apply finite_ultrametric_sum_strict _ _ _ (norm_pos_iff.mpr h0)
    intro j hj
    exact hterms (j + 1) (Nat.succ_pos j)
  have heval : P.eval x = P.coeff 0 + t := by
    rw [Polynomial.eval_eq_sum_range, Finset.sum_range_succ']
    simp [t, add_comm]
  rw [heval]
  have hnorms : ‖P.coeff 0‖ ≠ ‖t‖ := ne_of_gt htail
  rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hnorms]
  exact max_eq_left htail.le

/-- A unit-ball polynomial cannot lose its nonzero constant norm
inside the open disk with radius that norm. -/
theorem ultrametric_unit_coeff_disk
    {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
    (P : K[X]) (x : K)
    (h0 : P.coeff 0 ≠ 0)
    (hcoeff : ∀ k : ℕ, 0 < k → ‖P.coeff k‖ ≤ 1)
    (hcenter : ‖P.coeff 0‖ ≤ 1)
    (hx : ‖x‖ < ‖P.coeff 0‖) :
    ‖P.eval x‖ = ‖P.coeff 0‖ ∧ P.eval x ≠ 0 := by
  have hn : ‖P.eval x‖ = ‖P.coeff 0‖ := by
    apply ultrametric_eval_norm_eq_constant P x h0
    intro k hk
    calc
      ‖P.coeff k * x ^ k‖ = ‖P.coeff k‖ * ‖x‖ ^ k := by
        rw [norm_mul, norm_pow]
      _ ≤ ‖x‖ ^ k := by
        simpa only [one_mul] using
          (mul_le_mul_of_nonneg_right (hcoeff k hk)
            (pow_nonneg (norm_nonneg x) k))
      _ ≤ ‖x‖ :=
        pow_le_of_le_one (norm_nonneg x) (hx.le.trans hcenter)
          (Nat.ne_of_gt hk)
      _ < ‖P.coeff 0‖ := hx
  refine ⟨hn, ?_⟩
  intro hz
  have hz0 : ‖P.coeff 0‖ = 0 := by rw [← hn, hz, norm_zero]
  exact h0 (norm_eq_zero.mp hz0)

/-- Exact Proposition 4.3 norm preservation for an integral polynomial,
with arbitrary Z_p center and arbitrary Q_p evaluation point.
The center need not be a rational integer. -/
theorem PROPOSITION_4_3_INTEGRAL_QPADIC
    {p : ℕ} [Fact p.Prime]
    (Q : (ℤ_[p])[X]) (ξ : ℤ_[p]) (α : ℚ_[p])
    (hQ : Q.eval ξ ≠ 0)
    (hα : ‖α - (ξ : ℚ_[p])‖ < ‖((Q.eval ξ : ℤ_[p]) : ℚ_[p])‖) :
    ‖(Q.map (PadicInt.Coe.ringHom)).eval α‖ =
        ‖((Q.eval ξ : ℤ_[p]) : ℚ_[p])‖ ∧
    (Q.map (PadicInt.Coe.ringHom)).eval α ≠ 0 := by
  let S : (ℤ_[p])[X] := Q.comp (Polynomial.X + Polynomial.C ξ)
  let T : (ℚ_[p])[X] := S.map (PadicInt.Coe.ringHom)
  have hS0 : S.coeff 0 = Q.eval ξ := by
    simp [S, Polynomial.coeff_zero_eq_eval_zero]
  have hT0 : T.coeff 0 = ((Q.eval ξ : ℤ_[p]) : ℚ_[p]) := by
    calc
      T.coeff 0 = (PadicInt.Coe.ringHom) (S.coeff 0) := by
        simp only [T, Polynomial.coeff_map]
      _ = (PadicInt.Coe.ringHom) (Q.eval ξ) := by rw [hS0]
      _ = ((Q.eval ξ : ℤ_[p]) : ℚ_[p]) := rfl
  have hcoeff (k : ℕ) : ‖T.coeff k‖ ≤ 1 := by
    have hmap : T.coeff k = (PadicInt.Coe.ringHom) (S.coeff k) := by
      simp only [T, Polynomial.coeff_map]
    rw [hmap]
    change ‖((S.coeff k : ℤ_[p]) : ℚ_[p])‖ ≤ 1
    exact (S.coeff k).property
  have hT0ne : T.coeff 0 ≠ 0 := by
    rw [hT0]
    exact PadicInt.coe_ne_zero.mpr hQ
  have hT0le : ‖T.coeff 0‖ ≤ 1 := by
    rw [hT0]
    exact (Q.eval ξ).property
  have hball : ‖α - (ξ : ℚ_[p])‖ < ‖T.coeff 0‖ := by
    simpa only [hT0] using hα
  have hraw := ultrametric_unit_coeff_disk T
    (α - (ξ : ℚ_[p])) hT0ne (fun k _ => hcoeff k) hT0le hball
  have heval : T.eval (α - (ξ : ℚ_[p])) =
      (Q.map (PadicInt.Coe.ringHom)).eval α := by
    change ((Q.comp (Polynomial.X + Polynomial.C ξ)).map
      (PadicInt.Coe.ringHom)).eval (α - (ξ : ℚ_[p])) =
      (Q.map (PadicInt.Coe.ringHom)).eval α
    have hξ : (PadicInt.Coe.ringHom) ξ = (ξ : ℚ_[p]) := rfl
    rw [Polynomial.map_comp, Polynomial.eval_comp]
    simp only [Polynomial.map_add, Polynomial.map_X, Polynomial.map_C,
      Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C, hξ,
      sub_add_cancel]
  constructor
  · simpa only [heval, hT0] using hraw.1
  · simpa only [heval] using hraw.2

/-- The source manuscript's integer-polynomial case, now proved for Q_p.
The stronger C_p extension is a separate proof frontier. -/
theorem PROPOSITION_4_3_INTEGER_QPADIC
    {p : ℕ} [Fact p.Prime]
    (Q : ℤ[X]) (ξ : ℤ_[p]) (α : ℚ_[p])
    (hQ : (Q.map (Int.castRingHom (ℤ_[p]))).eval ξ ≠ 0)
    (hα : ‖α - (ξ : ℚ_[p])‖ <
        ‖(((Q.map (Int.castRingHom (ℤ_[p]))).eval ξ : ℤ_[p]) : ℚ_[p])‖) :
    ‖((Q.map (Int.castRingHom (ℤ_[p]))).map
      (PadicInt.Coe.ringHom)).eval α‖ =
      ‖(((Q.map (Int.castRingHom (ℤ_[p]))).eval ξ : ℤ_[p]) : ℚ_[p])‖ ∧
    ((Q.map (Int.castRingHom (ℤ_[p]))).map
      (PadicInt.Coe.ringHom)).eval α ≠ 0 := by
  exact PROPOSITION_4_3_INTEGRAL_QPADIC
    (Q.map (Int.castRingHom (ℤ_[p]))) ξ α hQ hα

end PaperAdvances.Proposition4_3_PadicDisk

#print axioms PaperAdvances.Proposition4_3_PadicDisk.finite_ultrametric_sum_strict
#print axioms PaperAdvances.Proposition4_3_PadicDisk.ultrametric_eval_norm_eq_constant
#print axioms PaperAdvances.Proposition4_3_PadicDisk.ultrametric_unit_coeff_disk
#print axioms PaperAdvances.Proposition4_3_PadicDisk.PROPOSITION_4_3_INTEGRAL_QPADIC
#print axioms PaperAdvances.Proposition4_3_PadicDisk.PROPOSITION_4_3_INTEGER_QPADIC
