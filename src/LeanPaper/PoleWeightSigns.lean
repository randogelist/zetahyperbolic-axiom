import LeanPaper.ImportedSection3.RealExponent
import Mathlib.Data.Sign.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic

/-! Exact alternating signs of the actual residue-defined slope weights.
This fills the sign calculation used by manuscript Theorem 3.3(3), including
its dependence on the parity of N. It makes no total-positivity or asymptotic
claim. -/
noncomputable section
open scoped BigOperators
open Polynomial SignType
namespace LeanPaper.PoleWeightSigns
open ManuscriptChain PoleDiagonalization

lemma sign_D_eval (N a : ℕ) (ha : N < a) :
    sign ((Real.D N).eval (-(a : ℚ)^2)) = (-1 : SignType)^N := by
  simp only [Real.D, Polynomial.eval_prod, Polynomial.eval_add,
    Polynomial.eval_X, Polynomial.eval_C]
  change signHom (∏ j ∈ Finset.range N, (-(a : ℚ)^2 + (↑(j+1) : ℚ)^2)) = _
  rw [map_prod]
  have hf (j : ℕ) (hj : j ∈ Finset.range N) :
      signHom (-(a : ℚ)^2 + (↑(j+1) : ℚ)^2) = (-1 : SignType) := by
    apply sign_eq_neg_one_iff.mpr
    have hja : (j+1 : ℚ) < a := by exact_mod_cast (show j+1<a by have := Finset.mem_range.mp hj; omega)
    have hj0 : (0 : ℚ) ≤ j+1 := by positivity
    have ha0 : (0 : ℚ) < a := by exact_mod_cast (show 0<a by omega)
    norm_num only [Nat.cast_add, Nat.cast_one] at *
    nlinarith
  rw [Finset.prod_congr rfl hf]
  simp

lemma sign_tail_derivative (p : Real.Parameters) (a : Fin p.h) :
    sign ((derivative (Real.tailD p)).eval (poleNode p a)) =
      (-1 : SignType)^a.val := by
  rw [poleNode, tailD_derivative_eval p _ (poleIndex_mem p a)]
  let j := poleIndex p a
  have hj : p.N+1 ≤ j ∧ j ≤ p.K := Finset.mem_Icc.mp (poleIndex_mem p a)
  have hsplit : (Finset.Icc (p.N+1) p.K).erase j =
      Finset.Ico (p.N+1) j ∪ Finset.Ioc j p.K := by
    ext b
    simp only [Finset.mem_erase, Finset.mem_Icc, Finset.mem_union,
      Finset.mem_Ico, Finset.mem_Ioc]
    omega
  have hd : Disjoint (Finset.Ico (p.N+1) j) (Finset.Ioc j p.K) := by
    rw [Finset.disjoint_left]
    intro b hb hc
    have := Finset.mem_Ico.mp hb
    have := Finset.mem_Ioc.mp hc
    omega
  change signHom (∏ b ∈ (Finset.Icc (p.N+1) p.K).erase j,
    ((b : ℚ)^2 - (j : ℚ)^2)) = _
  rw [hsplit, Finset.prod_union hd, map_mul, map_prod, map_prod]
  have hl (b : ℕ) (hb : b ∈ Finset.Ico (p.N+1) j) :
      signHom ((b : ℚ)^2 - (j : ℚ)^2) = (-1 : SignType) := by
    apply sign_eq_neg_one_iff.mpr
    have hbj : (b : ℚ) < j := by exact_mod_cast (Finset.mem_Ico.mp hb).2
    have hb0 : (0 : ℚ) ≤ b := by positivity
    have hj0 : (0 : ℚ) ≤ j := by positivity
    nlinarith
  have hr (b : ℕ) (hb : b ∈ Finset.Ioc j p.K) :
      signHom ((b : ℚ)^2 - (j : ℚ)^2) = (1 : SignType) := by
    apply sign_eq_one_iff.mpr
    have hbj : (j : ℚ) < b := by exact_mod_cast (Finset.mem_Ioc.mp hb).1
    have hb0 : (0 : ℚ) ≤ b := by positivity
    have hj0 : (0 : ℚ) ≤ j := by positivity
    nlinarith
  rw [Finset.prod_congr rfl hl, Finset.prod_congr rfl hr]
  simp [j, poleIndex]

/-- The sign is `(-1)^(N+a)` for the zero-based pole index a. -/
theorem poleWeight_sign (p : Real.Parameters) (hm : 1 ≤ p.m) (a : Fin p.h) :
    sign (poleWeight p a) = (-1 : SignType)^(p.N+a.val) := by
  have hodd : Odd (2*p.m-1) := ⟨p.m-1, by omega⟩
  have hD := sign_D_eval p.N (poleIndex p a) (by simp [poleIndex]; omega)
  have hj : sign (poleIndex p a : ℚ) = (1 : SignType) :=
    sign_eq_one_iff.mpr (by exact_mod_cast poleIndex_pos p a)
  change signHom (((Real.D p.N).eval (poleNode p a))^(2*p.m-1) /
    (derivative (Real.tailD p)).eval (poleNode p a) * (poleIndex p a : ℚ)^(2*p.k)) = _
  rw [map_mul, map_div₀, map_pow, map_pow]
  change sign ((Real.D p.N).eval (poleNode p a)) ^ (2*p.m-1) /
    sign ((derivative (Real.tailD p)).eval (poleNode p a)) *
      sign (poleIndex p a : ℚ) ^ (2*p.k) = _
  rw [show sign ((Real.D p.N).eval (poleNode p a)) = (-1 : SignType)^p.N from hD,
    sign_tail_derivative, hj, one_pow, mul_one]
  rw [← pow_mul, Nat.mul_comm p.N, pow_mul, hodd.neg_one_pow]
  rw [pow_add]
  rfl

/-- Consecutive actual residues have opposite signs. -/
theorem adjacent_poleWeight_sign (p : Real.Parameters) (hm : 1 ≤ p.m)
    (a b : Fin p.h) (hab : b.val = a.val+1) :
    sign (poleWeight p b) = -sign (poleWeight p a) := by
  rw [poleWeight_sign p hm b, poleWeight_sign p hm a, hab,
    ← Nat.add_assoc, pow_succ]
  simp

theorem poleWeight_pos_iff (p : Real.Parameters) (hm : 1 ≤ p.m) (a : Fin p.h) :
    0 < poleWeight p a ↔ Even (p.N+a.val) := by
  rw [← sign_eq_one_iff, poleWeight_sign p hm a]
  exact neg_one_pow_eq_one_iff_even (by decide : (-1 : SignType) ≠ 1)

theorem poleWeight_neg_iff (p : Real.Parameters) (hm : 1 ≤ p.m) (a : Fin p.h) :
    poleWeight p a < 0 ↔ Odd (p.N+a.val) := by
  rw [← sign_eq_neg_one_iff, poleWeight_sign p hm a]
  exact neg_one_pow_eq_neg_one_iff_odd (by decide : (-1 : SignType) ≠ 1)

theorem gamma_pos_iff_even (p : Real.Parameters) (hm : 1 ≤ p.m) (s : ℝ) (a : Fin p.h) :
    0 < PaperAdvances.Proposition3_2.gamma p s a ↔ Even (p.N+a.val) := by
  rw [PaperAdvances.Proposition3_2.gamma_pos_iff]
  exact (Rat.cast_pos (K := ℝ)).trans (poleWeight_pos_iff p hm a)

theorem gamma_neg_iff_odd (p : Real.Parameters) (hm : 1 ≤ p.m) (s : ℝ) (a : Fin p.h) :
    PaperAdvances.Proposition3_2.gamma p s a < 0 ↔ Odd (p.N+a.val) := by
  rw [PaperAdvances.Proposition3_2.gamma_neg_iff]
  exact (Rat.cast_lt_zero (K := ℝ)).trans (poleWeight_neg_iff p hm a)

/-- Every actual slope of dimension at least two contains both signs. -/
theorem gamma_has_both_signs (p : Real.Parameters) (hm : 1 ≤ p.m) (s : ℝ)
    (hh : 2 ≤ p.h) :
    (∃ a, 0 < PaperAdvances.Proposition3_2.gamma p s a) ∧
      (∃ a, PaperAdvances.Proposition3_2.gamma p s a < 0) := by
  let a : Fin p.h := ⟨0, by omega⟩
  let b : Fin p.h := ⟨1, by omega⟩
  rcases Nat.even_or_odd p.N with he | ho
  · refine ⟨⟨a, (gamma_pos_iff_even p hm s a).mpr ?_⟩,
      ⟨b, (gamma_neg_iff_odd p hm s b).mpr ?_⟩⟩
    · simpa [a] using he
    · simpa [b] using he.add_odd odd_one
  · refine ⟨⟨b, (gamma_pos_iff_even p hm s b).mpr ?_⟩,
      ⟨a, (gamma_neg_iff_odd p hm s a).mpr ?_⟩⟩
    · simpa [b] using ho.add_odd odd_one
    · simpa [a] using ho

/-- Exact sign of the actual determinant's leading coefficient. -/
theorem determinant_leading_sign (p : Real.Parameters) (hm : 1 ≤ p.m) :
    sign (Real.delta p).leadingCoeff =
      (-1 : SignType)^(p.N*p.h + p.h*(p.h-1)/2) := by
  rw [delta_leadingCoeff, rationalDerivativeMatrix_det, sign_mul,
    sign_eq_one_iff.mpr (sq_pos_of_ne_zero (poleVandermonde_det_ne_zero p)), one_mul]
  change signHom (∏ a : Fin p.h, poleWeight p a) = _
  rw [map_prod]
  have ht : (∏ a : Fin p.h, signHom (poleWeight p a)) =
      ∏ a : Fin p.h, (-1 : SignType)^(p.N+a.val) := by
    apply Finset.prod_congr rfl
    intro a _
    exact poleWeight_sign p hm a
  rw [ht, Finset.prod_pow_eq_pow_sum]
  congr 1
  rw [Finset.sum_add_distrib]
  have hi : (∑ a : Fin p.h, a.val) = p.h*(p.h-1)/2 := by
    simpa only [Finset.sum_range_id] using (Fin.sum_univ_eq_sum_range (fun i : ℕ => i) p.h)
  simp [hi, Nat.mul_comm]

end LeanPaper.PoleWeightSigns
#print axioms LeanPaper.PoleWeightSigns.poleWeight_sign
