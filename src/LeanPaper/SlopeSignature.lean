import LeanPaper.SlopeIndefinite
import Mathlib.LinearAlgebra.QuadraticForm.Signature
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-! Sylvester inertia counts of the actual slope and normalized pencil.
Signature means the intrinsic maximal dimensions of positive and negative
quadratic subspaces, as defined in Mathlib; this is not a supplied count. -/
noncomputable section
open scoped BigOperators MatrixOrder
open Matrix QuadraticMap
namespace LeanPaper.SlopeSignature
set_option backward.isDefEq.respectTransparency false
open ManuscriptChain
open PaperAdvances.Proposition3_2

lemma congruence_form {n : Type*} [Fintype n] [DecidableEq n]
    (A P : Matrix n n ℝ) :
    (Pᵀ*A*P).toQuadraticForm' = A.toQuadraticForm'.comp (Matrix.toLin' P) := by
  ext x
  simp only [Matrix.toQuadraticForm', LinearMap.BilinMap.toQuadraticMap_apply,
    Matrix.toLinearMap₂'_apply', QuadraticMap.comp_apply, Matrix.toLin'_apply]
  simp only [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]

lemma sigPos_congruence {n : Type*} [Fintype n] [DecidableEq n]
    (A P : Matrix n n ℝ) (hP : P.det ≠ 0) :
    sigPos (Pᵀ*A*P).toQuadraticForm' = sigPos A.toQuadraticForm' := by
  letI : Invertible P.det := invertibleOfNonzero hP
  letI : Invertible P := Matrix.invertibleOfDetInvertible P
  let e := Matrix.toLinearEquiv' P (inferInstance : Invertible P)
  have h : A.toQuadraticForm'.Equivalent
      (A.toQuadraticForm'.comp (Matrix.toLin' P)) :=
    ⟨QuadraticMap.isometryEquivOfCompLinearEquiv A.toQuadraticForm' e⟩
  rw [congruence_form]
  exact h.sigPos_eq.symm

lemma sigNeg_congruence {n : Type*} [Fintype n] [DecidableEq n]
    (A P : Matrix n n ℝ) (hP : P.det ≠ 0) :
    sigNeg (Pᵀ*A*P).toQuadraticForm' = sigNeg A.toQuadraticForm' := by
  letI : Invertible P.det := invertibleOfNonzero hP
  letI : Invertible P := Matrix.invertibleOfDetInvertible P
  let e := Matrix.toLinearEquiv' P (inferInstance : Invertible P)
  have h : A.toQuadraticForm'.Equivalent
      (A.toQuadraticForm'.comp (Matrix.toLin' P)) :=
    ⟨QuadraticMap.isometryEquivOfCompLinearEquiv A.toQuadraticForm' e⟩
  rw [congruence_form]
  exact h.sigNeg_eq.symm

lemma diagonal_form {n : Type*} [Fintype n] [DecidableEq n] (w : n → ℝ) :
    (Matrix.diagonal w).toQuadraticForm' = QuadraticMap.weightedSumSquares ℝ w := by
  ext x
  simp only [Matrix.toQuadraticForm', LinearMap.BilinMap.toQuadraticMap_apply,
    Matrix.toLinearMap₂'_apply', Matrix.mulVec_diagonal, dotProduct,
    QuadraticMap.weightedSumSquares_apply, smul_eq_mul, Pi.mul_apply]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Exact positive inertia, for every real exponent. -/
theorem slope_sigPos (p : Real.Parameters) (hm : 1 ≤ p.m) (s : ℝ) :
    sigPos (slope p s).toQuadraticForm' = {a : Fin p.h | Even (p.N+a.val)}.ncard := by
  have hV : (vandermonde p)ᵀ.det ≠ 0 := by
    rw [Matrix.det_transpose]
    exact vandermonde_det_ne_zero p
  have h := sigPos_congruence (Matrix.diagonal (gamma p s)) (vandermonde p)ᵀ hV
  rw [Matrix.transpose_transpose, diagonal_form,
    QuadraticForm.sigPos_weightedSumSquares] at h
  change sigPos (slope p s).toQuadraticForm' = _ at h
  rw [h]
  congr 1
  ext a
  exact PoleWeightSigns.gamma_pos_iff_even p hm s a

/-- Exact negative inertia, for every real exponent. -/
theorem slope_sigNeg (p : Real.Parameters) (hm : 1 ≤ p.m) (s : ℝ) :
    sigNeg (slope p s).toQuadraticForm' = {a : Fin p.h | Odd (p.N+a.val)}.ncard := by
  have hV : (vandermonde p)ᵀ.det ≠ 0 := by
    rw [Matrix.det_transpose]
    exact vandermonde_det_ne_zero p
  have h := sigNeg_congruence (Matrix.diagonal (gamma p s)) (vandermonde p)ᵀ hV
  rw [Matrix.transpose_transpose, diagonal_form,
    QuadraticForm.sigNeg_weightedSumSquares] at h
  change sigNeg (slope p s).toQuadraticForm' = _ at h
  rw [h]
  congr 1
  ext a
  exact PoleWeightSigns.gamma_neg_iff_odd p hm s a

lemma whitened_signature {n : ℕ} (p : Spectral.SymmetricAffinePencil n)
    (hp : p.base.PosDef) :
    sigPos (OperatorNormDisk.whitened p).toQuadraticForm' = sigPos p.direction.toQuadraticForm' ∧
    sigNeg (OperatorNormDisk.whitened p).toQuadraticForm' = sigNeg p.direction.toQuadraticForm' := by
  let S := CFC.sqrt p.base
  have hs : S*S = p.base := by
    simpa [S, _root_.sq] using CFC.sq_sqrt p.base hp.posSemidef.nonneg
  have hsym : S.IsHermitian := (CFC.sqrt_nonneg p.base).posSemidef.isHermitian
  have hdet : S.det ≠ 0 := by
    intro h
    have ht := congrArg Matrix.det hs
    rw [Matrix.det_mul, h, zero_mul] at ht
    exact (ne_of_gt hp.det_pos) ht.symm
  have hi : S⁻¹.det ≠ 0 :=
    (Matrix.isUnit_nonsing_inv_det S (isUnit_iff_ne_zero.mpr hdet)).ne_zero
  have hst : (S⁻¹)ᵀ = S⁻¹ := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hsym.inv.eq
  constructor
  · simpa only [hst, S, OperatorNormDisk.whitened] using sigPos_congruence p.direction S⁻¹ hi
  · simpa only [hst, S, OperatorNormDisk.whitened] using sigNeg_congruence p.direction S⁻¹ hi

/-- Exact signature of the actual B_K, with its analytic positivity discharged. -/
theorem actual_normalized_signature (p : Real.Parameters) (hp : Real.Admissible p) :
    sigPos (OperatorNormDisk.whitened (Real.manuscriptPencil p)).toQuadraticForm' =
      {a : Fin p.h | Even (p.N+a.val)}.ncard ∧
    sigNeg (OperatorNormDisk.whitened (Real.manuscriptPencil p)).toQuadraticForm' =
      {a : Fin p.h | Odd (p.N+a.val)}.ncard := by
  obtain ⟨hpos, hneg⟩ := whitened_signature (Real.manuscriptPencil p) (GRAM_POSITIVE p hp)
  change _ = sigPos (Real.derivativeMatrix p).toQuadraticForm' at hpos
  change _ = sigNeg (Real.derivativeMatrix p).toQuadraticForm' at hneg
  rw [← SlopeIndefinite.slope_odd_eq_derivative p, slope_sigPos p hp.m_pos] at hpos
  rw [← SlopeIndefinite.slope_odd_eq_derivative p, slope_sigNeg p hp.m_pos] at hneg
  exact ⟨hpos, hneg⟩

lemma even_sum_count (N h : ℕ) :
    (∑ a : Fin h, if Even (N+a.val) then 1 else 0 : ℕ) =
      if Even N then (h+1)/2 else h/2 := by
  induction h with
  | zero => simp
  | succ h ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [ih]
    split_ifs <;> simp_all only [Nat.even_add, Nat.even_iff] <;> omega

lemma even_index_count (N h : ℕ) :
    {a : Fin h | Even (N+a.val)}.ncard =
      if Even N then (h+1)/2 else h/2 := by
  rw [← Set.fintypeCard_eq_ncard, Fintype.card_subtype]
  simpa only [Finset.sum_boole, Nat.cast_id, Set.mem_setOf_eq] using even_sum_count N h

lemma odd_index_count (N h : ℕ) :
    {a : Fin h | Odd (N+a.val)}.ncard =
      if Even N then h/2 else (h+1)/2 := by
  have hc := Set.ncard_add_ncard_compl {a : Fin h | Even (N+a.val)}
  have heq : {a : Fin h | Even (N+a.val)}ᶜ = {a : Fin h | Odd (N+a.val)} := by
    ext a
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq, Nat.not_even_iff_odd]
  rw [heq, even_index_count] at hc
  simp only [Nat.card_fin] at hc
  split_ifs with he <;> simp only [he, ↓reduceIte] at hc <;> omega

/-- The explicit ceiling/floor signature claimed in Theorem 3.3(3). -/
theorem actual_normalized_signature_counts (p : Real.Parameters) (hp : Real.Admissible p) :
    sigPos (OperatorNormDisk.whitened (Real.manuscriptPencil p)).toQuadraticForm' =
      (if Even p.N then (p.h+1)/2 else p.h/2) ∧
    sigNeg (OperatorNormDisk.whitened (Real.manuscriptPencil p)).toQuadraticForm' =
      (if Even p.N then p.h/2 else (p.h+1)/2) := by
  simpa only [even_index_count, odd_index_count] using actual_normalized_signature p hp

end LeanPaper.SlopeSignature
#print axioms LeanPaper.SlopeSignature.actual_normalized_signature
