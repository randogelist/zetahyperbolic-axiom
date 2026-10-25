import LeanPaper.PoleWeightSigns
import LeanPaper.OperatorNormDisk
import LeanPaper.ImportedSection3.ActualPoleKernel
import Mathlib.Analysis.Matrix.PosDef

/-! Mixed signs for the actual manuscript slope and its spectral factors.
This establishes the nonconstant-spectrum input needed for strict Laguerre
bounds, without claiming that all eigenvalues are pairwise distinct. -/
noncomputable section
open scoped BigOperators MatrixOrder
open Matrix Polynomial
namespace LeanPaper.SlopeIndefinite
open ManuscriptChain ManuscriptChain.Spectral
open PaperAdvances.Proposition3_2

lemma slope_posSemidef_iff (p : Real.Parameters) (s : ℝ) :
    (slope p s).PosSemidef ↔ ∀ a, 0 ≤ gamma p s a := by
  have hV : IsUnit (vandermonde p) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr (vandermonde_det_ne_zero p))
  have h := hV.posSemidef_star_right_conjugate_iff (x := Matrix.diagonal (gamma p s))
  simpa [slope, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial,
    Matrix.posSemidef_diagonal_iff] using h

lemma neg_slope_posSemidef_iff (p : Real.Parameters) (s : ℝ) :
    (-(slope p s)).PosSemidef ↔ ∀ a, gamma p s a ≤ 0 := by
  have hV : IsUnit (vandermonde p) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr (vandermonde_det_ne_zero p))
  have h := hV.posSemidef_star_right_conjugate_iff (x := Matrix.diagonal (-(gamma p s)))
  simpa [slope, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial,
    Matrix.posSemidef_diagonal_iff, Matrix.diagonal_neg, Matrix.mul_neg, Matrix.neg_mul] using h

theorem slope_indefinite (p : Real.Parameters) (hm : 1 ≤ p.m) (s : ℝ) (hh : 2 ≤ p.h) :
    ¬ (slope p s).PosSemidef ∧ ¬ (-(slope p s)).PosSemidef := by
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := PoleWeightSigns.gamma_has_both_signs p hm s hh
  exact ⟨fun h => (not_le_of_gt hb) ((slope_posSemidef_iff p s).mp h b),
    fun h => (not_le_of_gt ha) ((neg_slope_posSemidef_iff p s).mp h a)⟩

lemma slope_odd_eq_derivative (p : Real.Parameters) :
    slope p (p.weight : ℝ) = Real.derivativeMatrix p := by
  exact PaperAdvances.Theorem3_8_Actual.actual_derivative_eq_real_slope p |>.symm

/-- The actual odd-weight slope is indefinite in every dimension h ≥ 2. -/
theorem derivative_indefinite (p : Real.Parameters) (hm : 1 ≤ p.m) (hh : 2 ≤ p.h) :
    ¬ (Real.derivativeMatrix p).PosSemidef ∧
      ¬ (-(Real.derivativeMatrix p)).PosSemidef := by
  rw [← slope_odd_eq_derivative]
  exact slope_indefinite p hm _ hh

lemma hermitian_mixed_eigenvalues {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ)
    (hB : B.IsHermitian) (hp : ¬ B.PosSemidef) (hn : ¬ (-B).PosSemidef) :
    (∃ i, hB.eigenvalues i < 0) ∧ (∃ j, 0 < hB.eigenvalues j) := by
  constructor
  · by_contra h
    push_neg at h
    exact hp (hB.posSemidef_iff_eigenvalues_nonneg.mpr h)
  · by_contra h
    push_neg at h
    apply hn
    have hd : (Matrix.diagonal (-hB.eigenvalues)).PosSemidef :=
      Matrix.posSemidef_diagonal_iff.mpr (fun i => neg_nonneg.mpr (h i))
    have hc := hd.mul_mul_conjTranspose_same (hB.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ)
    rw [hB.spectral_theorem]
    simpa [Unitary.conjStarAlgAut_apply, Matrix.diagonal_neg,
      Matrix.mul_neg, Matrix.neg_mul, Function.comp_def] using hc

theorem mixed_factorization_exists {n : ℕ}
    (p : SymmetricAffinePencil n) (positive : p.base.PosDef)
    (direction_nonzero : Matrix.det p.direction ≠ 0)
    (hp : ¬ p.direction.PosSemidef) (hn : ¬ (-p.direction).PosSemidef) :
    ∃ c : RootFactorization p, (∃ i, c.beta i < 0) ∧ (∃ j, 0 < c.beta j) := by
  let S := CFC.sqrt p.base
  have hSsq : S * S = p.base := by
    simpa [S, sq] using CFC.sq_sqrt p.base positive.posSemidef.nonneg
  have hSsymm : S.IsHermitian :=
    (CFC.sqrt_nonneg p.base).posSemidef.isHermitian
  have hbase : Matrix.det p.base ≠ 0 := ne_of_gt positive.det_pos
  have hSdet : Matrix.det S ≠ 0 := by
    have h := congrArg Matrix.det hSsq
    rw [Matrix.det_mul] at h
    intro hz
    simp [hz] at h
    exact hbase h.symm
  have hSunit : IsUnit (Matrix.det S) := isUnit_iff_ne_zero.mpr hSdet
  have hSinvdet : Matrix.det (S⁻¹) ≠ 0 :=
    (Matrix.isUnit_nonsing_inv_det S hSunit).ne_zero
  let B := S⁻¹ * p.direction * S⁻¹
  have hBsymm : B.IsHermitian := by
    have h := Matrix.isHermitian_conjTranspose_mul_mul (S⁻¹)
      (Matrix.isHermitian_iff_isSymm.mpr p.direction_symmetric)
    simpa only [hSsymm.inv.eq] using h
  have hBdet : Matrix.det B ≠ 0 := by
    dsimp only [B]
    rw [Matrix.det_mul, Matrix.det_mul]
    exact mul_ne_zero (mul_ne_zero hSinvdet direction_nonzero) hSinvdet
  have hconj : S * B * S = p.direction := by
    dsimp only [B]
    calc
      S * (S⁻¹ * p.direction * S⁻¹) * S =
          (S * S⁻¹) * p.direction * (S⁻¹ * S) := by
            simp only [Matrix.mul_assoc]
      _ = p.direction := by
        rw [Matrix.mul_nonsing_inv S hSunit, Matrix.nonsing_inv_mul S hSunit]
        simp
  have hpencil (x : ℝ) : p.matrixAt x = S * (1 + (x - p.center) • B) * S := by
    calc
      p.matrixAt x = S * S + (x - p.center) • (S * B * S) := by
        rw [hSsq, hconj]
        rfl
      _ = S * (1 + (x - p.center) • B) * S := by
        simp [Matrix.mul_add, Matrix.add_mul]
  have hBp : ¬ B.PosSemidef := by
    intro h
    apply hp
    have hh := h.mul_mul_conjTranspose_same S
    simpa only [hSsymm.eq, hconj] using hh
  have hBn : ¬ (-B).PosSemidef := by
    intro h
    apply hn
    have hh := h.mul_mul_conjTranspose_same S
    simpa only [hSsymm.eq, Matrix.mul_neg, Matrix.neg_mul, hconj] using hh
  refine ⟨{
    beta := hBsymm.eigenvalues
    beta_ne_zero := ?_
    base_det_ne_zero := hbase
    factorization := ?_
  }, hermitian_mixed_eigenvalues B hBsymm hBp hBn⟩
  · intro i hi
    apply hBdet
    rw [hBsymm.det_eq_prod_eigenvalues]
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simpa using hi
  · apply Polynomial.funext
    intro x
    rw [p.eval_detPolynomial, SymmetricAffinePencil.detValue, hpencil]
    rw [Matrix.det_mul, Matrix.det_mul]
    have hdetbase : Matrix.det S * Matrix.det S = Matrix.det p.base := by
      rw [← Matrix.det_mul, hSsq]
    rw [det_one_add_smul_of_hermitian B hBsymm]
    simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_prod,
      eval_spectralFactor]
    calc
      Matrix.det S * (∏ i, (1 + (x - p.center) * hBsymm.eigenvalues i)) *
          Matrix.det S = (Matrix.det S * Matrix.det S) *
            ∏ i, (1 + (x - p.center) * hBsymm.eigenvalues i) := by ring
      _ = _ := by rw [hdetbase]

/-- Mixed signs are intrinsic to the determinant, independent of the choice
of its spectral factorization. -/
theorem every_factorization_has_both_signs {n : ℕ} (p : SymmetricAffinePencil n)
    (positive : p.base.PosDef) (direction_nonzero : Matrix.det p.direction ≠ 0)
    (hp : ¬ p.direction.PosSemidef) (hn : ¬ (-p.direction).PosSemidef)
    (c : RootFactorization p) :
    (∃ i, c.beta i < 0) ∧ (∃ j, 0 < c.beta j) := by
  obtain ⟨d, ⟨a, ha⟩, ⟨b, hb⟩⟩ := mixed_factorization_exists p positive direction_nonzero hp hn
  have transfer (i : Fin n) : ∃ j, d.beta i = c.beta j := by
    obtain ⟨j, hj⟩ := (c.eval_eq_zero_iff (d.root i)).mp (d.eval_root i)
    refine ⟨j, ?_⟩
    apply inv_injective
    simpa only [RootFactorization.root, sub_right_inj] using hj
  obtain ⟨i, hi⟩ := transfer a
  obtain ⟨j, hj⟩ := transfer b
  exact ⟨⟨i, hi ▸ ha⟩, ⟨j, hj ▸ hb⟩⟩

/-- Both sides of the true odd-zeta center contain actual roots once h ≥ 2. -/
theorem actual_factorization_has_both_signs (p : Real.Parameters)
    (hp : Real.Admissible p) (hh : 2 ≤ p.h) :
    (∃ i, (General.factorization p (GRAM_POSITIVE p hp)).beta i < 0) ∧
      (∃ j, 0 < (General.factorization p (GRAM_POSITIVE p hp)).beta j) := by
  obtain ⟨hn, hp'⟩ := derivative_indefinite p hp.m_pos hh
  exact every_factorization_has_both_signs (Real.manuscriptPencil p) (GRAM_POSITIVE p hp)
    (PoleDiagonalization.derivativeMatrix_det_ne_zero p) hn hp' _

theorem actual_factorization_not_constant (p : Real.Parameters)
    (hp : Real.Admissible p) (hh : 2 ≤ p.h) :
    ∃ i j, (General.factorization p (GRAM_POSITIVE p hp)).beta i ≠
      (General.factorization p (GRAM_POSITIVE p hp)).beta j := by
  obtain ⟨⟨i, hi⟩, ⟨j, hj⟩⟩ := actual_factorization_has_both_signs p hp hh
  exact ⟨i, j, ne_of_lt (lt_trans hi hj)⟩

end LeanPaper.SlopeIndefinite
#print axioms LeanPaper.SlopeIndefinite.derivative_indefinite
