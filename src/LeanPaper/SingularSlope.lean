import Theorem_3_1_Universal_Hyperbolicity_And_Zero_Free_Disk

/-!
# Singular slopes: exact spectral factors and real determinant zeros

SOURCE CANDIDATE ONLY; native Windows Lean 4.33 compilation and axiom audit
are pending. Adapted from the commit-pinned principal-theorems archive
listed in provenance/principal_minor_extension.json. The construction uses
only the already-active ManuscriptChain.Spectral definitions and APIs.

Unlike the full-pencil factorization in Theorem 3.1, this theorem allows the
symmetric derivative matrix M to be singular. It is therefore applicable to
principal pencils with degree drops. The only matrix condition is G.PosDef;
there is no hypothesis requiring det M != 0 or nonzero eigenvalues.

The certificate expresses det(G+(X-xi)M) as a product with possibly constant
factors. A zero slope eigenvalue produces factor 1, not a spurious root.
-/

noncomputable section
open scoped BigOperators MatrixOrder
open Matrix Polynomial
open ManuscriptChain.Spectral

namespace LeanPaper.SingularSlope

/-- An exact spectral factorization that permits zero eigenvalues. -/
structure WeakSpectralFactorization {n : ℕ} (p : SymmetricAffinePencil n) where
  beta : Fin n → ℝ
  base_det_ne_zero : Matrix.det p.base ≠ 0
  factorization : p.detPolynomial =
    C (Matrix.det p.base) * ∏ i, spectralFactor p.center (beta i)

/-- The factorization exists for every positive-definite symmetric affine
pencil, *without* nonsingularity of its derivative matrix. -/
theorem weakSpectralFactorization_nonempty_of_posDef {n : ℕ}
    (p : SymmetricAffinePencil n) (positive : p.base.PosDef) :
    Nonempty (WeakSpectralFactorization p) := by
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
  let B := S⁻¹ * p.direction * S⁻¹
  have hBsymm : B.IsHermitian := by
    have h := Matrix.isHermitian_conjTranspose_mul_mul (S⁻¹)
      (Matrix.isHermitian_iff_isSymm.mpr p.direction_symmetric)
    simpa only [hSsymm.inv.eq] using h
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
  refine ⟨{
    beta := hBsymm.eigenvalues
    base_det_ne_zero := hbase
    factorization := ?_
  }⟩
  apply Polynomial.funext
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

/-- Choose the general (possibly singular) spectral certificate. -/
noncomputable def weakSpectralFactorizationOfPosDef {n : ℕ}
    (p : SymmetricAffinePencil n) (positive : p.base.PosDef) :
    WeakSpectralFactorization p :=
  Classical.choice (weakSpectralFactorization_nonempty_of_posDef p positive)

namespace WeakSpectralFactorization
variable {n : ℕ} {p : SymmetricAffinePencil n} (w : WeakSpectralFactorization p)

-- Keep the spectral witness available in the bodies of the next lemmas,
-- even when their conclusions do not mention it syntactically.
include w

/-- Every complex zero comes from a NONZERO eigenvalue, even though the
underlying slope matrix may have zero eigenvalues. -/
theorem complex_zero_has_nonzero_beta (z : ℂ)
    (hz : Polynomial.eval₂ (algebraMap ℝ ℂ) z p.detPolynomial = 0) :
    ∃ i : Fin n, w.beta i ≠ 0 ∧ z = ((p.center - (w.beta i)⁻¹ : ℝ) : ℂ) := by
  have heval : Polynomial.eval₂ (algebraMap ℝ ℂ) z p.detPolynomial =
      ((Matrix.det p.base : ℝ) : ℂ) *
        ∏ i, (1 + (z - (p.center : ℂ)) * (w.beta i : ℂ)) := by
    rw [w.factorization]
    simp [spectralFactor, Polynomial.eval₂_finsetProd]
  rw [heval] at hz
  have hd : ((Matrix.det p.base : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr w.base_det_ne_zero
  have hp := (mul_eq_zero.mp hz).resolve_left hd
  obtain ⟨i, _, hi⟩ := Finset.prod_eq_zero_iff.mp hp
  have hbeta : w.beta i ≠ 0 := by
    intro hzero
    have hone : (1 : ℂ) = 0 := by simpa [hzero] using hi
    exact one_ne_zero hone
  have hb : (w.beta i : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hbeta
  have hx := (linear_factor_eq_zero_iff
    (p.center : ℂ) (w.beta i : ℂ) z hb).mp hi
  refine ⟨i, hbeta, ?_⟩
  simpa using hx

/-- ALL complex roots lie on the real axis, without det M != 0. -/
theorem every_complex_zero_real (z : ℂ)
    (hz : Polynomial.eval₂ (algebraMap ℝ ℂ) z p.detPolynomial = 0) :
    z.im = 0 := by
  obtain ⟨i, _, rfl⟩ := w.complex_zero_has_nonzero_beta z hz
  simp

/-- A positive-definite base excludes the centre of every pencil. -/
theorem center_ne_zero : p.detPolynomial.eval p.center ≠ 0 := by
  rw [p.eval_detPolynomial_center]
  exact w.base_det_ne_zero

end WeakSpectralFactorization

/-- Unconditional algebraic correction of the printed principal-minor claim:
positive Gram and symmetric slope force real roots even when the slope drops
rank and the characteristic polynomial has fewer than n roots. -/
theorem all_complex_roots_real_even_if_slope_singular {n : ℕ}
    (p : SymmetricAffinePencil n) (positive : p.base.PosDef)
    (z : ℂ)
    (hz : Polynomial.eval₂ (algebraMap ℝ ℂ) z p.detPolynomial = 0) :
    z.im = 0 :=
  (weakSpectralFactorizationOfPosDef p positive).every_complex_zero_real z hz

end LeanPaper.SingularSlope

#print axioms LeanPaper.SingularSlope.all_complex_roots_real_even_if_slope_singular
