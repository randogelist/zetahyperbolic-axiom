import Theorem_3_1_Universal_Hyperbolicity_And_Zero_Free_Disk
import Mathlib.Analysis.Matrix.Order
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Tactic

/-!
# Theorem 5.2(1): dual (positive-slope) spectral theorem

The Section-3.1 spectral argument assumes a positive-definite constant
matrix. The two-variable Beukers pencil reverses the geometry: its X-slope
is positive definite, while the constant matrix may be indefinite or even
singular. This module proves the corresponding *dual* finite-dimensional
spectral theorem in arbitrary dimension without assuming constant-matrix
positivity/invertibility.

Its direction positivity hypothesis is discharged for the actual rational
Beukers coefficient pencil by `Theorem_5_2_ActualDual` when the coefficient
rows are linearly independent. It is NOT an additional analytic witness.
-/

noncomputable section
open scoped BigOperators MatrixOrder
open Matrix Polynomial

namespace PaperAdvances.Theorem5_2_RealRoots

open ManuscriptChain.Spectral

/-- Spectral determinant formula for an arbitrary real symmetric matrix,
    with the scalar perturbation on the identity rather than on the matrix. -/
theorem det_add_scalar_of_hermitian {n : ℕ}
    (B : Matrix (Fin n) (Fin n) ℝ) (hB : B.IsHermitian) (t : ℝ) :
    (B + t • (1 : Matrix (Fin n) (Fin n) ℝ)).det =
      ∏ i, (hB.eigenvalues i + t) := by
  let e := Unitary.conjStarAlgAut ℝ _ hB.eigenvectorUnitary
  have he : B = e (diagonal hB.eigenvalues) := by
    simpa [e, Function.comp_def] using hB.spectral_theorem
  have hmap : B + t • (1 : Matrix (Fin n) (Fin n) ℝ) =
      e (diagonal hB.eigenvalues + t • (1 : Matrix (Fin n) (Fin n) ℝ)) := by
    simp only [map_add, map_one, map_smul, ← he]
  rw [hmap]
  change Matrix.det
    (e (diagonal hB.eigenvalues + t • (1 : Matrix (Fin n) (Fin n) ℝ))) = _
  dsimp only [e]
  rw [Unitary.conjStarAlgAut_apply, Matrix.det_mul_comm, ← Matrix.mul_assoc]
  simp only [Unitary.coe_star_mul_self, Matrix.one_mul]
  have hd : diagonal hB.eigenvalues + t • (1 : Matrix (Fin n) (Fin n) ℝ) =
      diagonal (fun i => hB.eigenvalues i + t) := by
    ext i j
    by_cases h : i = j <;> simp [h, Matrix.diagonal]
  rw [hd, Matrix.det_diagonal]

/-- Any symmetric affine pencil with a strictly positive definite slope
    splits into real linear factors. The constant matrix need not be
    invertible, nor have any definite sign. -/
theorem positive_slope_factorization {n : ℕ}
    (p : SymmetricAffinePencil n) (hp : p.direction.PosDef) :
    ∃ beta : Fin n → ℝ,
      p.detPolynomial =
        C p.direction.det * ∏ i, (X + C (beta i - p.center)) := by
  let S := CFC.sqrt p.direction
  have hSsq : S * S = p.direction := by
    simpa [S, sq] using CFC.sq_sqrt p.direction hp.posSemidef.nonneg
  have hSsymm : S.IsHermitian :=
    (CFC.sqrt_nonneg p.direction).posSemidef.isHermitian
  have hdir : Matrix.det p.direction ≠ 0 := ne_of_gt hp.det_pos
  have hSdet : Matrix.det S ≠ 0 := by
    have h := congrArg Matrix.det hSsq
    rw [Matrix.det_mul] at h
    intro hz
    simp [hz] at h
    exact hdir h.symm
  have hSunit : IsUnit (Matrix.det S) := isUnit_iff_ne_zero.mpr hSdet
  let B := S⁻¹ * p.base * S⁻¹
  have hBsymm : B.IsHermitian := by
    have h := Matrix.isHermitian_conjTranspose_mul_mul (S⁻¹)
      (Matrix.isHermitian_iff_isSymm.mpr p.base_symmetric)
    simpa only [hSsymm.inv.eq] using h
  have hconj : S * B * S = p.base := by
    dsimp only [B]
    calc
      S * (S⁻¹ * p.base * S⁻¹) * S =
          (S * S⁻¹) * p.base * (S⁻¹ * S) := by
            simp only [Matrix.mul_assoc]
      _ = p.base := by
        rw [Matrix.mul_nonsing_inv S hSunit,
          Matrix.nonsing_inv_mul S hSunit]
        simp
  have hpencil (x : ℝ) :
      p.matrixAt x =
        S * (B + (x - p.center) • (1 : Matrix (Fin n) (Fin n) ℝ)) * S := by
    calc
      p.matrixAt x = S * B * S + (x - p.center) • (S * S) := by
        rw [hconj, hSsq]
        rfl
      _ = S * (B + (x - p.center) • (1 : Matrix (Fin n) (Fin n) ℝ)) * S := by
        simp [Matrix.mul_add, Matrix.add_mul]
  have hdetdir : Matrix.det S * Matrix.det S = Matrix.det p.direction := by
    rw [← Matrix.det_mul, hSsq]
  refine ⟨hBsymm.eigenvalues, ?_⟩
  apply Polynomial.funext
  intro x
  rw [p.eval_detPolynomial]
  change Matrix.det (p.matrixAt x) = _
  rw [hpencil, Matrix.det_mul, Matrix.det_mul,
    det_add_scalar_of_hermitian B hBsymm]
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_prod,
    Polynomial.eval_add, Polynomial.eval_X]
  calc
    Matrix.det S * (∏ i, (hBsymm.eigenvalues i + (x - p.center))) * Matrix.det S =
        (Matrix.det S * Matrix.det S) *
          (∏ i, (hBsymm.eigenvalues i + (x - p.center))) := by ring
    _ = Matrix.det p.direction *
          (∏ i, (x + (hBsymm.eigenvalues i - p.center))) := by
            rw [hdetdir]
            congr 1
            apply Finset.prod_congr rfl
            intro i _
            ring

/-- The determinant has exactly the full pencil dimension, including when
    its matrix at the distinguished center is singular. -/
theorem positive_slope_exact_degree {n : ℕ}
    (p : SymmetricAffinePencil n) (hp : p.direction.PosDef) :
    p.detPolynomial.natDegree = n := by
  obtain ⟨beta, hfactor⟩ := positive_slope_factorization p hp
  rw [hfactor, Polynomial.natDegree_C_mul (ne_of_gt hp.det_pos)]
  have hprod := Polynomial.natDegree_prod (s := Finset.univ)
    (fun i : Fin n => X + C (beta i - p.center))
    (fun i _ => (Polynomial.monic_X_add_C (beta i - p.center)).ne_zero)
  have hsum : (∑ _i : Fin n, (1 : ℕ)) = n := by
    simp only [Finset.sum_const, Finset.card_fin, Nat.nsmul_eq_mul, mul_one]
  calc
    (∏ i : Fin n, (X + C (beta i - p.center))).natDegree =
        (∑ i : Fin n, (X + C (beta i - p.center)).natDegree) := hprod
    _ = (∑ _i : Fin n, (1 : ℕ)) := by
      simp only [Polynomial.natDegree_X_add_C]
    _ = n := hsum

/-- Every complex zero of the dual pencil is real. No definiteness of the
    constant matrix and no nonzero-eigenvalue hypothesis are imposed. -/
theorem positive_slope_complex_roots_real {n : ℕ}
    (p : SymmetricAffinePencil n) (hp : p.direction.PosDef)
    (z : ℂ)
    (hz : Polynomial.eval₂ (algebraMap ℝ ℂ) z p.detPolynomial = 0) :
    z.im = 0 := by
  obtain ⟨beta, hfactor⟩ := positive_slope_factorization p hp
  have heval : Polynomial.eval₂ (algebraMap ℝ ℂ) z p.detPolynomial =
      ((p.direction.det : ℝ) : ℂ) *
        ∏ i, (z + ((beta i - p.center : ℝ) : ℂ)) := by
    rw [hfactor]
    simp [Polynomial.eval₂_finsetProd]
  rw [heval] at hz
  have hdet : ((p.direction.det : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt hp.det_pos)
  have hzero := (mul_eq_zero.mp hz).resolve_left hdet
  obtain ⟨i, _, hi⟩ := Finset.prod_eq_zero_iff.mp hzero
  have him := congrArg Complex.im hi
  simpa using him

end PaperAdvances.Theorem5_2_RealRoots

#print axioms PaperAdvances.Theorem5_2_RealRoots.det_add_scalar_of_hermitian
#print axioms PaperAdvances.Theorem5_2_RealRoots.positive_slope_factorization
#print axioms PaperAdvances.Theorem5_2_RealRoots.positive_slope_exact_degree
#print axioms PaperAdvances.Theorem5_2_RealRoots.positive_slope_complex_roots_real
