import LeanPaper.PrincipalMinorRealRoots
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Algebra.Polynomial.Splits

/-!
# Corrected principal-minor degree and root count

For a real symmetric affine pencil with positive-definite base, its determinant
has degree equal to the rank of its direction matrix. Its roots over the reals,
counted with algebraic multiplicity, have that same cardinality. Singular
principal directions therefore contribute fewer roots than the matrix order.

The proof constructs a rank-compatible spectral factorization by positive
square-root congruence. No nonsingularity of the direction is assumed. The
last theorems identify the result with the actual rational principal and
leading-principal determinants of the manuscript. This corrects the printed
universal r-root enumeration; it does not assert interlacing or simple roots.
-/

noncomputable section
open scoped BigOperators MatrixOrder Classical
open Matrix Polynomial
open ManuscriptChain.Spectral
open LeanPaper.SingularSlope

namespace LeanPaper.PrincipalMinorRank

/-- Eigenvalue occurrences, including multiplicities, with zero omitted. -/
def nonzeroCount {n : ℕ} (beta : Fin n → ℝ) : ℕ := by
  classical
  exact Fintype.card {i : Fin n // beta i ≠ 0}

theorem spectralFactor_degree_indicator (center beta : ℝ) :
    (spectralFactor center beta).natDegree = if beta ≠ 0 then 1 else 0 := by
  classical
  by_cases hb : beta ≠ 0
  · simp [hb, natDegree_spectralFactor center beta hb]
  · have hz : beta = 0 := not_ne_iff.mp hb
    simp [hz, spectralFactor]

theorem degree_eq_nonzeroCount {n : ℕ} {p : SymmetricAffinePencil n}
    (w : WeakSpectralFactorization p) :
    p.detPolynomial.natDegree = nonzeroCount w.beta := by
  classical
  rw [w.factorization, Polynomial.natDegree_C_mul w.base_det_ne_zero]
  have hp := Polynomial.natDegree_prod (s := Finset.univ)
    (fun i : Fin n => spectralFactor p.center (w.beta i))
    (fun i _ => spectralFactor_ne_zero p.center (w.beta i))
  rw [hp]
  simp_rw [spectralFactor_degree_indicator]
  unfold nonzeroCount
  rw [Fintype.card_subtype]
  exact Finset.sum_boole _ _

theorem weak_factorization_splits {n : ℕ} {p : SymmetricAffinePencil n}
    (w : WeakSpectralFactorization p) : p.detPolynomial.Splits := by
  classical
  rw [w.factorization]
  apply Polynomial.Splits.C_mul
  apply Polynomial.Splits.prod
  intro i hi
  apply Polynomial.Splits.of_natDegree_le_one
  rw [spectralFactor_degree_indicator]
  split <;> omega

/-- Root multiplicity, rather than distinct root count, matches the degree. -/
theorem roots_card_eq_nonzeroCount {n : ℕ} {p : SymmetricAffinePencil n}
    (w : WeakSpectralFactorization p) :
    p.detPolynomial.roots.card = nonzeroCount w.beta := by
  rw [← (weak_factorization_splits w).natDegree_eq_card_roots]
  exact degree_eq_nonzeroCount w

/-- The whitened eigenvalues are constructed together with their rank identity. -/
theorem rank_compatible_factorization {n : ℕ} (p : SymmetricAffinePencil n)
    (positive : p.base.PosDef) :
    ∃ w : WeakSpectralFactorization p, nonzeroCount w.beta = p.direction.rank := by
  classical
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
  have hfactor : p.detPolynomial =
      C (Matrix.det p.base) * ∏ i, spectralFactor p.center (hBsymm.eigenvalues i) := by
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
  refine ⟨{
    beta := hBsymm.eigenvalues
    base_det_ne_zero := hbase
    factorization := hfactor
  }, ?_⟩
  change nonzeroCount hBsymm.eigenvalues = p.direction.rank
  calc
    nonzeroCount hBsymm.eigenvalues = B.rank := by
      simpa [nonzeroCount] using hBsymm.rank_eq_card_non_zero_eigs.symm
    _ = (S * B * S).rank := by
      rw [Matrix.rank_mul_eq_left_of_det_ne_zero S (S * B) hSdet,
        Matrix.rank_mul_eq_right_of_det_ne_zero S B hSdet]
    _ = p.direction.rank := congrArg Matrix.rank hconj

/-- Exact degree law, including singular or zero directions. -/
theorem degree_eq_direction_rank {n : ℕ} (p : SymmetricAffinePencil n)
    (positive : p.base.PosDef) : p.detPolynomial.natDegree = p.direction.rank := by
  obtain ⟨w, hw⟩ := rank_compatible_factorization p positive
  exact (degree_eq_nonzeroCount w).trans hw

/-- Every root is real and the count with multiplicity is exactly the slope rank. -/
theorem real_roots_card_eq_direction_rank {n : ℕ} (p : SymmetricAffinePencil n)
    (positive : p.base.PosDef) : p.detPolynomial.roots.card = p.direction.rank := by
  obtain ⟨w, hw⟩ := rank_compatible_factorization p positive
  exact (roots_card_eq_nonzeroCount w).trans hw

/-- Any weak spectral witness has the same nonzero count; the count is intrinsic. -/
theorem nonzeroCount_eq_direction_rank {n : ℕ} (p : SymmetricAffinePencil n)
    (positive : p.base.PosDef) (w : WeakSpectralFactorization p) :
    nonzeroCount w.beta = p.direction.rank :=
  (degree_eq_nonzeroCount w).symm.trans (degree_eq_direction_rank p positive)

theorem root_count_le_dimension {n : ℕ} (p : SymmetricAffinePencil n)
    (positive : p.base.PosDef) : p.detPolynomial.roots.card ≤ n := by
  rw [real_roots_card_eq_direction_rank p positive]
  simpa using p.direction.rank_le_card_width

theorem zero_direction_has_no_roots {n : ℕ} (p : SymmetricAffinePencil n)
    (positive : p.base.PosDef) (hz : p.direction = 0) :
    p.detPolynomial.natDegree = 0 ∧ p.detPolynomial.roots.card = 0 := by
  rw [degree_eq_direction_rank p positive, real_roots_card_eq_direction_rank p positive,
    hz, Matrix.rank_zero]
  exact ⟨rfl, rfl⟩

open LeanPaper.PrincipalMinorRealRoots

/-- Degree of the ACTUAL rational principal determinant equals its real slope rank. -/
theorem original_principal_degree_eq_rank (p : ManuscriptChain.Real.Parameters)
    (hp : ManuscriptChain.Real.Admissible p) {r : ℕ} (index : Fin r ↪ Fin p.h) :
    (ManuscriptChain.PrincipalMinors.determinant p index).natDegree =
      (originalPencil p index).direction.rank := by
  have hd := degree_eq_direction_rank (originalPencil p index)
    (originalPencil_base_posDef p hp index)
  rw [originalPencil_detPolynomial, ManuscriptChain.Real.realPolynomial,
    Polynomial.natDegree_map] at hd
  exact hd

/-- The actual determinant's real root multiset has cardinality equal to its slope rank. -/
theorem original_principal_real_roots_card_eq_rank
    (p : ManuscriptChain.Real.Parameters) (hp : ManuscriptChain.Real.Admissible p)
    {r : ℕ} (index : Fin r ↪ Fin p.h) :
    (ManuscriptChain.Real.realPolynomial
      (ManuscriptChain.PrincipalMinors.determinant p index)).roots.card =
        (originalPencil p index).direction.rank := by
  rw [← originalPencil_detPolynomial]
  exact real_roots_card_eq_direction_rank (originalPencil p index)
    (originalPencil_base_posDef p hp index)

/-- Correct rank-sensitive degree and multiplicity count for every actual leading minor. -/
theorem original_leading_degree_and_root_count
    (p : ManuscriptChain.Real.Parameters) (hp : ManuscriptChain.Real.Admissible p)
    (r : ℕ) (hr : r ≤ p.h) :
    let index := ManuscriptChain.PrincipalMinors.leadingIndex p r hr
    (ManuscriptChain.PrincipalMinors.determinant p index).natDegree =
      (originalPencil p index).direction.rank ∧
    (ManuscriptChain.Real.realPolynomial
      (ManuscriptChain.PrincipalMinors.determinant p index)).roots.card =
        (originalPencil p index).direction.rank := by
  exact ⟨original_principal_degree_eq_rank p hp _,
    original_principal_real_roots_card_eq_rank p hp _⟩

end LeanPaper.PrincipalMinorRank

#print axioms LeanPaper.PrincipalMinorRank.degree_eq_direction_rank
#print axioms LeanPaper.PrincipalMinorRank.real_roots_card_eq_direction_rank
#print axioms LeanPaper.PrincipalMinorRank.original_leading_degree_and_root_count
