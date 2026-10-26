import MAIN_CHAIN_ASSEMBLED
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Matrix.Spectrum

/-!
# The actual operator-norm disk in Theorem 3.1

The norm in this module is the operator norm for the Euclidean inner product.
The whitening matrix is the actual positive-square-root congruence
`B = (sqrt G)⁻¹ M (sqrt G)⁻¹`. A constructed spectral witness has maximum
absolute eigenvalue equal to `‖B‖`; hence the existing exact zero-free radius
is precisely `1 / ‖B‖`. The last endpoints apply to the actual manuscript
polynomials, with positivity discharged by the proved hyperbolic measure.
No exponential norm estimate or irrationality consequence is claimed.
-/

noncomputable section
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator
open Matrix Polynomial
open ManuscriptChain.Spectral

namespace LeanPaper.OperatorNormDisk

/-- Positive-square-root normalization of the actual symmetric pencil. -/
def whitened {n : ℕ} (p : SymmetricAffinePencil n) : Matrix (Fin n) (Fin n) ℝ :=
  (CFC.sqrt p.base)⁻¹ * p.direction * (CFC.sqrt p.base)⁻¹

/-- The Euclidean operator norm of a real symmetric matrix is its maximum
absolute eigenvalue, represented by the sup norm of the eigenvalue vector. -/
theorem hermitian_norm_eq_eigenvalue_norm {n : ℕ}
    {B : Matrix (Fin n) (Fin n) ℝ} (hB : B.IsHermitian) :
    ‖B‖ = ‖hB.eigenvalues‖ := by
  have hdiag : B = Unitary.conjStarAlgAut ℝ _ hB.eigenvectorUnitary
      (Matrix.diagonal hB.eigenvalues) := by
    simpa [Function.comp_def] using hB.spectral_theorem
  conv_lhs => rw [hdiag]
  simp only [Unitary.conjStarAlgAut_apply, ← Unitary.coe_star,
    CStarRing.norm_mul_coe_unitary, CStarRing.norm_coe_unitary_mul,
    Matrix.l2_opNorm_diagonal]

/-- Construct the eigenvalues and their operator-norm identity together. -/
theorem norm_compatible_factorization {n : ℕ}
    (p : SymmetricAffinePencil n) (positive : p.base.PosDef)
    (direction_nonzero : Matrix.det p.direction ≠ 0) :
    ∃ c : RootFactorization p, ‖c.beta‖ = ‖whitened p‖ := by
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
  refine ⟨{
    beta := hBsymm.eigenvalues
    beta_ne_zero := ?_
    base_det_ne_zero := hbase
    factorization := ?_
  }, ?_⟩
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

  · exact (hermitian_norm_eq_eigenvalue_norm hBsymm).symm

/-- Every complex root lies at least the reciprocal operator norm from the center. -/
theorem complex_root_distance {n : ℕ} (p : SymmetricAffinePencil n)
    (positive : p.base.PosDef) (direction_nonzero : Matrix.det p.direction ≠ 0)
    (z : ℂ) (hz : Polynomial.eval₂ (algebraMap ℝ ℂ) z p.detPolynomial = 0) :
    1 / ‖whitened p‖ ≤ ‖z - (p.center : ℂ)‖ := by
  obtain ⟨c, hc⟩ := norm_compatible_factorization p positive direction_nonzero
  obtain ⟨i, rfl⟩ := c.complex_root_location z hz
  have hb (j : Fin n) : |c.beta j| ≤ ‖whitened p‖ := by
    rw [← hc]
    simpa only [Real.norm_eq_abs] using norm_le_pi_norm c.beta j
  simpa [← Complex.ofReal_sub] using c.root_distance_lower_bound _ hb i

/-- When the pencil is nonempty, the reciprocal norm is attained by a root. -/
theorem complex_root_on_boundary {n : ℕ} (p : SymmetricAffinePencil n)
    (hn : 0 < n) (positive : p.base.PosDef)
    (direction_nonzero : Matrix.det p.direction ≠ 0) :
    0 < 1 / ‖whitened p‖ ∧
    ∃ z : ℂ, Polynomial.eval₂ (algebraMap ℝ ℂ) z p.detPolynomial = 0 ∧
      ‖z - (p.center : ℂ)‖ = 1 / ‖whitened p‖ := by
  classical
  obtain ⟨c, hc⟩ := norm_compatible_factorization p positive direction_nonzero
  have hnonempty : (Finset.univ : Finset (Fin n)).Nonempty :=
    ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_sup' hnonempty (fun i => |c.beta i|)
  have himax : |c.beta i| = ‖c.beta‖ := by
    apply le_antisymm
    · simpa only [Real.norm_eq_abs] using norm_le_pi_norm c.beta i
    · apply (pi_norm_le_iff_of_nonneg (abs_nonneg _)).mpr
      intro j
      rw [Real.norm_eq_abs, ← hi]
      exact Finset.le_sup' (fun i => |c.beta i|) (Finset.mem_univ j)
  have hnpositive : 0 < ‖whitened p‖ := by
    rw [← hc, ← himax]
    exact abs_pos.mpr (c.beta_ne_zero i)
  refine ⟨one_div_pos.mpr hnpositive, (c.root i : ℂ), ?_, ?_⟩
  · have he := Polynomial.eval₂_at_apply (algebraMap ℝ ℂ)
      (c.root i) (p := p.detPolynomial)
    simpa only [Complex.coe_algebraMap, c.eval_root, map_zero] using he
  · have hd := c.root_distance i
    rw [himax, hc] at hd
    simpa [← Complex.ofReal_sub] using hd

open ManuscriptChain

/-- The existing exact radius is the literal inverse operator norm in the paper. -/
theorem actual_radius_eq_inverse_norm (p : Real.Parameters)
    (hp : Real.Admissible p) (positive : General.GramPositive p) :
    General.zeroFreeRadius p hp positive = 1 / ‖whitened (Real.manuscriptPencil p)‖ := by
  apply le_antisymm
  · obtain ⟨_, z, hz, hd⟩ := complex_root_on_boundary (Real.manuscriptPencil p)
      (Nat.sub_pos_of_lt hp.N_lt_K) positive (General.derivative_nonsingular p)
    have hroot : General.ComplexRoot p z := by
      rwa [General.complex_eval_transport] at hz
    have hbound := General.complex_root_distance p hp positive z hroot
    change ‖z - (Real.zeta p.weight : ℂ)‖ =
      1 / ‖whitened (Real.manuscriptPencil p)‖ at hd
    rw [hd] at hbound
    exact hbound
  · obtain ⟨z, hz, hd⟩ := General.complex_root_on_boundary p hp positive
    have hroot : Polynomial.eval₂ (algebraMap ℝ ℂ) z
        (Real.manuscriptPencil p).detPolynomial = 0 := by
      rw [General.complex_eval_transport]
      exact hz
    have hbound := complex_root_distance (Real.manuscriptPencil p) positive
      (General.derivative_nonsingular p) z hroot
    simpa only [Real.manuscriptPencil_center, hd] using hbound

/-- Actual determinant roots satisfy the printed operator-norm bound, with
positive definiteness supplied by the proved analytic Gram realization. -/
theorem actual_root_distance (p : Real.Parameters) (hp : Real.Admissible p)
    (z : ℂ) (hz : General.ComplexRoot p z) :
    1 / ‖whitened (Real.manuscriptPencil p)‖ ≤
      ‖z - (Real.zeta p.weight : ℂ)‖ := by
  rw [← actual_radius_eq_inverse_norm p hp (GRAM_POSITIVE p hp)]
  exact General.complex_root_distance p hp (GRAM_POSITIVE p hp) z hz

/-- An exact norm disk for the actual polynomial, including its attained boundary. -/
theorem actual_exact_norm_disk (p : Real.Parameters) (hp : Real.Admissible p) :
    0 < 1 / ‖whitened (Real.manuscriptPencil p)‖ ∧
    (∀ z : ℂ, ‖z - (Real.zeta p.weight : ℂ)‖ <
      1 / ‖whitened (Real.manuscriptPencil p)‖ → ¬ General.ComplexRoot p z) ∧
    (∃ z : ℂ, General.ComplexRoot p z ∧
      ‖z - (Real.zeta p.weight : ℂ)‖ = 1 / ‖whitened (Real.manuscriptPencil p)‖) := by
  rw [← actual_radius_eq_inverse_norm p hp (GRAM_POSITIVE p hp)]
  exact ⟨General.zeroFreeRadius_pos p hp (GRAM_POSITIVE p hp),
    General.complex_zero_free_disk p hp (GRAM_POSITIVE p hp),
    General.complex_root_on_boundary p hp (GRAM_POSITIVE p hp)⟩

/-- The original uploaded `Delta_poly` has this same literal norm radius. -/
theorem original_root_distance (p : Zetahyperbolic.HankelParams)
    (k : ℕ) (hk : 1 ≤ k) (z : ℂ)
    (hz : (Zetahyperbolic.Delta_poly p k).eval₂ (algebraMap ℚ ℂ) z = 0) :
    1 / ‖whitened (Real.manuscriptPencil
      (Zetahyperbolic.ManuscriptCompatibility.toParameters p k))‖ ≤
        ‖z - (Real.zeta (2 * k + 1) : ℂ)‖ := by
  let q := Zetahyperbolic.ManuscriptCompatibility.toParameters p k
  have hq : Real.Admissible q :=
    Zetahyperbolic.ManuscriptCompatibility.toParameters_admissible p k hk
  apply actual_root_distance q hq z
  simpa [General.ComplexRoot, q,
    Zetahyperbolic.ManuscriptCompatibility.Delta_poly_eq_delta] using hz

end LeanPaper.OperatorNormDisk

#print axioms LeanPaper.OperatorNormDisk.hermitian_norm_eq_eigenvalue_norm
#print axioms LeanPaper.OperatorNormDisk.actual_radius_eq_inverse_norm
#print axioms LeanPaper.OperatorNormDisk.actual_exact_norm_disk
#print axioms LeanPaper.OperatorNormDisk.original_root_distance
