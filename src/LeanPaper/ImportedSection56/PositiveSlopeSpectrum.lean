import LeanPaper.ImportedSection56.CoefficientGram
import Theorem_3_1_Universal_Hyperbolicity_And_Zero_Free_Disk

/-!
# Principal theorem 5.2(1): full-degree real spectrum for ALL dimensions

A symmetric constant pencil with a positive slope has a constructive
real spectral factorization, exact degree h, and no nonreal complex zeros.
Combined with the actual coefficient Gram positivity, this establishes
the complete finite-dimensional linear-algebra portion of manuscript
Theorem 5.2(1). No infinite-dimensional Krein-cone assertion is inferred.
-/

noncomputable section
open scoped BigOperators MatrixOrder
open Matrix Polynomial
namespace PaperOrder.PrincipalTheorems

/-- The principal h-by-h dual spectral problem: a symmetric constant
    matrix with a strictly positive slope. -/
structure PositiveSlopePencil (h : ℕ) where
  constant : Matrix (Fin h) (Fin h) ℝ
  slope : Matrix (Fin h) (Fin h) ℝ
  constant_symmetric : constant.IsSymm
  slope_posDef : slope.PosDef

namespace PositiveSlopePencil
variable {h : ℕ} (p : PositiveSlopePencil h)

/-- Named polynomial pencil matrix: prevents premature elaboration of the
    dependent `Matrix.det` binder during determinant evaluation. -/
def polynomialMatrix : Matrix (Fin h) (Fin h) (Polynomial ℝ) :=
  fun i j => C (p.constant i j) + X * C (p.slope i j)

/-- Polynomial det(A + X M) for the genuine dual affine-pencil orientation. -/
def detPolynomial : Polynomial ℝ :=
  Matrix.det p.polynomialMatrix

/-- Polynomial evaluation recovers the finite determinant.  Use precisely the
    already-user-verified named-matrix map_det pattern from
    `ManuscriptChain.Spectral.SymmetricAffinePencil.eval_detPolynomial`. -/
theorem eval_detPolynomial (x : ℝ) :
    p.detPolynomial.eval x = Matrix.det (p.constant + x • p.slope) := by
  unfold detPolynomial
  change (Polynomial.evalRingHom x) (Matrix.det p.polynomialMatrix) = _
  rw [(Polynomial.evalRingHom x).map_det]
  congr 1
  ext i j
  simp [polynomialMatrix, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul] <;> ring

end PositiveSlopePencil

/-- Determinant of a translated Hermitian operator is the exact product
    of its translated real eigenvalues, without a nonzero-eigenvalue input. -/
theorem det_add_smul_one_of_hermitian {h : ℕ}
    (B : Matrix (Fin h) (Fin h) ℝ) (hB : B.IsHermitian) (t : ℝ) :
    Matrix.det (B + t • 1) = ∏ i, (t + hB.eigenvalues i) := by
  let e := Unitary.conjStarAlgAut ℝ _ hB.eigenvectorUnitary
  have he : B = e (Matrix.diagonal hB.eigenvalues) := by
    simpa [e, Function.comp_def] using hB.spectral_theorem
  have hmap : B + t • 1 = e (Matrix.diagonal hB.eigenvalues + t • 1) := by
    simp only [map_add, map_one, map_smul, ← he]
  rw [hmap]
  change Matrix.det (e (Matrix.diagonal hB.eigenvalues + t • 1)) = _
  dsimp only [e]
  rw [Unitary.conjStarAlgAut_apply, Matrix.det_mul_comm, ← Matrix.mul_assoc]
  simp only [Unitary.coe_star_mul_self, Matrix.one_mul]
  have hd : Matrix.diagonal hB.eigenvalues + t • (1 : Matrix (Fin h) (Fin h) ℝ) =
      Matrix.diagonal (fun i => t + hB.eigenvalues i) := by
    ext i j
    by_cases hij : i = j <;> simp [hij, Matrix.diagonal, add_comm]
  rw [hd, Matrix.det_diagonal]

/-- Full all-dimensional spectral factorization for positive-slope pencils.
    This is the main spectral statement behind manuscript theorem 5.2(1). -/
theorem positiveSlopePencil_factorization_exists {h : ℕ}
    (p : PositiveSlopePencil h) :
    ∃ beta : Fin h → ℝ,
      p.detPolynomial =
        C (Matrix.det p.slope) * ∏ i, (X + C (beta i)) := by
  let S := CFC.sqrt p.slope
  have hSsq : S * S = p.slope := by
    simpa [S, sq] using CFC.sq_sqrt p.slope p.slope_posDef.posSemidef.nonneg
  have hSsymm : S.IsHermitian :=
    (CFC.sqrt_nonneg p.slope).posSemidef.isHermitian
  have hslope : Matrix.det p.slope ≠ 0 := ne_of_gt p.slope_posDef.det_pos
  have hSdet : Matrix.det S ≠ 0 := by
    have h := congrArg Matrix.det hSsq
    rw [Matrix.det_mul] at h
    intro hz
    simp [hz] at h
    exact hslope h.symm
  have hSunit : IsUnit (Matrix.det S) := isUnit_iff_ne_zero.mpr hSdet
  let B := S⁻¹ * p.constant * S⁻¹
  have hBsymm : B.IsHermitian := by
    have h := Matrix.isHermitian_conjTranspose_mul_mul (S⁻¹)
      (Matrix.isHermitian_iff_isSymm.mpr p.constant_symmetric)
    simpa only [hSsymm.inv.eq] using h
  have hconj : S * B * S = p.constant := by
    dsimp only [B]
    calc
      S * (S⁻¹ * p.constant * S⁻¹) * S =
          (S * S⁻¹) * p.constant * (S⁻¹ * S) := by
            simp only [Matrix.mul_assoc]
      _ = p.constant := by
        rw [Matrix.mul_nonsing_inv S hSunit, Matrix.nonsing_inv_mul S hSunit]
        simp
  have hpencil (x : ℝ) :
      p.constant + x • p.slope = S * (B + x • 1) * S := by
    calc
      p.constant + x • p.slope = S * B * S + x • (S * S) := by
        rw [hconj, hSsq]
      _ = S * (B + x • 1) * S := by
        simp [Matrix.mul_add, Matrix.add_mul]
  refine ⟨hBsymm.eigenvalues, ?_⟩
  apply Polynomial.funext
  intro x
  rw [p.eval_detPolynomial, hpencil]
  rw [Matrix.det_mul, Matrix.det_mul]
  have hdetbase : Matrix.det S * Matrix.det S = Matrix.det p.slope := by
    rw [← Matrix.det_mul, hSsq]
  rw [det_add_smul_one_of_hermitian B hBsymm]
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_prod,
    Polynomial.eval_add, Polynomial.eval_X]
  calc
    Matrix.det S * (∏ i, (x + hBsymm.eigenvalues i)) * Matrix.det S =
        (Matrix.det S * Matrix.det S) *
          ∏ i, (x + hBsymm.eigenvalues i) := by ring
    _ = _ := by rw [hdetbase]

/-! `spectralRoots` and its factorization lemma are methods of
`PositiveSlopePencil`.  In particular, the field-style elaborations
`p.spectralRoots i` and `p.spectralRoots_factorization` below must resolve
in this namespace rather than the outer `PrincipalTheorems` namespace. -/
namespace PositiveSlopePencil

/-- The canonical spectral certificate, constructed rather than assumed. -/
noncomputable def spectralRoots {h : ℕ} (p : PositiveSlopePencil h) :
    Fin h → ℝ :=
  Classical.choose (positiveSlopePencil_factorization_exists p)

/-- Exact polynomial factorization at EVERY dimension h. -/
theorem spectralRoots_factorization {h : ℕ} (p : PositiveSlopePencil h) :
    p.detPolynomial =
      C (Matrix.det p.slope) * ∏ i, (X + C (p.spectralRoots i)) :=
  Classical.choose_spec (positiveSlopePencil_factorization_exists p)

end PositiveSlopePencil

/-- Each of the h displayed real spectral numbers is a root. -/
theorem positiveSlopePencil_real_root {h : ℕ}
    (p : PositiveSlopePencil h) (i : Fin h) :
    p.detPolynomial.eval (-(p.spectralRoots i)) = 0 := by
  rw [p.spectralRoots_factorization]
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_prod,
    Polynomial.eval_add, Polynomial.eval_X]
  have hz : (∏ j : Fin h, (-(p.spectralRoots i) + p.spectralRoots j)) = 0 := by
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    ring
  rw [hz, mul_zero]

/-- The dual determinant has exact full degree h; no singular leading term. -/
theorem positiveSlopePencil_degree {h : ℕ} (p : PositiveSlopePencil h) :
    p.detPolynomial.natDegree = h := by
  have hdet : Matrix.det p.slope ≠ 0 := ne_of_gt p.slope_posDef.det_pos
  have hfactor (i : Fin h) : (X + C (p.spectralRoots i) : ℝ[X]) =
      ManuscriptChain.Spectral.spectralFactor (1 - p.spectralRoots i) 1 := by
    simp [ManuscriptChain.Spectral.spectralFactor]
    ring
  have hdeg (i : Fin h) :
      (X + C (p.spectralRoots i) : ℝ[X]).natDegree = 1 := by
    rw [hfactor]
    exact ManuscriptChain.Spectral.natDegree_spectralFactor
      (1 - p.spectralRoots i) 1 one_ne_zero
  have hnonzero (i : Fin h) :
      (X + C (p.spectralRoots i) : ℝ[X]) ≠ 0 := by
    rw [hfactor]
    exact ManuscriptChain.Spectral.spectralFactor_ne_zero
      (1 - p.spectralRoots i) 1
  rw [p.spectralRoots_factorization,
    Polynomial.natDegree_C_mul hdet]
  have hprod := Polynomial.natDegree_prod (s := Finset.univ)
    (fun i : Fin h => (X + C (p.spectralRoots i) : ℝ[X]))
    (fun i _ => hnonzero i)
  simpa [hdeg] using hprod

/-- Every complex zero of the full-dimensional determinant is REAL. -/
theorem positiveSlopePencil_every_complex_root_real {h : ℕ}
    (p : PositiveSlopePencil h) (z : ℂ)
    (hz : Polynomial.eval₂ (algebraMap ℝ ℂ) z p.detPolynomial = 0) :
    z.im = 0 := by
  have heval : Polynomial.eval₂ (algebraMap ℝ ℂ) z p.detPolynomial =
      ((Matrix.det p.slope : ℝ) : ℂ) *
        ∏ i, (z + (p.spectralRoots i : ℂ)) := by
    rw [p.spectralRoots_factorization]
    simp [Polynomial.eval₂_finsetProd]
  rw [heval] at hz
  have hd : ((Matrix.det p.slope : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt p.slope_posDef.det_pos)
  have hprod := (mul_eq_zero.mp hz).resolve_left hd
  obtain ⟨i, _, hi⟩ := Finset.prod_eq_zero_iff.mp hprod
  have hreal : z = - (p.spectralRoots i : ℂ) := by
    calc
      z = (z + (p.spectralRoots i : ℂ)) - (p.spectralRoots i : ℂ) := by ring
      _ = - (p.spectralRoots i : ℂ) := by rw [hi]; ring
  rw [hreal]
  simp

/-- The paper's independent-coefficient family gives a positive-slope
    pencil and therefore full real-rootedness in arbitrary dimension. -/
theorem independent_coefficients_full_hyperbolicity {h K : ℕ}
    (c : Fin h → Fin (K + 1) → ℝ)
    (constant : Matrix (Fin h) (Fin h) ℝ)
    (hconstant : constant.IsSymm)
    (hc : coefficientRowsSeparate c) :
    ∃ beta : Fin h → ℝ,
      (Matrix.det (fun i j =>
        C (constant i j) + X * C (coefficientSlope c i j)) : ℝ[X]) =
        C (Matrix.det (coefficientSlope c)) * ∏ i, (X + C (beta i)) := by
  let p : PositiveSlopePencil h :=
    { constant := constant
      slope := coefficientSlope c
      constant_symmetric := hconstant
      slope_posDef := coefficientSlope_posDef c hc }
  exact positiveSlopePencil_factorization_exists p

end PaperOrder.PrincipalTheorems

#print axioms PaperOrder.PrincipalTheorems.coefficientSlope_posDef
#print axioms PaperOrder.PrincipalTheorems.positiveSlopePencil_factorization_exists
#print axioms PaperOrder.PrincipalTheorems.positiveSlopePencil_degree
#print axioms PaperOrder.PrincipalTheorems.positiveSlopePencil_every_complex_root_real
#print axioms PaperOrder.PrincipalTheorems.independent_coefficients_full_hyperbolicity
