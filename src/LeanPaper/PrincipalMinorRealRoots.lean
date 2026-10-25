import LeanPaper.SingularSlope
import PaperChain.Stage04PrincipalMinorCenter

/-!
# Every original principal determinant has only real complex zeros

Source candidate; native Windows Lean 4.33 compilation and axiom audit are
pending. This is a corrected partial result for manuscript Theorem 3.4:
it allows singular principal slopes and asserts neither an exact degree
nor interlacing. The selected rational polynomial is identified explicitly
with the affine pencil; Gram positivity is derived from the original
analytic realization, with only the manuscript admissibility assumptions.
-/

noncomputable section
open Polynomial
open ManuscriptChain.Spectral

namespace LeanPaper.PrincipalMinorRealRoots

/-- The actual principal restriction of a symmetric affine pencil. -/
def selectedPencil {n r : ℕ} (p : SymmetricAffinePencil n)
    (index : Fin r → Fin n) : SymmetricAffinePencil r where
  center := p.center
  base := p.base.submatrix index index
  direction := p.direction.submatrix index index
  base_symmetric := by
    ext i j
    have h := congrArg (fun M : Matrix (Fin n) (Fin n) ℝ =>
      M (index i) (index j)) p.base_symmetric
    simpa [Matrix.transpose_apply, Matrix.submatrix] using h
  direction_symmetric := by
    ext i j
    have h := congrArg (fun M : Matrix (Fin n) (Fin n) ℝ =>
      M (index i) (index j)) p.direction_symmetric
    simpa [Matrix.transpose_apply, Matrix.submatrix] using h

theorem selectedPencil_matrixAt {n r : ℕ} (p : SymmetricAffinePencil n)
    (index : Fin r → Fin n) (x : ℝ) :
    (selectedPencil p index).matrixAt x =
      (p.matrixAt x).submatrix index index := by
  ext i j
  rfl

theorem selectedPencil_polynomialMatrix {n r : ℕ}
    (p : SymmetricAffinePencil n) (index : Fin r → Fin n) :
    (selectedPencil p index).polynomialMatrix =
      p.polynomialMatrix.submatrix index index := by
  ext i j
  rfl

/-- A lower-order affine pencil built from the original manuscript entries. -/
def originalPencil (p : ManuscriptChain.Real.Parameters) {r : ℕ}
    (index : Fin r ↪ Fin p.h) : SymmetricAffinePencil r :=
  selectedPencil (ManuscriptChain.Real.manuscriptPencil p) index

/-- The new real determinant is exactly the coefficient embedding of the
existing rational principal determinant; no new polynomial is postulated. -/
theorem originalPencil_detPolynomial (p : ManuscriptChain.Real.Parameters)
    {r : ℕ} (index : Fin r ↪ Fin p.h) :
    (originalPencil p index).detPolynomial =
      ManuscriptChain.Real.realPolynomial
        (ManuscriptChain.PrincipalMinors.determinant p index) := by
  unfold originalPencil SymmetricAffinePencil.detPolynomial
  rw [selectedPencil_polynomialMatrix,
    ManuscriptChain.Real.manuscriptPencil_polynomialMatrix]
  exact ((Polynomial.mapRingHom (Rat.castHom ℝ)).map_det
    (ManuscriptChain.PrincipalMinors.pencil p index)).symm

/-- Evaluation in the complex numbers respects the exact rational source. -/
theorem complex_eval_transport (p : ManuscriptChain.Real.Parameters)
    {r : ℕ} (index : Fin r ↪ Fin p.h) (z : ℂ) :
    Polynomial.eval₂ (algebraMap ℝ ℂ) z
        (originalPencil p index).detPolynomial =
      Polynomial.eval₂ (algebraMap ℚ ℂ) z
        (ManuscriptChain.PrincipalMinors.determinant p index) := by
  rw [originalPencil_detPolynomial, ManuscriptChain.Real.realPolynomial,
    Polynomial.eval₂_map]
  congr 1

/-- Positivity is obtained from the original Bose-density construction. -/
theorem originalPencil_base_posDef (p : ManuscriptChain.Real.Parameters)
    (hp : ManuscriptChain.Real.Admissible p)
    {r : ℕ} (index : Fin r ↪ Fin p.h) :
    (originalPencil p index).base.PosDef := by
  exact ManuscriptChain.PrincipalMinors.gram_posDef p hp index

/-- Every complex zero of an arbitrary original principal determinant is
real, including when the restricted derivative matrix is singular. -/
theorem original_principal_zeros_real (p : ManuscriptChain.Real.Parameters)
    (hp : ManuscriptChain.Real.Admissible p)
    {r : ℕ} (index : Fin r ↪ Fin p.h) (z : ℂ)
    (hz : Polynomial.eval₂ (algebraMap ℚ ℂ) z
      (ManuscriptChain.PrincipalMinors.determinant p index) = 0) :
    z.im = 0 := by
  apply SingularSlope.all_complex_roots_real_even_if_slope_singular
    (originalPencil p index) (originalPencil_base_posDef p hp index) z
  rw [complex_eval_transport]
  exact hz

/-- In particular the actual leading principal minors have only real zeros;
the statement makes no assertion that their degree equals their order. -/
theorem original_leading_principal_zeros_real
    (p : ManuscriptChain.Real.Parameters)
    (hp : ManuscriptChain.Real.Admissible p) (r : ℕ) (hr : r ≤ p.h) (z : ℂ)
    (hz : Polynomial.eval₂ (algebraMap ℚ ℂ) z
      (ManuscriptChain.PrincipalMinors.determinant p
        (ManuscriptChain.PrincipalMinors.leadingIndex p r hr)) = 0) :
    z.im = 0 :=
  original_principal_zeros_real p hp
    (ManuscriptChain.PrincipalMinors.leadingIndex p r hr) z hz

end LeanPaper.PrincipalMinorRealRoots

#print axioms LeanPaper.PrincipalMinorRealRoots.originalPencil_detPolynomial
#print axioms LeanPaper.PrincipalMinorRealRoots.complex_eval_transport
#print axioms LeanPaper.PrincipalMinorRealRoots.originalPencil_base_posDef
#print axioms LeanPaper.PrincipalMinorRealRoots.original_principal_zeros_real
#print axioms LeanPaper.PrincipalMinorRealRoots.original_leading_principal_zeros_real
