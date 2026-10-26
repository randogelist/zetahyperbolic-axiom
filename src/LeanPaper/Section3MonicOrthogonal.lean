import MAIN_CHAIN_ASSEMBLED
import Mathlib.Analysis.Matrix.LDL
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.Tactic

/-!
# Manuscript 3.8: monic orthogonal-polynomial construction, finite core

This module ports ONLY the exact LDL-based monic polynomial and positive
normalization construction from the continuation branch.  Its candidate
statements are instantiated on the actual odd-zeta Gram matrix via the
already accepted `ManuscriptChain.GRAM_POSITIVE`.

Not proved here: orthogonality of these polynomials for the manuscript
integral, the inverse-Gram reproducing kernel, Christoffel–Darboux identity,
or differentiation of the Laplace-deformed Gram integral.

Original donor: snditeration@0cee4ea / Section3/ChristoffelDarboux.lean.
Its overall continuation CI failed later in that source; these lemmas require
their own receiving-project compilation and transitive axiom check.
-/

noncomputable section
open scoped BigOperators MatrixOrder
open Matrix Polynomial

namespace LeanPaper.Section3MonicOrthogonal

variable {n : ℕ} {G : Matrix (Fin n) (Fin n) ℝ}

def orthogonalCoefficients (hG : G.PosDef) (i : Fin n) : Fin n → ℝ :=
  fun j => LDL.lowerInv hG i j / LDL.lowerInv hG i i

def monicPolynomial (hG : G.PosDef) (i : Fin n) : ℝ[X] :=
  Polynomial.ofFn n (orthogonalCoefficients hG i)

def squaredNorm (hG : G.PosDef) (i : Fin n) : ℝ :=
  LDL.diagEntries hG i / (LDL.lowerInv hG i i)^2

def kernel (hG : G.PosDef) (t u : ℝ) : ℝ :=
  ∑ i, (monicPolynomial hG i).eval t * (monicPolynomial hG i).eval u /
    squaredNorm hG i

theorem lower_diagonal_ne_zero (hG : G.PosDef) (i : Fin n) :
    LDL.lowerInv hG i i ≠ 0 := by
  have hd : (LDL.lowerInv hG).det ≠ 0 :=
    (Matrix.isUnit_det_of_invertible (LDL.lowerInv hG)).ne_zero
  rw [Matrix.det_of_isLowerTriangular _ (fun _ _ hij => LDL.lowerInv_triangular hG hij)] at hd
  exact (Finset.prod_ne_zero_iff.mp hd) i (Finset.mem_univ i)

theorem diagonal_positive (hG : G.PosDef) (i : Fin n) :
    0 < LDL.diagEntries hG i := by
  have hd : (LDL.diag hG).PosDef := by
    rw [LDL.diag_eq_lowerInv_conj]
    exact hG.mul_mul_conjTranspose_same
      (Matrix.vecMul_injective_of_invertible (LDL.lowerInv hG))
  simpa only [LDL.diag, Matrix.diagonal_apply_eq] using hd.diag_pos (i := i)

theorem squaredNorm_positive (hG : G.PosDef) (i : Fin n) :
    0 < squaredNorm hG i :=
  div_pos (diagonal_positive hG i) (sq_pos_of_ne_zero (lower_diagonal_ne_zero hG i))

theorem monicPolynomial_coeff_self (hG : G.PosDef) (i : Fin n) :
    (monicPolynomial hG i).coeff i.val = 1 := by
  simp [monicPolynomial, Polynomial.ofFn_coeff_eq_val_of_lt _ i.isLt,
    orthogonalCoefficients, lower_diagonal_ne_zero]

theorem monicPolynomial_coeff_above (hG : G.PosDef) (i : Fin n) {j : ℕ}
    (hij : i.val < j) : (monicPolynomial hG i).coeff j = 0 := by
  by_cases hj : j < n
  · rw [monicPolynomial, Polynomial.ofFn_coeff_eq_val_of_lt _ hj]
    simp only [orthogonalCoefficients,
      LDL.lowerInv_triangular hG (show i < (⟨j, hj⟩ : Fin n) from hij), zero_div]
  · exact Polynomial.ofFn_coeff_eq_zero_of_ge _ (Nat.le_of_not_gt hj)

theorem monicPolynomial_natDegree (hG : G.PosDef) (i : Fin n) :
    (monicPolynomial hG i).natDegree = i.val := by
  apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
  · exact Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
      (fun _ hij => monicPolynomial_coeff_above hG i hij)
  · rw [monicPolynomial_coeff_self]
    exact one_ne_zero

theorem monicPolynomial_monic (hG : G.PosDef) (i : Fin n) :
    (monicPolynomial hG i).Monic := by
  unfold Polynomial.Monic Polynomial.leadingCoeff
  rw [monicPolynomial_natDegree, monicPolynomial_coeff_self]


/-- The actual Gram matrix is positive definite by the already certified
hyperbolic integral realization. -/
theorem actualGram_posDef (p : ManuscriptChain.Real.Parameters)
    (hp : ManuscriptChain.Real.Admissible p) :
    (ManuscriptChain.Real.gram p (ManuscriptChain.Real.zeta p.weight)).PosDef :=
  ManuscriptChain.GRAM_POSITIVE p hp

/-- A monic polynomial of each degree below the actual Gram size. -/
noncomputable def actualMonicPolynomial
    (p : ManuscriptChain.Real.Parameters)
    (hp : ManuscriptChain.Real.Admissible p)
    (i : Fin p.h) : ℝ[X] :=
  monicPolynomial (actualGram_posDef p hp) i

theorem actualMonicPolynomial_monic
    (p : ManuscriptChain.Real.Parameters)
    (hp : ManuscriptChain.Real.Admissible p)
    (i : Fin p.h) :
    (actualMonicPolynomial p hp i).Monic :=
  monicPolynomial_monic (actualGram_posDef p hp) i

theorem actualMonicPolynomial_degree
    (p : ManuscriptChain.Real.Parameters)
    (hp : ManuscriptChain.Real.Admissible p)
    (i : Fin p.h) :
    (actualMonicPolynomial p hp i).natDegree = i.val :=
  monicPolynomial_natDegree (actualGram_posDef p hp) i

/-- No additional positivity hypothesis: norms come from the actual Gram. -/
noncomputable def actualSquaredNorm
    (p : ManuscriptChain.Real.Parameters)
    (hp : ManuscriptChain.Real.Admissible p)
    (i : Fin p.h) : ℝ :=
  squaredNorm (actualGram_posDef p hp) i

theorem actualSquaredNorm_positive
    (p : ManuscriptChain.Real.Parameters)
    (hp : ManuscriptChain.Real.Admissible p)
    (i : Fin p.h) :
    0 < actualSquaredNorm p hp i :=
  squaredNorm_positive (actualGram_posDef p hp) i

end LeanPaper.Section3MonicOrthogonal

#print axioms LeanPaper.Section3MonicOrthogonal.actualMonicPolynomial_monic
#print axioms LeanPaper.Section3MonicOrthogonal.actualSquaredNorm_positive
