import LeanPaper.Section4ManuscriptBridge
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

/-!
# The actual root-mean identity in Theorem 4.7

The affine determinant is identified with the characteristic polynomial of
`center * I - direction⁻¹ * base`, including its leading coefficient. Comparing
this identity with the already constructed root factorization identifies its
root sum with the matrix trace. The final manuscript endpoint constructs all
spectral data and uses only the original structural admissibility assumptions.
No numerical decay, height, or spectral estimate is introduced as a premise.
-/

noncomputable section
open scoped BigOperators
open Polynomial Matrix ManuscriptChain.Spectral

namespace LeanPaper.Section4RootMean

/-- The matrix whose characteristic roots are the roots of the affine pencil. -/
def rootMatrix {n : ℕ} (p : SymmetricAffinePencil n) : Matrix (Fin n) (Fin n) ℝ :=
  p.center • 1 - p.direction⁻¹ * p.base

/-- Exact characteristic-polynomial identification, with its genuine leading
coefficient, obtained from the actual matrix inverse. -/
theorem detPolynomial_eq_direction_charpoly {n : ℕ} (p : SymmetricAffinePencil n)
    (hD : p.direction.det ≠ 0) :
    p.detPolynomial = C p.direction.det * (rootMatrix p).charpoly := by
  classical
  have hunit : IsUnit p.direction.det := isUnit_iff_ne_zero.mpr hD
  apply Polynomial.funext
  intro x
  have hscalar : Matrix.scalar (Fin n) x = x • (1 : Matrix (Fin n) (Fin n) ℝ) := by
    ext i j
    by_cases hij : i = j <;> simp [Matrix.scalar_apply, Matrix.diagonal, hij]
  have hmatrix : p.direction * (Matrix.scalar (Fin n) x - rootMatrix p) =
      p.matrixAt x := by
    rw [hscalar]
    simp only [rootMatrix, Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one,
      ← Matrix.mul_assoc, Matrix.mul_nonsing_inv p.direction hunit, Matrix.one_mul,
      SymmetricAffinePencil.matrixAt, sub_smul]
    abel
  calc
    p.detPolynomial.eval x = (p.matrixAt x).det := p.eval_detPolynomial x
    _ = p.direction.det * (Matrix.scalar (Fin n) x - rootMatrix p).det := by
      rw [← hmatrix, Matrix.det_mul]
    _ = (C p.direction.det * (rootMatrix p).charpoly).eval x := by
      rw [Polynomial.eval_mul, Polynomial.eval_C, Matrix.eval_charpoly]

private theorem factorization_linear_product {n : ℕ} {p : SymmetricAffinePencil n}
    (c : RootFactorization p) :
    p.detPolynomial = C (p.base.det * ∏ i, c.beta i) *
      ∏ i, (X - C (c.root i)) := by
  classical
  have hlinear (i : Fin n) : spectralFactor p.center (c.beta i) =
      C (c.beta i) * (X - C (c.root i)) := by
    apply Polynomial.funext
    intro x
    simp only [eval_spectralFactor, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_sub, Polynomial.eval_X, RootFactorization.root]
    field_simp [c.beta_ne_zero i] <;> ring
  rw [c.factorization]
  simp_rw [hlinear]
  rw [Finset.prod_mul_distrib, ← map_prod, ← mul_assoc, ← map_mul]

/-- The characteristic polynomial is the product over the actual spectral
root vector, with multiplicities preserved and no root-sum assumption. -/
theorem rootMatrix_charpoly_eq_product {n : ℕ} {p : SymmetricAffinePencil n}
    (c : RootFactorization p) (hD : p.direction.det ≠ 0) :
    (rootMatrix p).charpoly = ∏ i, (X - C (c.root i)) := by
  classical
  have hchar := detPolynomial_eq_direction_charpoly p hD
  have hfac := factorization_linear_product c
  have hmonic : (∏ i, (X - C (c.root i))).Monic :=
    Polynomial.monic_prod_of_monic Finset.univ _ (fun _ _ => Polynomial.monic_X_sub_C _)
  have hlead : p.direction.det = p.base.det * ∏ i, c.beta i := by
    have h := congrArg Polynomial.leadingCoeff (hchar.symm.trans hfac)
    simpa only [(rootMatrix p).charpoly_monic.leadingCoeff_C_mul,
      hmonic.leadingCoeff_C_mul] using h
  apply mul_left_cancel₀ (show C p.direction.det ≠ 0 from Polynomial.C_ne_zero.mpr hD)
  calc
    C p.direction.det * (rootMatrix p).charpoly = p.detPolynomial := hchar.symm
    _ = C (p.base.det * ∏ i, c.beta i) * ∏ i, (X - C (c.root i)) := hfac
    _ = C p.direction.det * ∏ i, (X - C (c.root i)) := by rw [← hlead]

/-- The full root vector of the affine determinant has the trace predicted
by its actual base and direction matrices. -/
theorem root_sum_sub_center_eq_neg_trace {n : ℕ} {p : SymmetricAffinePencil n}
    (c : RootFactorization p) (hD : p.direction.det ≠ 0) :
    (∑ i, (c.root i - p.center)) = -(p.direction⁻¹ * p.base).trace := by
  classical
  have hnext : (∏ i : Fin n, (X - C (c.root i))).nextCoeff = -∑ i, c.root i := by
    simpa using Polynomial.prod_X_sub_C_nextCoeff (s := Finset.univ) c.root
  have hsum : (∑ i, c.root i) = (rootMatrix p).trace := by
    have ht := Matrix.trace_eq_neg_charpoly_nextCoeff (rootMatrix p)
    rw [rootMatrix_charpoly_eq_product c hD, hnext, neg_neg] at ht
    exact ht.symm
  rw [Finset.sum_sub_distrib, hsum]
  simp only [rootMatrix, Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_one,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, smul_eq_mul]
  ring

open ManuscriptChain

/-- The arithmetic mean formula printed in Theorem 4.7 for the actual
manuscript roots. Positivity and direction nonsingularity are already proved. -/
theorem manuscript_root_mean (p : Real.Parameters) (hp : Real.Admissible p) :
    (∑ i : Fin p.h, (General.factorization p (GRAM_POSITIVE p hp)).root i) /
        (p.h : ℝ) - Real.zeta p.weight =
      -((Real.derivativeMatrix p)⁻¹ * Real.gram p (Real.zeta p.weight)).trace /
        (p.h : ℝ) := by
  have hh : (p.h : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.sub_pos_of_lt hp.N_lt_K).ne'
  have hs := root_sum_sub_center_eq_neg_trace
    (General.factorization p (GRAM_POSITIVE p hp)) (General.derivative_nonsingular p)
  have hsum : (∑ i : Fin p.h, (General.factorization p (GRAM_POSITIVE p hp)).root i) -
      (p.h : ℝ) * Real.zeta p.weight =
      -((Real.derivativeMatrix p)⁻¹ * Real.gram p (Real.zeta p.weight)).trace := by
    simpa only [Finset.sum_sub_distrib, Real.manuscriptPencil_center,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using hs
  change (∑ i : Fin p.h, (General.factorization p (GRAM_POSITIVE p hp)).root i) /
      (p.h : ℝ) - Real.zeta p.weight =
    -((Real.derivativeMatrix p)⁻¹ * Real.gram p (Real.zeta p.weight)).trace / (p.h : ℝ)
  calc
    _ = ((∑ i : Fin p.h, (General.factorization p (GRAM_POSITIVE p hp)).root i) -
        (p.h : ℝ) * Real.zeta p.weight) / (p.h : ℝ) := by field_simp [hh]
    _ = _ := by rw [hsum]

end LeanPaper.Section4RootMean

#print axioms LeanPaper.Section4RootMean.detPolynomial_eq_direction_charpoly
#print axioms LeanPaper.Section4RootMean.rootMatrix_charpoly_eq_product
#print axioms LeanPaper.Section4RootMean.root_sum_sub_center_eq_neg_trace
#print axioms LeanPaper.Section4RootMean.manuscript_root_mean
