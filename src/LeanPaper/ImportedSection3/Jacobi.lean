import LeanPaper.ImportedSection3.ActualPoleKernel
import LeanPaper.ImportedSection3.SignStructure
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic

/-!
# Theorem 3.8(2): finite-dimensional affine Jacobi formula

This file proves the real derivative and log derivative at the center of
an affine finite matrix pencil, and identifies the actual odd-zeta matrix
pencil with the existing Christoffel-Darboux trace calculation.

**Scope**: the paper's additional Laplace-tau differentiation-under-an-
infinite-integral step remains open. The affine parameter in this file is
not the paper's weight deformation parameter tau. No witness is used here.

Fix6: fix entrywise matrix evaluation at diagonal and off-diagonal slots.
Fix5: explicitly specify `(Polynomial.X : ℝ[X])` both in the determinant
polynomial and in its evaluation bridge to eliminate unresolved coefficient
semiring metavariables. Apply the pinned Mathlib lemma
`Matrix.derivative_det_one_add_X_smul` directly (no manual coefficient cast).
Matrix evaluation uses the polynomial evaluation ring homomorphism and RingHom.map_det.
This version factors the real matrix G+tH directly rather
than manipulating determinants of arbitrary polynomial-valued matrices.
The only polynomial determinant used is det(I+X A), for which Mathlib
already provides the exact derivative-at-zero identity.
-/

noncomputable section
open Matrix Polynomial
namespace PaperAdvances.Theorem3_8_Jacobi

/-- The polynomial determinant for the identity-centered pencil. -/
def unitDetPoly {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : ℝ[X] :=
  Matrix.det ((1 : Matrix (Fin n) (Fin n) ℝ[X]) +
    (Polynomial.X : ℝ[X]) • A.map Polynomial.C)

/-- General finite-dimensional Jacobi coefficient at the identity matrix. -/
theorem unitDetPoly_derivative {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) :
    (Polynomial.derivative (unitDetPoly A)).eval 0 = A.trace := by
  -- This is Mathlib's exact all-dimensions Jacobi derivative at the identity.
  -- The explicit polynomial coefficient ring in `unitDetPoly` resolves `Semiring ?m`.
  exact Matrix.derivative_det_one_add_X_smul A

/-- The polynomial determinant evaluates to the real matrix determinant. -/
theorem unitDetPoly_eval {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (t : ℝ) :
    (unitDetPoly A).eval t = (1 + t • A).det := by
  let P : Matrix (Fin n) (Fin n) ℝ[X] :=
    (1 : Matrix (Fin n) (Fin n) ℝ[X]) +
      (Polynomial.X : ℝ[X]) • A.map Polynomial.C
  have hmat : P.map (Polynomial.evalRingHom t) = 1 + t • A := by
    classical
    ext i j
    -- Separate diagonal/off-diagonal entries so evaluation of the identity
    -- matrix entry reduces definitionally to 1 or 0. Ring normalisation then
    -- closes the remaining scalar commutativity (a * t = t * a).
    by_cases hij : i = j
    · subst j
      simp [P, Matrix.one_apply, Matrix.add_apply,
        Matrix.smul_apply, Matrix.map_apply, smul_eq_mul] <;> ring
    · simp [P, Matrix.one_apply, hij, Matrix.add_apply,
        Matrix.smul_apply, Matrix.map_apply, smul_eq_mul] <;> ring
  have hdet : (Polynomial.evalRingHom t) P.det =
      (P.map (Polynomial.evalRingHom t)).det := by
    exact RingHom.map_det (Polynomial.evalRingHom t) P
  calc
    (unitDetPoly A).eval t = (Polynomial.evalRingHom t) P.det := by rfl
    _ = (P.map (Polynomial.evalRingHom t)).det := hdet
    _ = (1 + t • A).det := congrArg Matrix.det hmat

/-- Identity-centered determinant differentiation in every dimension. -/
theorem unitDet_hasDerivAt {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) :
    HasDerivAt (fun t : ℝ => (1 + t • A).det) A.trace 0 := by
  have hp := (unitDetPoly A).hasDerivAt (0 : ℝ)
  have hcoeff :
      (Polynomial.derivative (unitDetPoly A)).eval (0 : ℝ) = A.trace :=
    unitDetPoly_derivative A
  rw [hcoeff] at hp
  have heq : (fun t : ℝ => (1 + t • A).det) =
      (fun t : ℝ => (unitDetPoly A).eval t) := by
    funext t
    exact (unitDetPoly_eval A t).symm
  rw [heq]
  exact hp

/-- Any nonsingular affine matrix pencil factors over real matrices. -/
theorem affineDet_factor_pointwise {n : ℕ}
    (G H : Matrix (Fin n) (Fin n) ℝ)
    (hG : G.det ≠ 0) (t : ℝ) :
    (G + t • H).det = G.det * (1 + t • (G⁻¹ * H)).det := by
  have hu : IsUnit G.det := isUnit_iff_ne_zero.mpr hG
  have hinv : G * (G⁻¹ * H) = H := by
    rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv G hu, Matrix.one_mul]
  have hfac : G * (1 + t • (G⁻¹ * H)) = G + t • H := by
    calc
      G * (1 + t • (G⁻¹ * H)) = G + t • (G * (G⁻¹ * H)) := by
        rw [Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul]
      _ = G + t • H := by rw [hinv]
  rw [← hfac, Matrix.det_mul]

/-- Jacobi's determinant derivative at the affine pencil center. -/
theorem affineDet_hasDerivAt {n : ℕ}
    (G H : Matrix (Fin n) (Fin n) ℝ)
    (hG : G.det ≠ 0) :
    HasDerivAt (fun t : ℝ => (G + t • H).det)
      (G.det * (G⁻¹ * H).trace) 0 := by
  have heq : (fun t : ℝ => (G + t • H).det) =
      (fun t : ℝ => G.det * (1 + t • (G⁻¹ * H)).det) := by
    funext t
    exact affineDet_factor_pointwise G H hG t
  rw [heq]
  exact (unitDet_hasDerivAt (G⁻¹ * H)).const_mul G.det

/-- Jacobi's logarithmic determinant derivative at the affine pencil center. -/
theorem affineDet_log_hasDerivAt {n : ℕ}
    (G H : Matrix (Fin n) (Fin n) ℝ)
    (hG : 0 < G.det) :
    HasDerivAt (fun t : ℝ => Real.log ((G + t • H).det))
      (G⁻¹ * H).trace 0 := by
  have hn : (G + (0 : ℝ) • H).det ≠ 0 := by
    simpa using (ne_of_gt hG)
  have hh := (affineDet_hasDerivAt G H (ne_of_gt hG)).log hn
  have hdiv : G.det * (G⁻¹ * H).trace /
      (G + (0 : ℝ) • H).det = (G⁻¹ * H).trace := by
    simp only [zero_smul, add_zero]
    field_simp [ne_of_gt hG]
  rw [hdiv] at hh
  exact hh

open ManuscriptChain

/-- The verified odd-zeta Gram and negative-pole trace satisfy finite Jacobi. -/
theorem actual_affine_log_jacobi
    (p : Real.Parameters) (hp : Real.Admissible p) :
    HasDerivAt
      (fun t : ℝ => Real.log
        ((Theorem3_8_Actual.actualGram p + t • Real.derivativeMatrix p).det))
      (Theorem3_8_Kernel.poleOperator
        (Theorem3_8_Actual.actualGram p)
        (Theorem3_8_Actual.actualV p)
        (Theorem3_8_Actual.actualGamma p)).trace 0 := by
  have hg : 0 < (Theorem3_8_Actual.actualGram p).det :=
    Theorem3_3.actual_gram_det_pos p hp
  have hh := affineDet_log_hasDerivAt
    (Theorem3_8_Actual.actualGram p) (Real.derivativeMatrix p) hg
  rw [Theorem3_8_Actual.actual_relative_trace_eq_pole p] at hh
  exact hh

end PaperAdvances.Theorem3_8_Jacobi

#print axioms PaperAdvances.Theorem3_8_Jacobi.unitDetPoly_derivative
#print axioms PaperAdvances.Theorem3_8_Jacobi.unitDetPoly_eval
#print axioms PaperAdvances.Theorem3_8_Jacobi.unitDet_hasDerivAt
#print axioms PaperAdvances.Theorem3_8_Jacobi.affineDet_factor_pointwise
#print axioms PaperAdvances.Theorem3_8_Jacobi.affineDet_hasDerivAt
#print axioms PaperAdvances.Theorem3_8_Jacobi.affineDet_log_hasDerivAt
#print axioms PaperAdvances.Theorem3_8_Jacobi.actual_affine_log_jacobi
