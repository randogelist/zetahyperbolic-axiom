import Theorem_2_4_Canonical_Basis_Invariance
import Mathlib.RingTheory.Polynomial.DegreeLT
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.LinearAlgebra.Basis.Bilinear
import Mathlib.LinearAlgebra.Determinant

/-!
# Canonical basis invariance for rational-function evaluations

This module supplies the functional-to-matrix bridge in manuscript Theorem 2.4.
The functional is arbitrary and the two polynomial families are genuine bases
of the degree-bounded polynomial space. Their change matrices are constructed;
invertibility is proved from the basis axioms, rather than supplied as an extra
hypothesis. The retained primitive normalization then gives the printed sign
ambiguity for every nonzero determinant.
-/

noncomputable section
open scoped BigOperators
open Polynomial Module

namespace LeanPaper.Section2FunctionalBasis

open ManuscriptChain.BasisInvariance

variable {h : ℕ} {V : Type*} [AddCommGroup V] [Module ℚ V]

def basisMatrix (L : V →ₗ[ℚ] V →ₗ[ℚ] ℚ[X])
    (A B : Basis (Fin h) ℚ V) : Matrix (Fin h) (Fin h) ℚ[X] :=
  fun i j => L (A i) (B j)

def rowChange (e A : Basis (Fin h) ℚ V) : Matrix (Fin h) (Fin h) ℚ :=
  (e.toMatrix A).transpose

theorem rowChange_det_ne_zero (e A : Basis (Fin h) ℚ V) :
    Matrix.det (rowChange e A) ≠ 0 := by
  simpa [rowChange, Module.Basis.det_apply] using (e.isUnit_det A).ne_zero

theorem basisMatrix_changeBasis (L : V →ₗ[ℚ] V →ₗ[ℚ] ℚ[X])
    (e A B : Basis (Fin h) ℚ V) :
    basisMatrix L A B =
      changeBasisPencil (basisMatrix L e e) (rowChange e A) (rowChange e B) := by
  funext i j
  rw [changeBasisPencil_apply]
  change L (A i) (B j) = _
  calc
    L (A i) (B j) = ∑ r, (e.repr (A i)) r • L (e r) (B j) := by
      conv_lhs => rw [← e.sum_repr (A i)]
      simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro r _
      conv_lhs => rw [← e.sum_repr (B j)]
      simp only [map_sum, map_smul, Finset.smul_sum, smul_smul]
      apply Finset.sum_congr rfl
      intro s _
      simp [rowChange, basisMatrix, Module.Basis.toMatrix_apply, Algebra.smul_def]

theorem det_basisMatrix (L : V →ₗ[ℚ] V →ₗ[ℚ] ℚ[X])
    (e A B : Basis (Fin h) ℚ V) :
    Matrix.det (basisMatrix L A B) =
      C (Matrix.det (rowChange e A) * Matrix.det (rowChange e B)) *
        Matrix.det (basisMatrix L e e) := by
  rw [basisMatrix_changeBasis L e A B, det_changeBasisPencil]

theorem det_basisMatrix_ne_zero (L : V →ₗ[ℚ] V →ₗ[ℚ] ℚ[X])
    (e A B : Basis (Fin h) ℚ V) (he : Matrix.det (basisMatrix L e e) ≠ 0) :
    Matrix.det (basisMatrix L A B) ≠ 0 := by
  rw [det_basisMatrix L e A B]
  apply mul_ne_zero
  · simpa only [ne_eq, C_eq_zero] using
      (mul_ne_zero (rowChange_det_ne_zero e A) (rowChange_det_ne_zero e B))
  · exact he

/-- The actual inclusion of degree-bounded polynomials in the rational-function field. -/
def polynomialEmbedding (h : ℕ) : degreeLT ℚ h →ₗ[ℚ] RatFunc ℚ :=
  (IsScalarTower.toAlgHom ℚ ℚ[X] (RatFunc ℚ)).toLinearMap.comp
    (degreeLT ℚ h).subtype

/-- The bilinear functional evaluation with fixed rational-function weight. -/
def weightedPairing (μ : RatFunc ℚ →ₗ[ℚ] ℚ[X]) (w : RatFunc ℚ) (h : ℕ) :
    degreeLT ℚ h →ₗ[ℚ] degreeLT ℚ h →ₗ[ℚ] ℚ[X] where
  toFun P := {
    toFun := fun Q => μ (w * polynomialEmbedding h P * polynomialEmbedding h Q)
    map_add' := by intros; simp [map_add, mul_add]
    map_smul' := by intros; simp [map_smul] }
  map_add' := by intros; ext; simp [map_add, mul_add, add_mul]
  map_smul' := by intros; ext; simp [map_smul]

/-- The matrix printed in Theorem 2.4, for arbitrary numerator and denominator. -/
def functionalMatrix (μ : RatFunc ℚ →ₗ[ℚ] ℚ[X]) (W D : ℚ[X])
    (A B : Basis (Fin h) ℚ (degreeLT ℚ h)) : Matrix (Fin h) (Fin h) ℚ[X] :=
  basisMatrix (weightedPairing μ
    (algebraMap ℚ[X] (RatFunc ℚ) W / algebraMap ℚ[X] (RatFunc ℚ) D) h) A B

theorem functionalMatrix_apply (μ : RatFunc ℚ →ₗ[ℚ] ℚ[X]) (W D : ℚ[X])
    (A B : Basis (Fin h) ℚ (degreeLT ℚ h)) (i j : Fin h) :
    functionalMatrix μ W D A B i j =
      μ (algebraMap ℚ[X] (RatFunc ℚ) (W * (A i : ℚ[X]) * (B j : ℚ[X])) /
        algebraMap ℚ[X] (RatFunc ℚ) D) := by
  simp only [functionalMatrix, basisMatrix, weightedPairing, LinearMap.coe_mk,
    AddHom.coe_mk, polynomialEmbedding, LinearMap.comp_apply,
    AlgHom.toLinearMap_apply, IsScalarTower.coe_toAlgHom', Submodule.subtype_apply, map_mul]
  congr 1
  ring

/-- Full functional/basis version of manuscript Theorem 2.4. Both primitive
normalizations are constructed from the sole nonzero-determinant hypothesis. -/
theorem theorem_2_4 (μ : RatFunc ℚ →ₗ[ℚ] ℚ[X]) (W D : ℚ[X])
    (A B : Basis (Fin h) ℚ (degreeLT ℚ h))
    (hdet : Matrix.det (functionalMatrix μ W D (degreeLT.basis ℚ h)
      (degreeLT.basis ℚ h)) ≠ 0) :
    let f := Matrix.det (functionalMatrix μ W D (degreeLT.basis ℚ h)
      (degreeLT.basis ℚ h))
    let g := Matrix.det (functionalMatrix μ W D A B)
    ∃ hg : g ≠ 0,
      (primitiveNormalization g hg).polynomial =
          (primitiveNormalization f hdet).polynomial ∨
        (primitiveNormalization g hg).polynomial =
          -(primitiveNormalization f hdet).polynomial := by
  let e := degreeLT.basis ℚ h
  let L := weightedPairing μ
    (algebraMap ℚ[X] (RatFunc ℚ) W / algebraMap ℚ[X] (RatFunc ℚ) D) h
  have hg := det_basisMatrix_ne_zero L e A B hdet
  refine ⟨hg, ?_⟩
  exact primitiveNormalization_scalar_invariance _ _
    (mul_ne_zero (rowChange_det_ne_zero e A) (rowChange_det_ne_zero e B))
    (det_basisMatrix L e A B)

end LeanPaper.Section2FunctionalBasis
