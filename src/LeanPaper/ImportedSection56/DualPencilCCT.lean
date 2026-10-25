import LeanPaper.ImportedSection56.DualAffineAlgebra

/-!
# Theorem 5.2 — exact positive-slope coefficient matrix architecture

For every matrix of rational polynomial coefficients C, the slope is CCᵀ.
This is the main finite algebraic observation behind Theorem 5.2. Positive
definiteness for linearly independent coefficient rows is a separate
linear-algebra consequence, not inserted as an unproved hypothesis here.
-/

noncomputable section
open scoped BigOperators
open Polynomial
namespace PaperOrder.CoreAlgebra
open ManuscriptChain.Real

/-- Exact coefficient matrix; rows index selected polynomials, columns
index their monomial coefficients. -/
def dualCoefficientMatrix {h K : ℕ}
    (c : Fin h → Fin (K + 1) → ℚ) :
    Matrix (Fin h) (Fin (K + 1)) ℚ := fun i r => c i r

/-- The X-slope of the true rational dual pencil is exactly CCᵀ. -/
theorem dualSlopeMatrix_eq_CCT {h K : ℕ}
    (c : Fin h → Fin (K + 1) → ℚ) :
    dualSlopeMatrix c =
      dualCoefficientMatrix c * (dualCoefficientMatrix c).transpose := by
  ext i j
  simp only [dualSlopeMatrix, dualCoefficientMatrix,
    Matrix.mul_apply, Matrix.transpose_apply]

/-- Constant/slope decomposition at the level of the WHOLE dual matrix. -/
theorem dualPencil_decomposition {h K : ℕ} (s : ℕ)
    (c : Fin h → Fin (K + 1) → ℚ) :
    (fun i j => dualEntry s c i j : Matrix (Fin h) (Fin h) (Polynomial ℚ)) =
      (X : Polynomial ℚ) • (dualSlopeMatrix c).map C +
        (dualConstantMatrix s c).map C := by
  ext i j
  rw [dualEntry_affine]
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul]
  ring

/-- Symmetric matrices are not only a feature of the slope: the harmonic
constant matrix is symmetric by the exact divided-difference cancellation. -/
theorem dualConstantMatrix_symmetric {h K : ℕ} (s : ℕ)
    (c : Fin h → Fin (K + 1) → ℚ) :
    (dualConstantMatrix s c).IsSymm := by
  classical
  -- Establish the entrywise symmetry first.  In the `IsSymm` goal,
  -- Matrix.transpose reverses the two matrix indices.
  have hsym (i j : Fin h) :
      dualConstantMatrix s c i j = dualConstantMatrix s c j i := by
    change (∑ r, ∑ t, c i r * c j t * dualConstant s r.val t.val) =
      (∑ r, ∑ t, c j r * c i t * dualConstant s r.val t.val)
    calc
      (∑ r, ∑ t, c i r * c j t * dualConstant s r.val t.val) =
          ∑ t, ∑ r, c i r * c j t * dualConstant s r.val t.val :=
            Finset.sum_comm
      _ = ∑ t, ∑ r, c j t * c i r * dualConstant s t.val r.val := by
        apply Finset.sum_congr rfl
        intro t ht
        apply Finset.sum_congr rfl
        intro r hr
        rw [dualConstant_swap s r.val t.val]
        ring
      _ = ∑ r, ∑ t, c j r * c i t * dualConstant s r.val t.val := rfl
  ext i j
  simpa only [Matrix.transpose_apply] using (hsym j i)

end PaperOrder.CoreAlgebra

#print axioms PaperOrder.CoreAlgebra.dualSlopeMatrix_eq_CCT
#print axioms PaperOrder.CoreAlgebra.dualPencil_decomposition
#print axioms PaperOrder.CoreAlgebra.dualConstantMatrix_symmetric
