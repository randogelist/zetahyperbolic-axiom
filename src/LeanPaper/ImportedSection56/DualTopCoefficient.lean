import LeanPaper.ImportedSection56.DualPencilCCT

/-!
# Theorem 5.2 — exact X-degree and leading coefficient of dual Beukers pencil

The coefficient [X^h] is det(CCᵀ), with no analytic or number-theoretic input.
The polynomial degree is at most h. The monomial basis is the identity
coefficient matrix and gives a MONIC degree-h dual pencil.
-/

noncomputable section
open scoped BigOperators
open Polynomial
namespace PaperOrder.CoreAlgebra
open ManuscriptChain.Real

/-- General leading coefficient, including linearly dependent coefficient
rows (where the top coefficient is zero). -/
theorem dualDelta_coefficient_dimension {h K : ℕ} (s : ℕ)
    (c : Fin h → Fin (K + 1) → ℚ) :
    (dualDelta s c).coeff h = (dualSlopeMatrix c).det := by
  unfold dualDelta
  rw [dualPencil_decomposition]
  simpa using Polynomial.coeff_det_X_add_C_card
    (dualSlopeMatrix c) (dualConstantMatrix s c)

/-- The universal degree cap requires no nonsingularity assumption. -/
theorem dualDelta_natDegree_le {h K : ℕ} (s : ℕ)
    (c : Fin h → Fin (K + 1) → ℚ) :
    (dualDelta s c).natDegree ≤ h := by
  unfold dualDelta
  rw [dualPencil_decomposition]
  simpa using Polynomial.natDegree_det_X_add_C_le
    (dualSlopeMatrix c) (dualConstantMatrix s c)

/-- The first `h` monomials in `ℚ[x]` of degree at most `h` form a
coordinate-selected basis. The final coefficient column is zero.
Using a padded `(h+1)`-column matrix avoids the false definitional equality
`h - 1 + 1 = h` at `h = 0` and works uniformly in every dimension. -/
def dualMonomialCoefficients (h : ℕ) : Fin h → Fin (h + 1) → ℚ :=
  fun i r => if i.castSucc = r then 1 else 0

/-- The derivative of the dual monomial pencil is exactly the identity,
including the dimension-zero case. This is a finite coefficient identity;
no irrationality witness or analytic estimate is required. -/
theorem dualMonomialSlope_eq_one (h : ℕ) :
    dualSlopeMatrix (K := h) (dualMonomialCoefficients h) = 1 := by
  classical
  ext i j
  -- Evaluate the coefficient Gram sum at its sole possibly nonzero column.
  have hsum :
      (∑ r : Fin (h + 1),
        (if (Fin.castSucc i : Fin (h + 1)) = r then (1 : ℚ) else 0) *
        (if (Fin.castSucc j : Fin (h + 1)) = r then (1 : ℚ) else 0)) =
      (if (Fin.castSucc j : Fin (h + 1)) = Fin.castSucc i
        then (1 : ℚ) else 0) := by
    have hsingle :
        (∑ r : Fin (h + 1),
          (if (Fin.castSucc i : Fin (h + 1)) = r then (1 : ℚ) else 0) *
          (if (Fin.castSucc j : Fin (h + 1)) = r then (1 : ℚ) else 0)) =
        (if (Fin.castSucc i : Fin (h + 1)) = Fin.castSucc i
           then (1 : ℚ) else 0) *
        (if (Fin.castSucc j : Fin (h + 1)) = Fin.castSucc i
           then (1 : ℚ) else 0) := by
      apply Finset.sum_eq_single (Fin.castSucc i)
      · intro r _ hr
        have hne : (Fin.castSucc i : Fin (h + 1)) ≠ r := Ne.symm hr
        simp [hne]
      · simp
    simpa using hsingle
  calc
    (dualSlopeMatrix (K := h) (dualMonomialCoefficients h)) i j =
        ∑ r : Fin (h + 1),
          (if (Fin.castSucc i : Fin (h + 1)) = r then (1 : ℚ) else 0) *
          (if (Fin.castSucc j : Fin (h + 1)) = r then (1 : ℚ) else 0) := rfl
    _ = (if (Fin.castSucc j : Fin (h + 1)) = Fin.castSucc i
          then (1 : ℚ) else 0) := hsum
    _ = (1 : Matrix (Fin h) (Fin h) ℚ) i j := by
      by_cases hij : i = j
      · subst j
        simp
      · have hcast : (Fin.castSucc j : Fin (h + 1)) ≠ Fin.castSucc i := by
          intro hc
          have hval : i.val = j.val := by
            have hv : (Fin.castSucc i : Fin (h + 1)).val =
                (Fin.castSucc j : Fin (h + 1)).val :=
              congrArg (fun k : Fin (h + 1) => k.val) hc.symm
            exact hv
          exact hij (Fin.ext hval)
        simp [Matrix.one_apply, hij, hcast]

end PaperOrder.CoreAlgebra

#print axioms PaperOrder.CoreAlgebra.dualDelta_coefficient_dimension
#print axioms PaperOrder.CoreAlgebra.dualDelta_natDegree_le
