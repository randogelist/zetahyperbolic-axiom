import LeanPaper.BeukersKreinMonomialActual

/-!
# Theorem 5.2(2): finite polynomial-coefficient Beukers form

A polynomial coefficient matrix is the finite bilinear extension of the
actual (already proved) two-variable Beukers monomial moments. This theorem
gives its exact signed Krein mode expansion without assuming a new
analytic representation. This result is a finite-polynomial supporting
claim, not a proof of the theorem's arbitrary-L² extension.
-/

noncomputable section
open scoped BigOperators
open MeasureTheory

namespace ManuscriptChain.Beukers

/-- True finite polynomial coefficient pairing of the *actual* Beukers moments. -/
def polynomialMomentForm {K : ℕ}
    (c d : Fin (K + 1) → ℚ) : ℝ :=
  ∑ r : Fin (K + 1), ∑ t : Fin (K + 1),
    (c r : ℝ) * (d t : ℝ) *
      (∫ z, z.1 ^ r.val * z.2 ^ t.val * density z ∂squareMeasure)

/-- Every rational polynomial coefficient bilinear form is the finite
coefficient extension of the exact, convergent signed Krein modes. -/
theorem polynomialMomentForm_eq_krein {K : ℕ}
    (c d : Fin (K + 1) → ℚ) :
    polynomialMomentForm c d =
      ∑ r : Fin (K + 1), ∑ t : Fin (K + 1),
        (c r : ℝ) * (d t : ℝ) *
          (∑' m : ℕ,
            kreinSignedPairing (kreinChannel r.val m) (kreinChannel t.val m)) := by
  unfold polynomialMomentForm
  simp_rw [actual_monomial_krein_bilinear]

/-- The actual diagonal polynomial coefficient form uses the
same signed infinite modes; no positive-definite cone is asserted. -/
theorem polynomialMomentForm_quadratic {K : ℕ}
    (c : Fin (K + 1) → ℚ) :
    polynomialMomentForm c c =
      ∑ r : Fin (K + 1), ∑ t : Fin (K + 1),
        (c r : ℝ) * (c t : ℝ) *
          (∑' m : ℕ,
            kreinSignedPairing (kreinChannel r.val m) (kreinChannel t.val m)) :=
  polynomialMomentForm_eq_krein c c

end ManuscriptChain.Beukers
