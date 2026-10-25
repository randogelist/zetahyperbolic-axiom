import LeanPaper.ImportedSection56.PositiveSlopeSpectrum
import LeanPaper.ImportedSection56.SelectedMonomial

/-!
# The actual rational dual determinant has a real spectrum

The archived positive-slope construction is identified with `Real.dualDelta`,
not merely with an unrelated symmetric matrix. Real row separation is exactly
the finite coefficient independence hypothesis. For selected distinct monomials
the separation is proved explicitly. No Beukers integral representation,
infinite-dimensional Krein cone, or arithmetic estimate is inferred.
-/

noncomputable section
open scoped BigOperators
open Polynomial
open ManuscriptChain PaperOrder.CoreAlgebra PaperOrder.PrincipalTheorems

namespace LeanPaper.Section5DualSpectrum

def realCoefficients {h K : ℕ} (c : Fin h → Fin (K + 1) → ℚ) :
    Fin h → Fin (K + 1) → ℝ := fun i r => (c i r : ℝ)

def actualDualPencil {h K : ℕ} (s : ℕ) (c : Fin h → Fin (K + 1) → ℚ)
    (hc : coefficientRowsSeparate (realCoefficients c)) : PositiveSlopePencil h where
  constant := (dualConstantMatrix s c).map (fun q : ℚ => (q : ℝ))
  slope := coefficientSlope (realCoefficients c)
  constant_symmetric := (dualConstantMatrix_symmetric s c).map _
  slope_posDef := coefficientSlope_posDef _ hc

theorem actualDualPencil_polynomialMatrix {h K : ℕ} (s : ℕ)
    (c : Fin h → Fin (K + 1) → ℚ)
    (hc : coefficientRowsSeparate (realCoefficients c)) :
    (actualDualPencil s c hc).polynomialMatrix =
      (fun i j => (Polynomial.mapRingHom (Rat.castHom ℝ)) (Real.dualEntry s c i j)) := by
  funext i j
  change C ((dualConstantMatrix s c i j : ℚ) : ℝ) +
      X * C (∑ r, (c i r : ℝ) * (c j r : ℝ)) =
    (C (dualConstantMatrix s c i j) + C (dualSlopeMatrix c i j) * X).map
      (Rat.castHom ℝ)
  rw [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C,
    Polynomial.map_C, Polynomial.map_X]
  simp only [dualSlopeMatrix, map_sum, map_mul, Rat.coe_castHom]
  ring

theorem actualDualPencil_detPolynomial {h K : ℕ} (s : ℕ)
    (c : Fin h → Fin (K + 1) → ℚ)
    (hc : coefficientRowsSeparate (realCoefficients c)) :
    (actualDualPencil s c hc).detPolynomial =
      Real.realPolynomial (Real.dualDelta s c) := by
  unfold PositiveSlopePencil.detPolynomial
  rw [actualDualPencil_polynomialMatrix]
  exact ((Polynomial.mapRingHom (Rat.castHom ℝ)).map_det
    (fun i j => Real.dualEntry s c i j)).symm

/-- Exact full degree of the actual rational determinant under real row independence. -/
theorem actual_dual_degree {h K : ℕ} (s : ℕ)
    (c : Fin h → Fin (K + 1) → ℚ)
    (hc : coefficientRowsSeparate (realCoefficients c)) :
    (Real.dualDelta s c).natDegree = h := by
  have hd := positiveSlopePencil_degree (actualDualPencil s c hc)
  rw [actualDualPencil_detPolynomial, Real.realPolynomial, Polynomial.natDegree_map] at hd
  exact hd

/-- Every complex zero of the actual rational dual determinant is real. -/
theorem actual_dual_zeros_real {h K : ℕ} (s : ℕ)
    (c : Fin h → Fin (K + 1) → ℚ)
    (hc : coefficientRowsSeparate (realCoefficients c)) (z : ℂ)
    (hz : Polynomial.eval₂ (algebraMap ℚ ℂ) z (Real.dualDelta s c) = 0) :
    z.im = 0 := by
  apply positiveSlopePencil_every_complex_root_real (actualDualPencil s c hc) z
  rw [actualDualPencil_detPolynomial, Real.realPolynomial, Polynomial.eval₂_map]
  rw [Subsingleton.elim ((algebraMap ℝ ℂ).comp (Rat.castHom ℝ))
    (algebraMap ℚ ℂ)]
  exact hz

theorem selected_monomial_rows_separate {h K : ℕ}
    (f : Fin h → Fin (K + 1)) (hf : Function.Injective f) :
    coefficientRowsSeparate (realCoefficients (dualSelectedMonomialCoefficients f)) := by
  intro v hv
  have hex : ∃ i, v i ≠ 0 := by
    by_contra hn
    push_neg at hn
    exact hv (funext hn)
  obtain ⟨i, hi⟩ := hex
  refine ⟨f i, ?_⟩
  simpa [realCoefficients, dualSelectedMonomialCoefficients, hf.eq_iff, apply_ite, mul_ite] using hi

/-- Distinct selected monomials supply the coefficient hypothesis constructively. -/
theorem selected_monomial_dual_zeros_real {h K : ℕ} (s : ℕ)
    (f : Fin h → Fin (K + 1)) (hf : Function.Injective f) (z : ℂ)
    (hz : Polynomial.eval₂ (algebraMap ℚ ℂ) z
      (Real.dualDelta s (dualSelectedMonomialCoefficients f)) = 0) :
    z.im = 0 :=
  actual_dual_zeros_real s _ (selected_monomial_rows_separate f hf) z hz

end LeanPaper.Section5DualSpectrum
