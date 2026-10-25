import LeanPaper.ImportedSection4.Proposition_4_3_IsometricExtension
import Mathlib.NumberTheory.Padics.Complex
import Mathlib.Tactic

/-!
# Proposition 4.3: the complex p-adic zero-free disk

This extends the compiler-verified Q_p result to the algebraically
closed completed field C_p, with an arbitrary p-adic integral center.
The argument uses Mathlib's isometric inclusion Q_p -> C_p and the
proved universal ultrametric isometric-extension theorem. The radius
and the evaluated polynomial are the exact embedded p-adic quantities.

Neither a numerical witness nor an irrationality assumption is used.
-/

noncomputable section
open Polynomial

namespace PaperAdvances.Proposition4_3_ComplexPadicDisk

/-- For every integral p-adic polynomial, nonzero value at an integral
center gives a full complex-p-adic open disk free of zeros, with
exact preservation of the center's p-adic norm. -/
theorem PROPOSITION_4_3_INTEGRAL_COMPLEX_PADIC
    {p : ℕ} [Fact p.Prime]
    (Q : (ℤ_[p])[X]) (ξ : ℤ_[p]) (α : ℂ_[p])
    (hQ : Q.eval ξ ≠ 0)
    (hα : ‖α - ((ξ : ℚ_[p]) : ℂ_[p])‖ <
      ‖((Q.eval ξ : ℤ_[p]) : ℚ_[p])‖) :
    ‖((Q.map (PadicInt.Coe.ringHom)).map
        (algebraMap ℚ_[p] ℂ_[p])).eval α‖ =
      ‖((Q.eval ξ : ℤ_[p]) : ℚ_[p])‖ ∧
    ((Q.map (PadicInt.Coe.ringHom)).map
      (algebraMap ℚ_[p] ℂ_[p])).eval α ≠ 0 := by
  let φ : ℚ_[p] →+* ℂ_[p] := algebraMap ℚ_[p] ℂ_[p]
  have hφ : ∀ y : ℚ_[p], ‖φ y‖ = ‖y‖ := by
    intro y
    change ‖(y : ℂ_[p])‖ = ‖y‖
    exact PadicComplex.norm_extends' p y
  -- Coercion `ℚ_[p] → ℂ_[p]` is the composite of the canonical
  -- embeddings through `PadicAlgCl p`. Identify it with the tower's
  -- algebraMap explicitly; it is not syntax-identical to `φ` in `hα`.
  have hcenter : ((ξ : ℚ_[p]) : ℂ_[p]) = φ (ξ : ℚ_[p]) := by
    change
      (algebraMap (PadicAlgCl p) (ℂ_[p]))
        ((algebraMap ℚ_[p] (PadicAlgCl p)) (ξ : ℚ_[p])) =
      (algebraMap ℚ_[p] ℂ_[p]) (ξ : ℚ_[p])
    exact (IsScalarTower.algebraMap_apply
      ℚ_[p] (PadicAlgCl p) ℂ_[p] (ξ : ℚ_[p])).symm
  have hball : ‖α - φ (ξ : ℚ_[p])‖ <
      ‖((Q.eval ξ : ℤ_[p]) : ℚ_[p])‖ := by
    rw [hcenter] at hα
    exact hα
  exact PaperAdvances.Proposition4_3_IsometricExtension.PROPOSITION_4_3_INTEGRAL_ISOMETRIC_EXTENSION
    φ hφ Q ξ α hQ hball

/-- The integer-coefficient manuscript version for every root search
point in C_p, not only in the rational p-adic subfield. -/
theorem PROPOSITION_4_3_INTEGER_COMPLEX_PADIC
    {p : ℕ} [Fact p.Prime]
    (Q : ℤ[X]) (ξ : ℤ_[p]) (α : ℂ_[p])
    (hQ : (Q.map (Int.castRingHom (ℤ_[p]))).eval ξ ≠ 0)
    (hα : ‖α - ((ξ : ℚ_[p]) : ℂ_[p])‖ <
      ‖(((Q.map (Int.castRingHom (ℤ_[p]))).eval ξ : ℤ_[p]) : ℚ_[p])‖) :
    ‖(((Q.map (Int.castRingHom (ℤ_[p]))).map
      (PadicInt.Coe.ringHom)).map
      (algebraMap ℚ_[p] ℂ_[p])).eval α‖ =
      ‖(((Q.map (Int.castRingHom (ℤ_[p]))).eval ξ : ℤ_[p]) : ℚ_[p])‖ ∧
    (((Q.map (Int.castRingHom (ℤ_[p]))).map
      (PadicInt.Coe.ringHom)).map
      (algebraMap ℚ_[p] ℂ_[p])).eval α ≠ 0 := by
  exact PROPOSITION_4_3_INTEGRAL_COMPLEX_PADIC
    (Q.map (Int.castRingHom (ℤ_[p]))) ξ α hQ hα

end PaperAdvances.Proposition4_3_ComplexPadicDisk

#print axioms PaperAdvances.Proposition4_3_ComplexPadicDisk.PROPOSITION_4_3_INTEGRAL_COMPLEX_PADIC
#print axioms PaperAdvances.Proposition4_3_ComplexPadicDisk.PROPOSITION_4_3_INTEGER_COMPLEX_PADIC
