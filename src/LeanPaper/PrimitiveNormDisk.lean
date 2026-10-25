import LeanPaper.OperatorNormDisk
import MAIN_CHAIN_IRRATIONALITY

/-!
# Theorem 3.1 for the actual primitive integer polynomial

A proved nonzero rational scaling transports complex roots from the actual
primitive integer normalization to the determinant. The assembled endpoint
contains degree, positivity at the actual zeta value, reality of every complex
root, and the exact Euclidean operator-norm disk, including a boundary root.
Only the manuscript's structural admissibility conditions are hypotheses.
-/

noncomputable section
open scoped Matrix.Norms.L2Operator
open Polynomial
open ManuscriptChain
open LeanPaper.OperatorNormDisk

namespace LeanPaper.PrimitiveNormDisk

/-- Positive primitive normalization preserves evaluation up to its proved scale. -/
theorem normalization_eval_complex {f : ℚ[X]}
    (nf : BasisInvariance.PrimitiveNormalization f) (z : ℂ) :
    nf.polynomial.eval₂ (algebraMap ℤ ℂ) z =
      (nf.scale : ℂ) * f.eval₂ (algebraMap ℚ ℂ) z := by
  have hcomp : (algebraMap ℚ ℂ).comp (Int.castRingHom ℚ) = algebraMap ℤ ℂ := by
    ext n
    simp
  calc
    nf.polynomial.eval₂ (algebraMap ℤ ℂ) z =
        (nf.polynomial.map (Int.castRingHom ℚ)).eval₂ (algebraMap ℚ ℂ) z := by
      rw [Polynomial.eval₂_map, hcomp]
    _ = (nf.scale : ℂ) * f.eval₂ (algebraMap ℚ ℂ) z := by
      rw [nf.identity, Polynomial.eval₂_mul, Polynomial.eval₂_C]
      rfl

/-- No additional factorization or root certificate is needed for this transport. -/
theorem normalization_complex_root_iff {f : ℚ[X]}
    (nf : BasisInvariance.PrimitiveNormalization f) (z : ℂ) :
    nf.polynomial.eval₂ (algebraMap ℤ ℂ) z = 0 ↔
      f.eval₂ (algebraMap ℚ ℂ) z = 0 := by
  have hscale : (nf.scale : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt nf.scale_pos
  rw [normalization_eval_complex]
  simp only [mul_eq_zero, hscale, false_or]

theorem primitive_complex_root_iff (p : Real.Parameters) (z : ℂ) :
    (GeneralIrrationality.primitivePolynomial p).eval₂ (algebraMap ℤ ℂ) z = 0 ↔
      General.ComplexRoot p z :=
  normalization_complex_root_iff (GeneralIrrationality.normalization p) z

/-- Every complex zero of the actual primitive integer polynomial satisfies the
literal inverse-operator-norm bound. -/
theorem primitive_root_distance (p : Real.Parameters) (hp : Real.Admissible p)
    (z : ℂ)
    (hz : (GeneralIrrationality.primitivePolynomial p).eval₂ (algebraMap ℤ ℂ) z = 0) :
    1 / ‖whitened (Real.manuscriptPencil p)‖ ≤
      ‖z - (Real.zeta p.weight : ℂ)‖ :=
  actual_root_distance p hp z ((primitive_complex_root_iff p z).mp hz)

/-- The primitive polynomial and determinant have the same exact norm disk. -/
theorem primitive_exact_norm_disk (p : Real.Parameters) (hp : Real.Admissible p) :
    0 < 1 / ‖whitened (Real.manuscriptPencil p)‖ ∧
    (∀ z : ℂ, ‖z - (Real.zeta p.weight : ℂ)‖ <
      1 / ‖whitened (Real.manuscriptPencil p)‖ →
        (GeneralIrrationality.primitivePolynomial p).eval₂ (algebraMap ℤ ℂ) z ≠ 0) ∧
    (∃ z : ℂ,
      (GeneralIrrationality.primitivePolynomial p).eval₂ (algebraMap ℤ ℂ) z = 0 ∧
      ‖z - (Real.zeta p.weight : ℂ)‖ = 1 / ‖whitened (Real.manuscriptPencil p)‖) := by
  obtain ⟨hpos, hfree, z, hz, hd⟩ := actual_exact_norm_disk p hp
  refine ⟨hpos, ?_, z, (primitive_complex_root_iff p z).mpr hz, hd⟩
  intro w hw hroot
  exact hfree w hw ((primitive_complex_root_iff p w).mp hroot)

/-- Assembled primitive-integer endpoint of Theorem 3.1, with actual zeta center
and no unproved positivity or spectral premise. Roots may have multiplicity. -/
theorem primitive_theorem_3_1 (p : Real.Parameters) (hp : Real.Admissible p) :
    (GeneralIrrationality.primitivePolynomial p).IsPrimitive ∧
    (GeneralIrrationality.primitivePolynomial p).natDegree = p.h ∧
    0 < RealTransfer.evalReal (GeneralIrrationality.primitivePolynomial p)
      (Real.zeta p.weight) ∧
    Real.zeta p.weight = (riemannZeta (p.weight : ℂ)).re ∧
    0 < 1 / ‖whitened (Real.manuscriptPencil p)‖ ∧
    (∀ z : ℂ,
      (GeneralIrrationality.primitivePolynomial p).eval₂ (algebraMap ℤ ℂ) z = 0 →
        z.im = 0 ∧ z ≠ (Real.zeta p.weight : ℂ) ∧
          1 / ‖whitened (Real.manuscriptPencil p)‖ ≤
            ‖z - (Real.zeta p.weight : ℂ)‖) ∧
    (∃ z : ℂ,
      (GeneralIrrationality.primitivePolynomial p).eval₂ (algebraMap ℤ ℂ) z = 0 ∧
      ‖z - (Real.zeta p.weight : ℂ)‖ = 1 / ‖whitened (Real.manuscriptPencil p)‖) := by
  obtain ⟨hpos, _, hboundary⟩ := primitive_exact_norm_disk p hp
  refine ⟨GeneralIrrationality.primitivePolynomial_isPrimitive p,
    GeneralIrrationality.primitivePolynomial_natDegree p,
    GeneralIrrationality.primitivePolynomial_eval_pos p hp,
    General.center_eq_riemannZeta p hp,
    hpos, ?_, hboundary⟩
  intro z hz
  have hroot := (primitive_complex_root_iff p z).mp hz
  have hd := primitive_root_distance p hp z hz
  refine ⟨General.roots_real p (GRAM_POSITIVE p hp) z hroot, ?_, hd⟩
  intro heq
  rw [heq, sub_self, norm_zero] at hd
  exact (not_le_of_gt hpos) hd

end LeanPaper.PrimitiveNormDisk

#print axioms LeanPaper.PrimitiveNormDisk.primitive_complex_root_iff
#print axioms LeanPaper.PrimitiveNormDisk.primitive_exact_norm_disk
#print axioms LeanPaper.PrimitiveNormDisk.primitive_theorem_3_1
