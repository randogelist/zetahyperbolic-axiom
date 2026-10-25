import LeanPaper.ImportedSection3.StrictTuranRolle
import LeanPaper.ImportedMultiweight.PositiveSlopeSpectrum
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Tactic

/-!
# Finite-dimensional multiweight positive spectral cones, Section 6.6

The full printed infinite multiweight theorem requires new analytic
integral bridges. The unconditional FINITE-SLOPE mechanism, by contrast,
works for arbitrarily many positive-weight positive-definite component
matrices. Their sum remains positive definite, so an affine symmetric
matrix pencil with that slope has a real-linear determinant
factorization, exact degree, complex-root reality and Turan positivity.

This is a mathematical theorem and not a conditional witness wrapper.
-/

noncomputable section
open Matrix Polynomial
open scoped BigOperators
namespace PaperAdvances.Theorem6_6_FiniteMultiweightCone

/-- An arbitrary finite positive cone of strictly positive definite
real matrices is again strictly positive definite. -/
theorem FINITE_MULTIWEIGHT_POSITIVE_DIRECTION
    {n : ℕ} {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (hs : s.Nonempty)
    (A : ι → Matrix (Fin n) (Fin n) ℝ) (w : ι → ℝ)
    (hA : ∀ i ∈ s, (A i).PosDef)
    (hw : ∀ i ∈ s, 0 < w i) :
    (∑ i ∈ s, w i • A i).PosDef := by
  apply Matrix.posDef_sum hs
  intro i hi
  exact (hA i hi).smul (hw i hi)

/-- The actual finite multiweight direction has a full real spectral
factorization even if the symmetric base matrix is indefinite. -/
theorem FINITE_MULTIWEIGHT_SPECTRAL_FACTORIZATION
    {n : ℕ} {ι : Type*} [DecidableEq ι]
    (p : ManuscriptChain.Spectral.SymmetricAffinePencil n)
    (s : Finset ι) (hs : s.Nonempty)
    (A : ι → Matrix (Fin n) (Fin n) ℝ) (w : ι → ℝ)
    (hA : ∀ i ∈ s, (A i).PosDef)
    (hw : ∀ i ∈ s, 0 < w i)
    (hdir : p.direction = ∑ i ∈ s, w i • A i) :
    ∃ beta : Fin n → ℝ,
      p.detPolynomial = Polynomial.C p.direction.det *
        ∏ i, (Polynomial.X + Polynomial.C (beta i - p.center)) := by
  have hp : p.direction.PosDef := by
    rw [hdir]
    exact FINITE_MULTIWEIGHT_POSITIVE_DIRECTION s hs A w hA hw
  exact PaperAdvances.Theorem5_2_RealRoots.positive_slope_factorization p hp

/-- Three simultaneous unconditional finite-cone consequences:
exact degree, no nonreal complex roots, and all-real-x Turan inequality. -/
theorem FINITE_MULTIWEIGHT_SPECTRAL_HYPERBOLICITY
    {n : ℕ} {ι : Type*} [DecidableEq ι]
    (p : ManuscriptChain.Spectral.SymmetricAffinePencil n)
    (s : Finset ι) (hs : s.Nonempty)
    (A : ι → Matrix (Fin n) (Fin n) ℝ) (w : ι → ℝ)
    (hA : ∀ i ∈ s, (A i).PosDef)
    (hw : ∀ i ∈ s, 0 < w i)
    (hdir : p.direction = ∑ i ∈ s, w i • A i) :
    p.detPolynomial.natDegree = n ∧
    (∀ z : ℂ, Polynomial.eval₂ (algebraMap ℝ ℂ) z p.detPolynomial = 0 →
       z.im = 0) ∧
    (∀ x : ℝ, 0 ≤ PaperAdvances.Theorem3_7_AllDegrees.turan p.detPolynomial x) := by
  have hp : p.direction.PosDef := by
    rw [hdir]
    exact FINITE_MULTIWEIGHT_POSITIVE_DIRECTION s hs A w hA hw
  exact ⟨PaperAdvances.Theorem5_2_RealRoots.positive_slope_exact_degree p hp,
    (fun z hz =>
      PaperAdvances.Theorem5_2_RealRoots.positive_slope_complex_roots_real p hp z hz),
    (fun x => PaperAdvances.Theorem3_7_AllDegrees.positive_slope_turan_nonnegative p hp x)⟩

/-- Strict first Turan positivity away from the roots in every positive
finite-dimensional multiweight cone, when the pencil has positive size. -/
theorem FINITE_MULTIWEIGHT_STRICT_TURAN
    {n : ℕ} {ι : Type*} [DecidableEq ι]
    (p : ManuscriptChain.Spectral.SymmetricAffinePencil n)
    (s : Finset ι) (hs : s.Nonempty)
    (A : ι → Matrix (Fin n) (Fin n) ℝ) (w : ι → ℝ)
    (hA : ∀ i ∈ s, (A i).PosDef)
    (hw : ∀ i ∈ s, 0 < w i)
    (hdir : p.direction = ∑ i ∈ s, w i • A i)
    (hn : 0 < n) (x : ℝ) (hx : p.detPolynomial.eval x ≠ 0) :
    0 < PaperAdvances.Theorem3_7_AllDegrees.turan p.detPolynomial x := by
  have hp : p.direction.PosDef := by
    rw [hdir]
    exact FINITE_MULTIWEIGHT_POSITIVE_DIRECTION s hs A w hA hw
  exact PaperAdvances.Theorem3_7_StrictRolle.positive_slope_turan_strict_offroots
    p hp hn x hx

end PaperAdvances.Theorem6_6_FiniteMultiweightCone

#print axioms PaperAdvances.Theorem6_6_FiniteMultiweightCone.FINITE_MULTIWEIGHT_POSITIVE_DIRECTION
#print axioms PaperAdvances.Theorem6_6_FiniteMultiweightCone.FINITE_MULTIWEIGHT_SPECTRAL_HYPERBOLICITY
#print axioms PaperAdvances.Theorem6_6_FiniteMultiweightCone.FINITE_MULTIWEIGHT_STRICT_TURAN
