import LeanPaper.ImportedMultiweight.FiniteMultiweightCone
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Tactic

/-!
# Theorem 6.6: a positive anchor inside a semidefinite multiweight cone

The earlier finite multiweight theorem assumed every component matrix was
positive definite and every weight strictly positive. These stronger results
need only positive SEMIDEFINITENESS of all components, nonnegative weights,
and one strictly positive weighted positive-definite anchor.

The result is finite-dimensional and unconditional. It does NOT identify
an unproved continuous moment integral or establish the entire manuscript
Theorem 6.6; all such analytic input remains a separate open frontier.
-/

noncomputable section
open Matrix Polynomial
open scoped BigOperators

namespace PaperAdvances.Theorem6_6_AnchoredSemidefiniteCone

/-- Any nonnegative finite cone of positive semidefinite matrices becomes
strictly positive definite if one positively weighted component is
strictly positive definite. All other weights may be zero. -/
theorem ANCHORED_FINITE_CONE_POSDEF
    {n : ℕ} {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (A : ι → Matrix (Fin n) (Fin n) ℝ)
    (w : ι → ℝ)
    (hA : ∀ i ∈ s, (A i).PosSemidef)
    (hw : ∀ i ∈ s, 0 ≤ w i)
    (j : ι) (hj : j ∈ s)
    (hAj : (A j).PosDef) (hwj : 0 < w j) :
    (∑ i ∈ s, w i • A i).PosDef := by
  classical
  have hrest : (∑ i ∈ s.erase j, w i • A i).PosSemidef := by
    apply Matrix.posSemidef_sum (s.erase j)
    intro i hi
    exact (hA i (Finset.mem_of_mem_erase hi)).smul
      (hw i (Finset.mem_of_mem_erase hi))
  have hanchor : (w j • A j).PosDef := hAj.smul hwj
  have hsplit : (∑ i ∈ s, w i • A i) =
      w j • A j + ∑ i ∈ s.erase j, w i • A i := by
    calc
      (∑ i ∈ s, w i • A i) =
          ∑ i ∈ insert j (s.erase j), w i • A i := by
            rw [Finset.insert_erase hj]
      _ = w j • A j + ∑ i ∈ s.erase j, w i • A i := by
            rw [Finset.sum_insert (Finset.notMem_erase j s)]
  rw [hsplit]
  exact hanchor.add_posSemidef hrest

/-- Consequently, arbitrary nonnegative semidefinite weight families
with one positive-definite anchor have exact determinant degree, a full
real-root factorization, no nonreal complex zeros, global first Turan
nonnegativity and strict Turan away from zeros in positive dimension. -/
theorem ANCHORED_FINITE_CONE_SPECTRAL_PACKAGE
    {n : ℕ} {ι : Type*} [DecidableEq ι]
    (p : ManuscriptChain.Spectral.SymmetricAffinePencil n)
    (s : Finset ι) (A : ι → Matrix (Fin n) (Fin n) ℝ)
    (w : ι → ℝ)
    (hA : ∀ i ∈ s, (A i).PosSemidef)
    (hw : ∀ i ∈ s, 0 ≤ w i)
    (j : ι) (hj : j ∈ s)
    (hAj : (A j).PosDef) (hwj : 0 < w j)
    (hdir : p.direction = ∑ i ∈ s, w i • A i) :
    (∃ beta : Fin n → ℝ,
      p.detPolynomial = Polynomial.C p.direction.det *
        ∏ i, (Polynomial.X + Polynomial.C (beta i - p.center))) ∧
    p.detPolynomial.natDegree = n ∧
    (∀ z : ℂ, Polynomial.eval₂ (algebraMap ℝ ℂ) z p.detPolynomial = 0 →
      z.im = 0) ∧
    (∀ x : ℝ,
      0 ≤ PaperAdvances.Theorem3_7_AllDegrees.turan p.detPolynomial x) ∧
    (∀ hn : 0 < n, ∀ x : ℝ, p.detPolynomial.eval x ≠ 0 →
      0 < PaperAdvances.Theorem3_7_AllDegrees.turan p.detPolynomial x) := by
  have hp : p.direction.PosDef := by
    rw [hdir]
    exact ANCHORED_FINITE_CONE_POSDEF s A w hA hw j hj hAj hwj
  refine ⟨PaperAdvances.Theorem5_2_RealRoots.positive_slope_factorization p hp,
    PaperAdvances.Theorem5_2_RealRoots.positive_slope_exact_degree p hp,
    ?_, ?_, ?_⟩
  · intro z hz
    exact PaperAdvances.Theorem5_2_RealRoots.positive_slope_complex_roots_real p hp z hz
  · intro x
    exact PaperAdvances.Theorem3_7_AllDegrees.positive_slope_turan_nonnegative p hp x
  · intro hn x hx
    exact PaperAdvances.Theorem3_7_StrictRolle.positive_slope_turan_strict_offroots
      p hp hn x hx

end PaperAdvances.Theorem6_6_AnchoredSemidefiniteCone

#print axioms PaperAdvances.Theorem6_6_AnchoredSemidefiniteCone.ANCHORED_FINITE_CONE_POSDEF
#print axioms PaperAdvances.Theorem6_6_AnchoredSemidefiniteCone.ANCHORED_FINITE_CONE_SPECTRAL_PACKAGE
