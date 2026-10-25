import LeanPaper.ReciprocalAllOrders
import LeanPaper.ReciprocalNearestRootLimit

/-!
# Complete corrected finite-family Corollary 3.6

The ordinary input is a rational non-root of the actual primitive integer
polynomial. All logarithmic, rationality, positive finite-measure, exact
Hankel-rank, finite-factor and nearest-root-limit conclusions are assembled
with no extra analytic or root-simplicity premises.

This theorem certifies the explicitly corrected statement. It cannot certify
the printed all-orders strict-Hankel claim, alternating sign for r-x gaps,
or reversed finite-factor interval.
-/

noncomputable section
open scoped BigOperators Topology
open Filter Polynomial

namespace LeanPaper.CorrectedReciprocalCorollary

open ManuscriptChain
open LeanPaper.ReciprocalRootMoments
open LeanPaper.ReciprocalAllOrders
open LeanPaper.ReciprocalNearestRootLimit

/-- Non-root hypotheses for the actual rational determinant and its actual
primitive integer normalization are equivalent. -/
theorem primitive_nonzero_iff_delta (p : Real.Parameters) (x : ℝ) :
    RealTransfer.evalReal (GeneralIrrationality.primitivePolynomial p) x ≠ 0 ↔
      Real.evalQ (Real.delta p) x ≠ 0 := by
  have hs : ((GeneralIrrationality.normalization p).scale : ℝ) ≠ 0 := by
    exact_mod_cast ne_of_gt (GeneralIrrationality.normalization p).scale_pos
  rw [GeneralIrrationality.primitivePolynomial_eval]
  exact mul_ne_zero_iff.trans (and_iff_right hs)

/-- All clauses of the corrected fixed-K corollary for the manuscript family.
The Hankel threshold is the number of distinct inverse-square gaps. -/
theorem corrected_corollary_3_6
    (p : Real.Parameters) (hp : Real.Admissible p) (q : ℚ)
    (hq : RealTransfer.evalReal (GeneralIrrationality.primitivePolynomial p) (q : ℝ) ≠ 0) :
    (∀ m : ℕ, ∃ a : ℚ,
      reciprocalEvenMoment (manuscriptRoots p hp) (q : ℝ) m = (a : ℝ)) ∧
    (∀ n : ℕ, inverseGapSum (manuscriptRoots p hp) (n + 1) (q : ℝ) =
      (rationalMoment ((GeneralIrrationality.primitivePolynomial p).map (Int.castRingHom ℚ))
        n q : ℝ)) ∧
    (∀ n : ℕ, iteratedDeriv (n + 1)
      (fun y : ℝ => _root_.Real.log
        (RealTransfer.evalReal (GeneralIrrationality.primitivePolynomial p) y)) (q : ℝ) =
      -(n.factorial : ℝ) * inverseGapSum (manuscriptRoots p hp) (n + 1) (q : ℝ)) ∧
    (∀ i, 0 < reciprocalAtom (manuscriptRoots p hp) (q : ℝ) i) ∧
    (∀ n : ℕ,
      (reciprocalHankel (manuscriptRoots p hp) (q : ℝ) n).PosSemidef ∧
      Matrix.PosSemidef (fun i j : Fin n => reciprocalEvenMoment (manuscriptRoots p hp)
        (q : ℝ) (i.val + j.val + 1)) ∧
      (0 < (reciprocalHankel (manuscriptRoots p hp) (q : ℝ) n).det ↔
        n ≤ (atomSupport (reciprocalAtom (manuscriptRoots p hp) (q : ℝ))).card) ∧
      ((atomSupport (reciprocalAtom (manuscriptRoots p hp) (q : ℝ))).card < n →
        (reciprocalHankel (manuscriptRoots p hp) (q : ℝ) n).det = 0)) ∧
    (∃ j : Fin p.h,
      0 < |manuscriptRoots p hp j - (q : ℝ)| ∧
      (∀ i, |manuscriptRoots p hp j - (q : ℝ)| ≤
        |manuscriptRoots p hp i - (q : ℝ)|) ∧
      (∀ n : ℕ, 0 < n →
        (p.h : ℝ) ^ (-1 / (2 * (n : ℝ))) * |manuscriptRoots p hp j - (q : ℝ)| ≤
          reciprocalEvenMoment (manuscriptRoots p hp) (q : ℝ) n ^ (-1 / (2 * (n : ℝ))) ∧
        reciprocalEvenMoment (manuscriptRoots p hp) (q : ℝ) n ^ (-1 / (2 * (n : ℝ))) ≤
          |manuscriptRoots p hp j - (q : ℝ)|) ∧
      Tendsto (fun m : ℕ =>
        reciprocalEvenMoment (manuscriptRoots p hp) (q : ℝ) (m + 1) ^
          (-1 / (2 * ((m + 1 : ℕ) : ℝ)))) atTop
        (𝓝 |manuscriptRoots p hp j - (q : ℝ)|)) := by
  have hdelta := (primitive_nonzero_iff_delta p (q : ℝ)).mp hq
  exact ⟨fun m => actual_even_moment_exists_rational p hp m q hdelta,
    fun n => primitive_inverseGapSum_rational p hp n q hq,
    fun n => primitive_iterated_log p hp n (q : ℝ) hq,
    (manuscript_reciprocal_moments p hp q hdelta 0).1,
    fun n => (manuscript_reciprocal_moments p hp q hdelta n).2,
    actual_nearest_root_limit p hp q hdelta⟩

end LeanPaper.CorrectedReciprocalCorollary

#print axioms LeanPaper.CorrectedReciprocalCorollary.corrected_corollary_3_6
