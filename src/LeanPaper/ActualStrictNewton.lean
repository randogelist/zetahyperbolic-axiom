import LeanPaper.ActualStrictCenter
import LeanPaper.StrictNormalizedNewton

/-!
# The actual manuscript's strict Newton hierarchy

The two-distinct-root condition is discharged by the alternating residue
signature of the actual pencil. No root simplicity or genericity assumption
is used. All normalized Taylor Newton inequalities at the true zeta center
are strict. This does not claim that every individual Taylor coefficient is
nonzero, a separate assertion in the manuscript's prose.
-/

noncomputable section
open Polynomial

namespace LeanPaper.ActualStrictNewton

open ManuscriptChain
open LeanPaper.HigherDerivativeTuran LeanPaper.DerivativeDistinctRoots
open LeanPaper.ReciprocalRootMoments LeanPaper.ActualStrictCenter

theorem actual_primitive_hasDistinctRoots
    (p : Real.Parameters) (hp : Real.Admissible p) (hh : 2 ≤ p.h) :
    HasDistinctRoots (primitiveRealPolynomial p) := by
  obtain ⟨i, j, hij⟩ := actual_distinct_roots p hp hh
  have hroot (l : Fin p.h) : (primitiveRealPolynomial p).IsRoot (manuscriptRoots p hp l) := by
    change (primitiveRealPolynomial p).eval (manuscriptRoots p hp l) = 0
    rw [primitiveRealPolynomial_identity, Polynomial.eval_mul, Polynomial.eval_C]
    change ((GeneralIrrationality.normalization p).scale : ℝ) *
      Real.evalQ (Real.delta p) (manuscriptRoots p hp l) = 0
    rw [manuscriptRoots_eval, mul_zero]
  exact ⟨_, _, hroot i, hroot j, hij⟩

/-- The exact strict/non-strict coefficient pattern in Theorem3.7(2). -/
theorem actual_coefficient_strict_criterion
    (p : Real.Parameters) (hp : Real.Admissible p) (hh : 2 ≤ p.h)
    (k : ℕ) (hk : k + 2 ≤ p.h) :
    ((primitiveRealPolynomial p).coeff k / (p.h.choose k : ℝ)) *
        ((primitiveRealPolynomial p).coeff (k + 2) / (p.h.choose (k + 2) : ℝ)) <
        ((primitiveRealPolynomial p).coeff (k + 1) / (p.h.choose (k + 1) : ℝ)) ^ 2 ↔
      (primitiveRealPolynomial p).coeff (k + 1) ≠ 0 ∨
        ((primitiveRealPolynomial p).coeff k ≠ 0 ∧
          (primitiveRealPolynomial p).coeff (k + 2) ≠ 0) := by
  simpa only [primitiveRealPolynomial_natDegree] using
    StrictNormalizedNewton.coefficient_newton_strict_criterion
      (primitiveRealPolynomial_splits p hp) (actual_primitive_hasDistinctRoots p hp hh)
      k (by simpa only [primitiveRealPolynomial_natDegree] using hk)

/-- Every normalized Taylor Newton inequality at the actual zeta center is
strict, with no individual-coefficient-nonvanishing premise. -/
theorem actual_centered_newton_strict
    (p : Real.Parameters) (hp : Real.Admissible p) (hh : 2 ≤ p.h)
    (k : ℕ) (hk : k + 2 ≤ p.h) :
    ((((primitiveRealPolynomial p).taylor (Real.zeta p.weight)).coeff k /
        (primitiveRealPolynomial p).eval (Real.zeta p.weight)) /
      (p.h.choose k : ℝ)) *
      ((((primitiveRealPolynomial p).taylor (Real.zeta p.weight)).coeff (k + 2) /
          (primitiveRealPolynomial p).eval (Real.zeta p.weight)) /
        (p.h.choose (k + 2) : ℝ)) <
      ((((primitiveRealPolynomial p).taylor (Real.zeta p.weight)).coeff (k + 1) /
          (primitiveRealPolynomial p).eval (Real.zeta p.weight)) /
        (p.h.choose (k + 1) : ℝ)) ^ 2 := by
  simpa only [primitiveRealPolynomial_natDegree] using
    StrictNormalizedNewton.normalized_shifted_newton_strict
      (primitiveRealPolynomial_splits p hp) (actual_primitive_hasDistinctRoots p hp hh)
      (Real.zeta p.weight) (ne_of_gt (GeneralIrrationality.primitivePolynomial_eval_pos p hp))
      k (by simpa only [primitiveRealPolynomial_natDegree] using hk)

end LeanPaper.ActualStrictNewton

#print axioms LeanPaper.ActualStrictNewton.actual_coefficient_strict_criterion
#print axioms LeanPaper.ActualStrictNewton.actual_centered_newton_strict
