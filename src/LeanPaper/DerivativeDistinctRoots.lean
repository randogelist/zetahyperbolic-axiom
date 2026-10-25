import LeanPaper.ConsecutiveDerivativeZeros
import Mathlib.Algebra.Polynomial.FieldDivision

/-!
# Distinct roots survive differentiation until degree one

For real-split polynomials, a derivative of degree at least two cannot
collapse to one repeated root unless the original polynomial already had
only that root. The proof propagates a multiple derivative root backward
using strict Turan, then uses the exact derivative multiplicity formula.
-/

noncomputable section
open Polynomial

namespace LeanPaper.DerivativeDistinctRoots

open LeanPaper.HigherDerivativeTuran
open LeanPaper.ConsecutiveDerivativeZeros

def HasDistinctRoots (P : ℝ[X]) : Prop :=
  ∃ a b : ℝ, P.IsRoot a ∧ P.IsRoot b ∧ a ≠ b

theorem derivative_hasDistinctRoots {P : ℝ[X]} (hP : P.Splits)
    (hd : 3 ≤ P.natDegree) (hdist : HasDistinctRoots P) :
    HasDistinctRoots P.derivative := by
  classical
  by_contra hnot
  have hone : ∀ a b : ℝ, P.derivative.IsRoot a → P.derivative.IsRoot b → a = b := by
    intro a b ha hb
    by_contra hab
    exact hnot ⟨a, b, ha, hb, hab⟩
  have hs := real_splits_derivative hP
  have hddeg : 2 ≤ P.derivative.natDegree := by
    rw [Polynomial.natDegree_derivative]
    omega
  have hdne : P.derivative ≠ 0 := by
    intro hz
    simp [hz] at hddeg
  have hpne : P ≠ 0 := by
    intro hz
    simp [hz] at hd
  obtain ⟨a, ha⟩ := Multiset.exists_mem_of_ne_zero
    (hs.roots_ne_zero (by omega))
  have haroot : P.derivative.IsRoot a := (Polynomial.mem_roots hdne).mp ha
  have hcount : P.derivative.roots.count a = P.derivative.roots.card :=
    Multiset.count_eq_card.mpr (fun b hb => hone a b haroot ((Polynomial.mem_roots hdne).mp hb))
  have hmult : P.derivative.rootMultiplicity a = P.derivative.natDegree := by
    simpa only [Polynomial.count_roots, ← hs.natDegree_eq_card_roots] using hcount
  have hdouble : P.derivative.derivative.IsRoot a := by
    have hm : 1 < P.derivative.rootMultiplicity a := by omega
    simpa only [Function.iterate_one] using
      (Polynomial.isRoot_iterate_derivative_of_lt_rootMultiplicity (n := 1) hm)
  have hpa : P.IsRoot a := by
    apply consecutive_derivative_zeros_force_root hP 1 (by omega) a
    · simpa only [Function.iterate_one, Polynomial.IsRoot.def] using haroot
    · simpa only [Function.iterate_succ_apply', Function.iterate_zero, id_eq, Polynomial.IsRoot.def] using hdouble
  have hpmult : P.rootMultiplicity a = P.natDegree := by
    rw [Polynomial.derivative_rootMultiplicity_of_root hpa,
      Polynomial.natDegree_derivative] at hmult
    omega
  have hall : ∀ b ∈ P.roots, a = b := by
    apply Multiset.count_eq_card.mp
    rw [Polynomial.count_roots, hpmult, hP.natDegree_eq_card_roots]
  obtain ⟨b, c, hb, hc, hbc⟩ := hdist
  exact hbc ((hall b ((Polynomial.mem_roots hpne).mpr hb)).symm.trans
    (hall c ((Polynomial.mem_roots hpne).mpr hc)))

/-- Every iterated derivative still of degree at least two has distinct roots. -/
theorem iterated_derivative_hasDistinctRoots {P : ℝ[X]} (hP : P.Splits)
    (hdist : HasDistinctRoots P) (k : ℕ) (hk : k + 2 ≤ P.natDegree) :
    HasDistinctRoots (Polynomial.derivative^[k] P) := by
  induction k with
  | zero => simpa only [Function.iterate_zero, id_eq] using hdist
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      apply derivative_hasDistinctRoots (real_splits_iterated_derivative hP k)
      · rw [iterated_derivative_natDegree]
        omega
      · exact ih (by omega)

end LeanPaper.DerivativeDistinctRoots

#print axioms LeanPaper.DerivativeDistinctRoots.derivative_hasDistinctRoots
#print axioms LeanPaper.DerivativeDistinctRoots.iterated_derivative_hasDistinctRoots
