import LeanPaper.ImportedSection3.StrictTuranRolle
import MAIN_CHAIN_IRRATIONALITY
import Mathlib.Algebra.Polynomial.Splits
import Mathlib.Analysis.Calculus.LocalExtr.Polynomial

/-!
# Higher-derivative Turan inequalities for the actual manuscript polynomial

Rolle's theorem with multiplicities preserves real splitting under formal
differentiation. Consequently the first Turan inequality applies to every
iterated derivative. Strictness holds off its zeros while that derivative
still has positive degree. This includes the manuscript range 1 ≤ m ≤ h-1.

The primitive integer normalization is transported explicitly to a real
polynomial, so the endpoint concerns the paper's normalized polynomial as
well as its rational determinant. The separate binomial-normalized Newton
hierarchy, its equality assertions, and the sharpened strict center bound
are not established by these declarations.
-/

noncomputable section
open Polynomial

namespace LeanPaper.HigherDerivativeTuran

open PaperAdvances.Theorem3_7_AllDegrees
open PaperAdvances.Theorem3_7_StrictRolle

/-- Rolle's multiplicity count proves derivative closure over the real field. -/
theorem real_splits_derivative {P : ℝ[X]} (hP : P.Splits) : P.derivative.Splits := by
  by_cases hd : P.natDegree = 0
  · rw [Polynomial.derivative_of_natDegree_zero hd]
    exact Polynomial.Splits.zero
  · apply Polynomial.splits_iff_card_roots.mpr
    have hroots := Polynomial.card_roots_le_derivative P
    have hupper := Polynomial.card_roots' P.derivative
    have hcount := hP.natDegree_eq_card_roots
    have hdegree := Polynomial.natDegree_derivative P
    omega

/-- Every formal derivative, including the eventual zero polynomial, splits. -/
theorem real_splits_iterated_derivative {P : ℝ[X]} (hP : P.Splits) (k : ℕ) :
    (Polynomial.derivative^[k] P).Splits := by
  induction k with
  | zero => simpa using hP
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact real_splits_derivative ih

/-- The exact degree law for iterated derivatives in characteristic zero. -/
theorem iterated_derivative_natDegree (P : ℝ[X]) (k : ℕ) :
    (Polynomial.derivative^[k] P).natDegree = P.natDegree - k := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Function.iterate_succ_apply', Polynomial.natDegree_derivative, ih]
      omega

private def rootProduct (r : Multiset ℝ) : ℝ[X] :=
  (r.map (fun a => (X : ℝ[X]) - C a)).prod

private theorem rootProduct_cons (a : ℝ) (r : Multiset ℝ) :
    rootProduct (a ::ₘ r) = (X - C a) * rootProduct r := by
  simp [rootProduct]

private theorem rootProduct_turan_cons (a : ℝ) (r : Multiset ℝ) (x : ℝ) :
    turan (rootProduct (a ::ₘ r)) x =
      (x - a) ^ 2 * turan (rootProduct r) x + ((rootProduct r).eval x) ^ 2 := by
  rw [rootProduct_cons,
    turan_mul_linear (rootProduct r) (X - C a) 1 x (by simp)]
  simp

private theorem rootProduct_turan_nonnegative (r : Multiset ℝ) (x : ℝ) :
    0 ≤ turan (rootProduct r) x := by
  induction r using Multiset.induction_on with
  | empty => simp [rootProduct, turan]
  | cons a r ih =>
      rw [rootProduct_turan_cons]
      exact add_nonneg (mul_nonneg (sq_nonneg _) ih) (sq_nonneg _)

private theorem rootProduct_turan_strict (r : Multiset ℝ) (hr : r ≠ 0)
    (x : ℝ) (hx : (rootProduct r).eval x ≠ 0) :
    0 < turan (rootProduct r) x := by
  induction r using Multiset.induction_on with
  | empty => exact (hr rfl).elim
  | cons a r ih =>
      have hvalue : (rootProduct r).eval x ≠ 0 := by
        rw [rootProduct_cons, Polynomial.eval_mul] at hx
        exact (mul_ne_zero_iff.mp hx).2
      rw [rootProduct_turan_cons]
      exact add_pos_of_nonneg_of_pos
        (mul_nonneg (sq_nonneg _) (rootProduct_turan_nonnegative r x))
        (sq_pos_of_ne_zero hvalue)

/-- Every real-split polynomial satisfies the global first Turan inequality. -/
theorem turan_nonnegative_of_real_splits {P : ℝ[X]} (hP : P.Splits) (x : ℝ) :
    0 ≤ turan P x := by
  rw [hP.eq_prod_roots, turan_const_mul]
  exact mul_nonneg (sq_nonneg _) (rootProduct_turan_nonnegative P.roots x)

/-- Positive degree gives strictness wherever a real-split polynomial is nonzero. -/
theorem turan_strict_of_real_splits {P : ℝ[X]} (hP : P.Splits)
    (hd : 0 < P.natDegree) (x : ℝ) (hx : P.eval x ≠ 0) :
    0 < turan P x := by
  have hp0 : P ≠ 0 := by
    intro hz
    simp [hz] at hd
  have hc : P.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hp0
  have hr : P.roots ≠ 0 := hP.roots_ne_zero (Nat.ne_of_gt hd)
  have hprod : (rootProduct P.roots).eval x ≠ 0 := by
    rw [hP.eq_prod_roots, Polynomial.eval_mul, Polynomial.eval_C] at hx
    exact (mul_ne_zero_iff.mp hx).2
  rw [hP.eq_prod_roots, turan_const_mul]
  exact mul_pos (sq_pos_of_ne_zero hc) (rootProduct_turan_strict P.roots hr x hprod)

/-- All derivative orders satisfy Turan, with no degree or nonvanishing input. -/
theorem iterated_turan_nonnegative {P : ℝ[X]} (hP : P.Splits) (k : ℕ) (x : ℝ) :
    0 ≤ turan (Polynomial.derivative^[k] P) x :=
  turan_nonnegative_of_real_splits (real_splits_iterated_derivative hP k) x

/-- Strictness through the last nonconstant derivative, at every non-root. -/
theorem iterated_turan_strict {P : ℝ[X]} (hP : P.Splits) (k : ℕ)
    (hk : k < P.natDegree) (x : ℝ)
    (hx : (Polynomial.derivative^[k] P).eval x ≠ 0) :
    0 < turan (Polynomial.derivative^[k] P) x := by
  apply turan_strict_of_real_splits (real_splits_iterated_derivative hP k) _ x hx
  rw [iterated_derivative_natDegree]
  exact Nat.sub_pos_of_lt hk

/-- At each nonconstant derivative, equality means a multiple real zero. -/
theorem iterated_turan_eq_zero_iff {P : ℝ[X]} (hP : P.Splits)
    (k : ℕ) (hk : k < P.natDegree) (x : ℝ) :
    turan (Polynomial.derivative^[k] P) x = 0 ↔
      (Polynomial.derivative^[k] P).eval x = 0 ∧
      (Polynomial.derivative (Polynomial.derivative^[k] P)).eval x = 0 :=
  turan_eq_zero_iff_multiple_zero _ x (iterated_turan_strict hP k hk x)

open ManuscriptChain

theorem spectral_polynomial_splits {n : ℕ}
    {p : Spectral.SymmetricAffinePencil n} (h : Spectral.RootFactorization p) :
    p.detPolynomial.Splits := by
  rw [h.factorization]
  apply Polynomial.Splits.mul (Polynomial.Splits.C _)
  apply Polynomial.Splits.prod
  intro i _
  exact Polynomial.Splits.of_natDegree_eq_one
    (Spectral.natDegree_spectralFactor p.center (h.beta i) (h.beta_ne_zero i))

/-- Splitting is obtained from the constructed actual Gram/spectral proof. -/
theorem actual_determinant_splits (p : Real.Parameters) (hp : Real.Admissible p) :
    (Real.realPolynomial (Real.delta p)).Splits := by
  simpa only [Real.manuscriptPencil_detPolynomial] using
    spectral_polynomial_splits (General.factorization p (GRAM_POSITIVE p hp))

/-- The real polynomial obtained from the actual primitive integer normalization. -/
def primitiveRealPolynomial (p : Real.Parameters) : ℝ[X] :=
  (GeneralIrrationality.primitivePolynomial p).map (algebraMap ℤ ℝ)

theorem primitiveRealPolynomial_identity (p : Real.Parameters) :
    primitiveRealPolynomial p =
      C ((GeneralIrrationality.normalization p).scale : ℝ) *
        Real.realPolynomial (Real.delta p) := by
  apply Polynomial.funext
  intro x
  change RealTransfer.evalReal (GeneralIrrationality.primitivePolynomial p) x = _
  rw [GeneralIrrationality.primitivePolynomial_eval]
  simp [Real.evalQ]

theorem primitiveRealPolynomial_splits (p : Real.Parameters) (hp : Real.Admissible p) :
    (primitiveRealPolynomial p).Splits := by
  rw [primitiveRealPolynomial_identity]
  exact (actual_determinant_splits p hp).C_mul _

theorem primitiveRealPolynomial_natDegree (p : Real.Parameters) :
    (primitiveRealPolynomial p).natDegree = p.h := by
  rw [primitiveRealPolynomial,
    Polynomial.natDegree_map_eq_of_injective
      (show Function.Injective (algebraMap ℤ ℝ) from Int.cast_injective),
    GeneralIrrationality.primitivePolynomial_natDegree]

/-- Complete higher-derivative Turan nonnegativity for the actual integer
normalization. `k=m-1` is exactly the manuscript's T_m expression. -/
theorem actual_primitive_all_derivative_turan
    (p : Real.Parameters) (hp : Real.Admissible p) (k : ℕ) (x : ℝ) :
    0 ≤ turan (Polynomial.derivative^[k] (primitiveRealPolynomial p)) x :=
  iterated_turan_nonnegative (primitiveRealPolynomial_splits p hp) k x

/-- The strict clause of the higher-derivative Turan theorem holds off roots,
through all nonconstant derivative orders of the actual normalized polynomial. -/
theorem actual_primitive_all_derivative_turan_strict
    (p : Real.Parameters) (hp : Real.Admissible p) (k : ℕ) (hk : k < p.h)
    (x : ℝ) (hx : (Polynomial.derivative^[k] (primitiveRealPolynomial p)).eval x ≠ 0) :
    0 < turan (Polynomial.derivative^[k] (primitiveRealPolynomial p)) x := by
  apply iterated_turan_strict (primitiveRealPolynomial_splits p hp) k _ x hx
  simpa only [primitiveRealPolynomial_natDegree] using hk

/-- The equality case is a multiple zero of the corresponding derivative. -/
theorem actual_primitive_all_derivative_turan_equality
    (p : Real.Parameters) (hp : Real.Admissible p) (k : ℕ) (hk : k < p.h) (x : ℝ) :
    turan (Polynomial.derivative^[k] (primitiveRealPolynomial p)) x = 0 ↔
      (Polynomial.derivative^[k] (primitiveRealPolynomial p)).eval x = 0 ∧
      (Polynomial.derivative
        (Polynomial.derivative^[k] (primitiveRealPolynomial p))).eval x = 0 := by
  apply iterated_turan_eq_zero_iff (primitiveRealPolynomial_splits p hp) k _ x
  simpa only [primitiveRealPolynomial_natDegree] using hk

end LeanPaper.HigherDerivativeTuran

#print axioms LeanPaper.HigherDerivativeTuran.real_splits_derivative
#print axioms LeanPaper.HigherDerivativeTuran.actual_primitive_all_derivative_turan
#print axioms LeanPaper.HigherDerivativeTuran.actual_primitive_all_derivative_turan_strict
#print axioms LeanPaper.HigherDerivativeTuran.actual_primitive_all_derivative_turan_equality
