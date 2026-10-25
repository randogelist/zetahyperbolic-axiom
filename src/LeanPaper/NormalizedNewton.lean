import LeanPaper.HigherDerivativeTuran
import Mathlib.Algebra.Polynomial.Taylor

/-!
# Degree-normalized Turan and Newton inequalities

The strengthened Laguerre inequality is proved by a real-root-product
induction, including multiplicities and zeros of the polynomial. Applying
it to each derivative yields the complete binomial-normalized Newton
inequalities, both for coefficients and for coefficients after every real
translation. No coefficient sign assumption is needed.

The final declarations specialize this hierarchy to the actual primitive
integer normalization of the manuscript determinant. Strict Newton
inequalities and the manuscript's proposed equality classification are
not asserted here.

Source: new proof using the pinned Mathlib real Rolle/root-count theorem
and the actual spectral factorization, through HigherDerivativeTuran.
-/

noncomputable section
open Polynomial

namespace LeanPaper.NormalizedNewton

open HigherDerivativeTuran

/-- The degree-normalized Laguerre expression. Its parameter is the
degree, not a freely chosen upper bound. -/
def laguerre (n : ℕ) (P : ℝ[X]) (x : ℝ) : ℝ :=
  ((n : ℝ) - 1) * (P.derivative.eval x) ^ 2 -
    (n : ℝ) * P.eval x * (P.derivative.derivative.eval x)

private theorem laguerre_const_mul (n : ℕ) (P : ℝ[X]) (c x : ℝ) :
    laguerre n (C c * P) x = c ^ 2 * laguerre n P x := by
  simp only [laguerre, Polynomial.derivative_C_mul, Polynomial.eval_mul,
    Polynomial.eval_C]
  ring

/-- A sum-of-squares recurrence for adjoining one real root. -/
theorem laguerre_mul_root_identity (m : ℕ) (P : ℝ[X]) (a x : ℝ) :
    (m : ℝ) * laguerre (m + 1) ((X - C a) * P) x =
      ((m : ℝ) + 1) * (x - a) ^ 2 * laguerre m P x +
        ((x - a) * P.derivative.eval x - (m : ℝ) * P.eval x) ^ 2 := by
  have hfirst : (((X - C a) * P) : ℝ[X]).derivative =
      P + (X - C a) * P.derivative := by simp
  have hsecond : (((X - C a) * P) : ℝ[X]).derivative.derivative =
      2 * P.derivative + (X - C a) * P.derivative.derivative := by
    rw [hfirst]
    simp only [Polynomial.derivative_add, Polynomial.derivative_mul,
      Polynomial.derivative_sub, Polynomial.derivative_X,
      Polynomial.derivative_C, sub_zero, one_mul]
    ring
  unfold laguerre
  rw [hsecond, hfirst]
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_sub,
    Polynomial.eval_X, Polynomial.eval_C, Polynomial.eval_ofNat, Nat.cast_add,
    Nat.cast_one]
  ring

private def rootsProduct (r : Multiset ℝ) : ℝ[X] :=
  (r.map (fun a => (X : ℝ[X]) - C a)).prod

private theorem rootsProduct_cons (a : ℝ) (r : Multiset ℝ) :
    rootsProduct (a ::ₘ r) = (X - C a) * rootsProduct r := by
  simp [rootsProduct]

private theorem laguerre_roots_nonnegative (r : Multiset ℝ) (x : ℝ) :
    0 ≤ laguerre r.card (rootsProduct r) x := by
  induction r using Multiset.induction_on with
  | empty => simp [rootsProduct, laguerre]
  | cons a r ih =>
      by_cases hr : r = 0
      · subst r
        simp [rootsProduct, laguerre]
      · have hm : 0 < (r.card : ℝ) := by
          exact_mod_cast (Multiset.card_pos.mpr hr)
        have hid := laguerre_mul_root_identity r.card (rootsProduct r) a x
        have hnonneg : 0 ≤ (r.card : ℝ) *
            laguerre (r.card + 1) ((X - C a) * rootsProduct r) x := by
          rw [hid]
          exact add_nonneg (mul_nonneg (mul_nonneg (by positivity) (sq_nonneg _)) ih)
            (sq_nonneg _)
        have hresult := nonneg_of_mul_nonneg_right hnonneg hm
        simpa only [Multiset.card_cons, rootsProduct_cons] using hresult

/-- The sharpened global Laguerre inequality for every real-rooted polynomial. -/
theorem laguerre_nonnegative_of_real_splits {P : ℝ[X]} (hP : P.Splits) (x : ℝ) :
    0 ≤ laguerre P.natDegree P x := by
  have heq : laguerre P.natDegree P x =
      P.leadingCoeff ^ 2 * laguerre P.roots.card (rootsProduct P.roots) x := by
    conv_lhs => arg 2; rw [hP.eq_prod_roots]
    rw [laguerre_const_mul, hP.natDegree_eq_card_roots]
    rfl
  rw [heq]
  exact mul_nonneg (sq_nonneg _) (laguerre_roots_nonnegative P.roots x)

/-- Formal-derivative value divided by the falling factorial of the degree.
At zero this is the ordinary coefficient divided by its binomial weight. -/
def normalizedJet (P : ℝ[X]) (n k : ℕ) (x : ℝ) : ℝ :=
  (Polynomial.derivative^[k] P).eval x / (n.descFactorial k : ℝ)

private theorem normalize_laguerre (A B C d f : ℝ) (hd : 1 < d) (hf : 0 < f)
    (h : 0 ≤ (d - 1) * B ^ 2 - d * A * C) :
    A / f * (C / ((d - 1) * d * f)) ≤ (B / (d * f)) ^ 2 := by
  have hd0 : d ≠ 0 := ne_of_gt (lt_trans zero_lt_one hd)
  have hd1 : d - 1 ≠ 0 := ne_of_gt (sub_pos.mpr hd)
  have hf0 : f ≠ 0 := ne_of_gt hf
  have heq : (B / (d * f)) ^ 2 - A / f * (C / ((d - 1) * d * f)) =
      ((d - 1) * B ^ 2 - d * A * C) / ((d - 1) * d ^ 2 * f ^ 2) := by
    field_simp [hd0, hd1, hf0]
  have hquot : 0 ≤ ((d - 1) * B ^ 2 - d * A * C) /
      ((d - 1) * d ^ 2 * f ^ 2) := div_nonneg h (by positivity)
  rw [← heq] at hquot
  linarith

/-- Full degree-normalized derivative Newton hierarchy, at every real point. -/
theorem normalizedJet_newton {P : ℝ[X]} (hP : P.Splits) (k : ℕ)
    (hk : k + 2 ≤ P.natDegree) (x : ℝ) :
    normalizedJet P P.natDegree k x * normalizedJet P P.natDegree (k + 2) x ≤
      normalizedJet P P.natDegree (k + 1) x ^ 2 := by
  let n := P.natDegree
  have hkn : k ≤ n := by dsimp [n]; omega
  have hdn : 2 ≤ n - k := by dsimp [n]; omega
  have hd : 1 < ((n - k : ℕ) : ℝ) := by
    exact_mod_cast (show 1 < n - k by omega)
  have hf : 0 < (n.descFactorial k : ℝ) := by
    exact_mod_cast (Nat.descFactorial_pos.mpr hkn)
  have hdsub : ((n - (k + 1) : ℕ) : ℝ) = ((n - k : ℕ) : ℝ) - 1 := by
    have heq : n - (k + 1) + 1 = n - k := by omega
    have heqr : ((n - (k + 1) : ℕ) : ℝ) + 1 = ((n - k : ℕ) : ℝ) := by
      exact_mod_cast heq
    linarith
  have hfac1 : (n.descFactorial (k + 1) : ℝ) =
      ((n - k : ℕ) : ℝ) * (n.descFactorial k : ℝ) := by
    simp only [Nat.descFactorial_succ, Nat.cast_mul]
  have hfac2 : (n.descFactorial (k + 2) : ℝ) =
      (((n - k : ℕ) : ℝ) - 1) * ((n - k : ℕ) : ℝ) *
        (n.descFactorial k : ℝ) := by
    rw [show k + 2 = (k + 1) + 1 by omega, Nat.descFactorial_succ, Nat.cast_mul,
      hfac1, hdsub]
    ring
  have hlag := laguerre_nonnegative_of_real_splits
    (real_splits_iterated_derivative hP k) x
  rw [laguerre, iterated_derivative_natDegree] at hlag
  have h := normalize_laguerre
    ((Polynomial.derivative^[k] P).eval x)
    ((Polynomial.derivative^[k + 1] P).eval x)
    ((Polynomial.derivative^[k + 2] P).eval x)
    ((n - k : ℕ) : ℝ) (n.descFactorial k : ℝ) hd hf
    (by simpa only [Function.iterate_succ_apply'] using hlag)
  change normalizedJet P n k x * normalizedJet P n (k + 2) x ≤
    normalizedJet P n (k + 1) x ^ 2
  simpa only [normalizedJet, hfac1, hfac2] using h

theorem normalizedJet_zero (P : ℝ[X]) (n k : ℕ) (hk : k ≤ n) :
    normalizedJet P n k 0 = P.coeff k / (n.choose k : ℝ) := by
  unfold normalizedJet
  rw [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_iterate_derivative]
  simp only [zero_add, Nat.descFactorial_self, nsmul_eq_mul]
  rw [Nat.descFactorial_eq_factorial_mul_choose, Nat.cast_mul]
  have hf : (k.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
  have hc : (n.choose k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.choose_ne_zero hk)
  field_simp [hf, hc]

/-- The complete binomial-normalized coefficient inequalities. This remains
valid for mixed-sign coefficients; it does not assert strictness. -/
theorem coefficient_newton {P : ℝ[X]} (hP : P.Splits) (k : ℕ)
    (hk : k + 2 ≤ P.natDegree) :
    (P.coeff k / (P.natDegree.choose k : ℝ)) *
      (P.coeff (k + 2) / (P.natDegree.choose (k + 2) : ℝ)) ≤
        (P.coeff (k + 1) / (P.natDegree.choose (k + 1) : ℝ)) ^ 2 := by
  have h := normalizedJet_newton hP k hk 0
  rw [normalizedJet_zero P P.natDegree k (by omega),
    normalizedJet_zero P P.natDegree (k + 1) (by omega),
    normalizedJet_zero P P.natDegree (k + 2) hk] at h
  exact h

/-- The same normalized Newton hierarchy after every real translation. -/
theorem shifted_coefficient_newton {P : ℝ[X]} (hP : P.Splits) (a : ℝ) (k : ℕ)
    (hk : k + 2 ≤ P.natDegree) :
    ((P.taylor a).coeff k / (P.natDegree.choose k : ℝ)) *
      ((P.taylor a).coeff (k + 2) / (P.natDegree.choose (k + 2) : ℝ)) ≤
        ((P.taylor a).coeff (k + 1) / (P.natDegree.choose (k + 1) : ℝ)) ^ 2 := by
  have hs : (P.taylor a).Splits := hP.comp_X_add_C a
  simpa only [Polynomial.natDegree_taylor] using
    coefficient_newton hs k (by simpa only [Polynomial.natDegree_taylor] using hk)

/-- Newton is homogeneous of degree two, so division of every shifted
coefficient by the polynomial's center value preserves the inequality. -/
theorem normalized_shifted_newton {P : ℝ[X]} (hP : P.Splits) (a : ℝ) (k : ℕ)
    (hk : k + 2 ≤ P.natDegree) :
    (((P.taylor a).coeff k / P.eval a) / (P.natDegree.choose k : ℝ)) *
      (((P.taylor a).coeff (k + 2) / P.eval a) /
        (P.natDegree.choose (k + 2) : ℝ)) ≤
      (((P.taylor a).coeff (k + 1) / P.eval a) /
        (P.natDegree.choose (k + 1) : ℝ)) ^ 2 := by
  have h := mul_le_mul_of_nonneg_left (shifted_coefficient_newton hP a k hk)
    (sq_nonneg ((P.eval a)⁻¹))
  simpa only [div_eq_mul_inv, pow_two, mul_assoc, mul_left_comm, mul_comm] using h

open ManuscriptChain

/-- The sharpened, non-strict bound for the actual normalized determinant. -/
theorem actual_primitive_laguerre (p : Real.Parameters) (hp : Real.Admissible p)
    (x : ℝ) : 0 ≤ laguerre p.h (primitiveRealPolynomial p) x := by
  simpa only [primitiveRealPolynomial_natDegree] using
    laguerre_nonnegative_of_real_splits (primitiveRealPolynomial_splits p hp) x

/-- All binomial-normalized Newton coefficient inequalities for the actual
primitive integer polynomial, transported to real coefficients. -/
theorem actual_primitive_coefficient_newton
    (p : Real.Parameters) (hp : Real.Admissible p) (k : ℕ) (hk : k + 2 ≤ p.h) :
    ((primitiveRealPolynomial p).coeff k / (p.h.choose k : ℝ)) *
      ((primitiveRealPolynomial p).coeff (k + 2) / (p.h.choose (k + 2) : ℝ)) ≤
        ((primitiveRealPolynomial p).coeff (k + 1) / (p.h.choose (k + 1) : ℝ)) ^ 2 := by
  simpa only [primitiveRealPolynomial_natDegree] using
    coefficient_newton (primitiveRealPolynomial_splits p hp) k
      (by simpa only [primitiveRealPolynomial_natDegree] using hk)

/-- The full weak shifted Newton hierarchy for every real center of the
actual normalized determinant. -/
theorem actual_primitive_shifted_newton
    (p : Real.Parameters) (hp : Real.Admissible p) (a : ℝ) (k : ℕ)
    (hk : k + 2 ≤ p.h) :
    (((primitiveRealPolynomial p).taylor a).coeff k / (p.h.choose k : ℝ)) *
      (((primitiveRealPolynomial p).taylor a).coeff (k + 2) / (p.h.choose (k + 2) : ℝ)) ≤
        (((primitiveRealPolynomial p).taylor a).coeff (k + 1) /
          (p.h.choose (k + 1) : ℝ)) ^ 2 := by
  simpa only [primitiveRealPolynomial_natDegree] using
    shifted_coefficient_newton (primitiveRealPolynomial_splits p hp) a k
      (by simpa only [primitiveRealPolynomial_natDegree] using hk)

/-- Exactly the weak Newton hierarchy for the paper's coefficients
e_m = [Y^m] P(zeta + Y) / P(zeta), with binomial normalization. -/
theorem actual_primitive_centered_newton
    (p : Real.Parameters) (hp : Real.Admissible p) (k : ℕ) (hk : k + 2 ≤ p.h) :
    ((((primitiveRealPolynomial p).taylor (Real.zeta p.weight)).coeff k /
        (primitiveRealPolynomial p).eval (Real.zeta p.weight)) /
      (p.h.choose k : ℝ)) *
      ((((primitiveRealPolynomial p).taylor (Real.zeta p.weight)).coeff (k + 2) /
          (primitiveRealPolynomial p).eval (Real.zeta p.weight)) /
        (p.h.choose (k + 2) : ℝ)) ≤
      ((((primitiveRealPolynomial p).taylor (Real.zeta p.weight)).coeff (k + 1) /
          (primitiveRealPolynomial p).eval (Real.zeta p.weight)) /
        (p.h.choose (k + 1) : ℝ)) ^ 2 := by
  simpa only [primitiveRealPolynomial_natDegree] using
    normalized_shifted_newton (primitiveRealPolynomial_splits p hp)
      (Real.zeta p.weight) k
      (by simpa only [primitiveRealPolynomial_natDegree] using hk)

end LeanPaper.NormalizedNewton

#print axioms LeanPaper.NormalizedNewton.laguerre_nonnegative_of_real_splits
#print axioms LeanPaper.NormalizedNewton.actual_primitive_laguerre
#print axioms LeanPaper.NormalizedNewton.actual_primitive_coefficient_newton
#print axioms LeanPaper.NormalizedNewton.actual_primitive_shifted_newton
#print axioms LeanPaper.NormalizedNewton.actual_primitive_centered_newton
