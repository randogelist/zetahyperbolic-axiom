import LeanPaper.StrictLaguerreGeneral

/-!
# Strict normalized Newton hierarchy and exact equality criterion

For a real-split polynomial with two distinct roots, the degree-normalized
Newton inequalities are strict exactly at the coefficient patterns stated in
Theorem 3.7(2). At a non-root translation center, consecutive Taylor zeros
are impossible, hence the full translated hierarchy is strict. Individual
Taylor coefficients need not be nonzero.
-/

noncomputable section
open Polynomial

namespace LeanPaper.StrictNormalizedNewton

open LeanPaper.HigherDerivativeTuran LeanPaper.NormalizedNewton
open LeanPaper.DerivativeDistinctRoots LeanPaper.ConsecutiveDerivativeZeros
open LeanPaper.StrictLaguerreGeneral

theorem laguerre_strict_iff {P : ℝ[X]} (hP : P.Splits) (hdist : HasDistinctRoots P)
    (hd : 2 ≤ P.natDegree) (x : ℝ) :
    0 < laguerre P.natDegree P x ↔ P.eval x ≠ 0 ∨ P.derivative.eval x ≠ 0 := by
  constructor
  · intro hh
    by_contra hz
    push Not at hz
    simp only [laguerre, hz.1, hz.2, zero_pow (by decide : 2 ≠ 0),
      mul_zero, zero_mul, sub_self, lt_self_iff_false] at hh
  · rintro (ha | hb)
    · exact laguerre_strict_of_distinct_roots hP hdist x ha
    · by_cases ha : P.eval x = 0
      · have hn : (1 : ℝ) < (P.natDegree : ℝ) := by exact_mod_cast (by omega : 1 < P.natDegree)
        simp only [laguerre, ha, mul_zero, zero_mul, sub_zero]
        exact mul_pos (sub_pos.mpr hn) (sq_pos_of_ne_zero hb)
      · exact laguerre_strict_of_distinct_roots hP hdist x ha

private theorem normalize_laguerre_strict (A B C d f : ℝ) (hd : 1 < d) (hf : 0 < f)
    (h : 0 < (d - 1) * B ^ 2 - d * A * C) :
    A / f * (C / ((d - 1) * d * f)) < (B / (d * f)) ^ 2 := by
  have hd0 : d ≠ 0 := ne_of_gt (lt_trans zero_lt_one hd)
  have hd1 : d - 1 ≠ 0 := ne_of_gt (sub_pos.mpr hd)
  have hf0 : f ≠ 0 := ne_of_gt hf
  have heq : (B / (d * f)) ^ 2 - A / f * (C / ((d - 1) * d * f)) =
      ((d - 1) * B ^ 2 - d * A * C) / ((d - 1) * d ^ 2 * f ^ 2) := by
    field_simp [hd0, hd1, hf0]
  have hquot : 0 < ((d - 1) * B ^ 2 - d * A * C) /
      ((d - 1) * d ^ 2 * f ^ 2) := div_pos h (by positivity)
  rw [← heq] at hquot
  linarith

theorem normalizedJet_newton_strict_of_pair {P : ℝ[X]} (hP : P.Splits)
    (hdist : HasDistinctRoots P) (k : ℕ) (hk : k + 2 ≤ P.natDegree) (x : ℝ)
    (hpair : (Polynomial.derivative^[k] P).eval x ≠ 0 ∨
      (Polynomial.derivative^[k + 1] P).eval x ≠ 0) :
    normalizedJet P P.natDegree k x * normalizedJet P P.natDegree (k + 2) x <
      normalizedJet P P.natDegree (k + 1) x ^ 2 := by
  let n := P.natDegree
  have hkn : k ≤ n := by dsimp [n]; omega
  have hdn : 2 ≤ n - k := by dsimp [n]; omega
  have hd : 1 < ((n - k : ℕ) : ℝ) := by exact_mod_cast (show 1 < n - k by omega)
  have hf : 0 < (n.descFactorial k : ℝ) := by exact_mod_cast (Nat.descFactorial_pos.mpr hkn)
  have hdsub : ((n - (k + 1) : ℕ) : ℝ) = ((n - k : ℕ) : ℝ) - 1 := by
    have heq : n - (k + 1) + 1 = n - k := by omega
    have heqr : ((n - (k + 1) : ℕ) : ℝ) + 1 = ((n - k : ℕ) : ℝ) := by exact_mod_cast heq
    linarith
  have hfac1 : (n.descFactorial (k + 1) : ℝ) =
      ((n - k : ℕ) : ℝ) * (n.descFactorial k : ℝ) := by
    simp only [Nat.descFactorial_succ, Nat.cast_mul]
  have hfac2 : (n.descFactorial (k + 2) : ℝ) =
      (((n - k : ℕ) : ℝ) - 1) * ((n - k : ℕ) : ℝ) * (n.descFactorial k : ℝ) := by
    rw [show k + 2 = (k + 1) + 1 by omega, Nat.descFactorial_succ,
      Nat.cast_mul, hfac1, hdsub]
    ring
  have hlag := (laguerre_strict_iff (real_splits_iterated_derivative hP k)
    (iterated_derivative_hasDistinctRoots hP hdist k hk)
    (by rw [iterated_derivative_natDegree]; exact hdn) x).mpr
      (by simpa only [Function.iterate_succ_apply'] using hpair)
  rw [laguerre, iterated_derivative_natDegree] at hlag
  have hh := normalize_laguerre_strict
    ((Polynomial.derivative^[k] P).eval x)
    ((Polynomial.derivative^[k + 1] P).eval x)
    ((Polynomial.derivative^[k + 2] P).eval x)
    ((n - k : ℕ) : ℝ) (n.descFactorial k : ℝ) hd hf
    (by simpa only [Function.iterate_succ_apply'] using hlag)
  change normalizedJet P n k x * normalizedJet P n (k + 2) x <
    normalizedJet P n (k + 1) x ^ 2
  simpa only [normalizedJet, hfac1, hfac2] using hh

theorem normalizedJet_newton_strict_iff {P : ℝ[X]} (hP : P.Splits)
    (hdist : HasDistinctRoots P) (k : ℕ) (hk : k + 2 ≤ P.natDegree) (x : ℝ) :
    normalizedJet P P.natDegree k x * normalizedJet P P.natDegree (k + 2) x <
        normalizedJet P P.natDegree (k + 1) x ^ 2 ↔
      (Polynomial.derivative^[k] P).eval x ≠ 0 ∨
        (Polynomial.derivative^[k + 1] P).eval x ≠ 0 := by
  constructor
  · intro hh
    by_contra hz
    push Not at hz
    simp only [normalizedJet, hz.1, hz.2, zero_div, zero_mul,
      zero_pow (by decide : 2 ≠ 0), lt_self_iff_false] at hh
  · exact normalizedJet_newton_strict_of_pair hP hdist k hk x

theorem coefficient_newton_strict_iff_pair {P : ℝ[X]} (hP : P.Splits)
    (hdist : HasDistinctRoots P) (k : ℕ) (hk : k + 2 ≤ P.natDegree) :
    (P.coeff k / (P.natDegree.choose k : ℝ)) *
        (P.coeff (k + 2) / (P.natDegree.choose (k + 2) : ℝ)) <
        (P.coeff (k + 1) / (P.natDegree.choose (k + 1) : ℝ)) ^ 2 ↔
      P.coeff k ≠ 0 ∨ P.coeff (k + 1) ≠ 0 := by
  have hh := normalizedJet_newton_strict_iff hP hdist k hk 0
  rw [normalizedJet_zero P P.natDegree k (by omega),
    normalizedJet_zero P P.natDegree (k + 1) (by omega),
    normalizedJet_zero P P.natDegree (k + 2) hk] at hh
  have hv (j : ℕ) : (Polynomial.derivative^[j] P).eval 0 =
      (j.factorial : ℝ) * P.coeff j := by
    rw [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_iterate_derivative]
    simp only [zero_add, Nat.descFactorial_self, nsmul_eq_mul]
  have hf0 : (k.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  have hf1 : ((k + 1).factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (k + 1)
  rw [hv k, hv (k + 1)] at hh
  constructor
  · intro h
    rcases hh.mp h with ha | hb
    · exact Or.inl (mul_ne_zero_iff.mp ha).2
    · exact Or.inr (mul_ne_zero_iff.mp hb).2
  · intro h
    apply hh.mpr
    rcases h with ha | hb
    · exact Or.inl (mul_ne_zero hf0 ha)
    · exact Or.inr (mul_ne_zero hf1 hb)

/-- Exactly the strictness condition printed in Theorem 3.7(2). -/
theorem coefficient_newton_strict_criterion {P : ℝ[X]} (hP : P.Splits)
    (hdist : HasDistinctRoots P) (k : ℕ) (hk : k + 2 ≤ P.natDegree) :
    (P.coeff k / (P.natDegree.choose k : ℝ)) *
        (P.coeff (k + 2) / (P.natDegree.choose (k + 2) : ℝ)) <
        (P.coeff (k + 1) / (P.natDegree.choose (k + 1) : ℝ)) ^ 2 ↔
      P.coeff (k + 1) ≠ 0 ∨ (P.coeff k ≠ 0 ∧ P.coeff (k + 2) ≠ 0) := by
  constructor
  · intro hh
    by_cases hb : P.coeff (k + 1) = 0
    · right
      constructor <;> intro hz <;>
        simp only [hz, hb, zero_div, zero_mul, mul_zero,
          zero_pow (by decide : 2 ≠ 0), lt_self_iff_false] at hh
    · exact Or.inl hb
  · rintro (hb | ⟨ha, _⟩)
    · exact (coefficient_newton_strict_iff_pair hP hdist k hk).mpr (Or.inr hb)
    · exact (coefficient_newton_strict_iff_pair hP hdist k hk).mpr (Or.inl ha)

theorem hasDistinctRoots_taylor {P : ℝ[X]} (hdist : HasDistinctRoots P) (x : ℝ) :
    HasDistinctRoots (P.taylor x) := by
  obtain ⟨a, b, ha, hb, hab⟩ := hdist
  refine ⟨a - x, b - x, ?_, ?_, ?_⟩
  · simpa only [Polynomial.IsRoot.def, Polynomial.taylor_apply, Polynomial.eval_comp,
      Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C, sub_add_cancel] using ha
  · simpa only [Polynomial.IsRoot.def, Polynomial.taylor_apply, Polynomial.eval_comp,
      Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C, sub_add_cancel] using hb
  · intro hh
    exact hab (by linarith)

/-- At a non-root center all shifted Newton inequalities are strict, even
if individual shifted coefficients vanish. -/
theorem shifted_coefficient_newton_strict {P : ℝ[X]} (hP : P.Splits)
    (hdist : HasDistinctRoots P) (x : ℝ) (hx : P.eval x ≠ 0)
    (k : ℕ) (hk : k + 2 ≤ P.natDegree) :
    ((P.taylor x).coeff k / (P.natDegree.choose k : ℝ)) *
        ((P.taylor x).coeff (k + 2) / (P.natDegree.choose (k + 2) : ℝ)) <
        ((P.taylor x).coeff (k + 1) / (P.natDegree.choose (k + 1) : ℝ)) ^ 2 := by
  have hs : (P.taylor x).Splits := hP.comp_X_add_C x
  have hh := (coefficient_newton_strict_iff_pair (P := P.taylor x) hs
    (hasDistinctRoots_taylor hdist x) k
    (by simpa only [Polynomial.natDegree_taylor] using hk)).mpr
      (consecutive_taylor_nonvanishing hP k (by omega) x hx)
  simpa only [Polynomial.natDegree_taylor] using hh

theorem normalized_shifted_newton_strict {P : ℝ[X]} (hP : P.Splits)
    (hdist : HasDistinctRoots P) (x : ℝ) (hx : P.eval x ≠ 0)
    (k : ℕ) (hk : k + 2 ≤ P.natDegree) :
    (((P.taylor x).coeff k / P.eval x) / (P.natDegree.choose k : ℝ)) *
        (((P.taylor x).coeff (k + 2) / P.eval x) /
          (P.natDegree.choose (k + 2) : ℝ)) <
      (((P.taylor x).coeff (k + 1) / P.eval x) /
        (P.natDegree.choose (k + 1) : ℝ)) ^ 2 := by
  have hh := mul_lt_mul_of_pos_left (shifted_coefficient_newton_strict hP hdist x hx k hk)
    (sq_pos_of_ne_zero (inv_ne_zero hx))
  simpa only [div_eq_mul_inv, pow_two, mul_assoc, mul_left_comm, mul_comm] using hh

end LeanPaper.StrictNormalizedNewton

#print axioms LeanPaper.StrictNormalizedNewton.coefficient_newton_strict_criterion
#print axioms LeanPaper.StrictNormalizedNewton.normalized_shifted_newton_strict
