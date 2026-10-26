import LeanPaper.DerivativeDistinctRoots
import LeanPaper.StrictCenteredLaguerre
import Mathlib.Data.List.OfFn

/-!
# Strict degree-normalized Laguerre inequality for real-split polynomials

An arbitrary real-split polynomial is factored using its actual root multiset,
including multiplicities. Logarithmic differentiation gives the exact finite
variance identity. Two distinct roots make the variance strictly positive at
every non-root. No finite spectrum or derivative certificate is assumed.
-/

noncomputable section
open scoped BigOperators Topology
open Polynomial Filter

namespace LeanPaper.StrictLaguerreGeneral

open LeanPaper.NormalizedNewton LeanPaper.StrictCenteredLaguerre
open LeanPaper.DerivativeDistinctRoots

theorem factorized_logDeriv {n : ℕ} (P : ℝ[X]) (c : ℝ) (r : Fin n → ℝ)
    (hfac : P = C c * ∏ i, (X - C (r i))) (hc : c ≠ 0) (x : ℝ)
    (hx : P.eval x ≠ 0) :
    logDeriv (fun y : ℝ => P.eval y) x = ∑ i, (x - r i)⁻¹ := by
  have hvalue : (fun y : ℝ => P.eval y) =
      (fun y : ℝ => c * ∏ i, (y - r i)) := by
    funext y
    simp [hfac, Polynomial.eval_prod]
  have hprod : (∏ i, (x - r i)) ≠ 0 := by
    have hh := hx
    change (fun y : ℝ => P.eval y) x ≠ 0 at hh
    rw [hvalue] at hh
    exact (mul_ne_zero_iff.mp hh).2
  have hgap (i : Fin n) : x - r i ≠ 0 :=
    (Finset.prod_ne_zero_iff.mp hprod) i (Finset.mem_univ i)
  have hd (i : Fin n) : HasDerivAt (fun y : ℝ => y - r i) 1 x :=
    (hasDerivAt_id x).sub_const (r i)
  rw [hvalue, logDeriv_const_mul x _ hc,
    logDeriv_prod (fun i _ => hgap i) (fun i _ => (hd i).differentiableAt)]
  apply Finset.sum_congr rfl
  intro i _
  rw [logDeriv_apply, (hd i).deriv, one_div]

theorem real_logDeriv_hasDerivAt (P : ℝ[X]) (x : ℝ) (hx : P.eval x ≠ 0) :
    HasDerivAt (logDeriv (fun y : ℝ => P.eval y))
      ((P.derivative.derivative.eval x * P.eval x - P.derivative.eval x ^ 2) /
        P.eval x ^ 2) x := by
  have heq : logDeriv (fun y : ℝ => P.eval y) =
      (fun y : ℝ => P.derivative.eval y / P.eval y) := by
    funext y
    rw [logDeriv_apply, Polynomial.deriv]
  rw [heq]
  simpa only [pow_two] using
    (P.derivative.hasDerivAt x).fun_div (P.hasDerivAt x) hx

theorem factorized_laguerre_dispersion {n : ℕ} (P : ℝ[X]) (c : ℝ) (r : Fin n → ℝ)
    (hfac : P = C c * ∏ i, (X - C (r i))) (hc : c ≠ 0) (x : ℝ)
    (hx : P.eval x ≠ 0) :
    laguerre n P x = P.eval x ^ 2 * dispersion (fun i => (x - r i)⁻¹) := by
  have hgap (i : Fin n) : x - r i ≠ 0 := by
    intro hz
    apply hx
    have hprod : (∏ j, (x - r j)) = 0 := Finset.prod_eq_zero (Finset.mem_univ i) hz
    simpa [hfac, Polynomial.eval_prod] using congrArg (fun z : ℝ => c * z) hprod
  have hd (i : Fin n) : HasDerivAt (fun y : ℝ => (y - r i)⁻¹)
      (-((x - r i)⁻¹) ^ 2) x := by
    apply (((hasDerivAt_id x).sub_const (r i)).fun_inv (hgap i)).congr_deriv
    simp only [neg_div, one_div, inv_pow, id_eq]
  have hsum : HasDerivAt (fun y : ℝ => ∑ i, (y - r i)⁻¹)
      (-(∑ i, ((x - r i)⁻¹) ^ 2)) x := by
    simpa only [Finset.sum_neg_distrib] using
      HasDerivAt.fun_sum (u := Finset.univ) (fun i _ => hd i)
  have hlog : HasDerivAt (logDeriv (fun y : ℝ => P.eval y))
      (-(∑ i, ((x - r i)⁻¹) ^ 2)) x := by
    apply hsum.congr_of_eventuallyEq
    have hevent := P.continuousAt.eventually_ne hx
    filter_upwards [hevent] with y hy
    exact factorized_logDeriv P c r hfac hc y hy
  have hsecond := hlog.unique (real_logDeriv_hasDerivAt P x hx)
  have hsecond' : (∑ i, ((x - r i)⁻¹) ^ 2) =
      (P.derivative.eval x ^ 2 - P.derivative.derivative.eval x * P.eval x) /
        P.eval x ^ 2 := by
    calc
      _ = -((P.derivative.derivative.eval x * P.eval x - P.derivative.eval x ^ 2) /
          P.eval x ^ 2) := by linarith [hsecond]
      _ = _ := by ring
  have hfirst := factorized_logDeriv P c r hfac hc x hx
  rw [logDeriv_apply, Polynomial.deriv] at hfirst
  unfold dispersion
  rw [← hfirst, hsecond']
  unfold laguerre
  field_simp [hx]
  <;> ring

/-- The exact generic off-root strictness theorem; no simplicity is assumed. -/
theorem laguerre_strict_of_distinct_roots {P : ℝ[X]} (hP : P.Splits)
    (hdist : HasDistinctRoots P) (x : ℝ) (hx : P.eval x ≠ 0) :
    0 < laguerre P.natDegree P x := by
  classical
  have hpne : P ≠ 0 := by intro hz; simp [hz] at hx
  let r : Fin P.roots.toList.length → ℝ := P.roots.toList.get
  have hprod : (∏ i, (X - C (r i))) =
      (P.roots.map (fun a : ℝ => (X : ℝ[X]) - C a)).prod := by
    calc
      (∏ i, (X - C (r i))) =
          (P.roots.toList.map (fun a : ℝ => (X : ℝ[X]) - C a)).prod := by
        rw [← Fin.prod_ofFn]
        congr 1
        dsimp only [r]
        simpa only [List.get_eq_getElem] using
          (List.ofFn_getElem_eq_map P.roots.toList (fun a : ℝ => (X : ℝ[X]) - C a))
      _ = _ := Multiset.prod_map_toList _ _
  have hfac : P = C P.leadingCoeff * ∏ i, (X - C (r i)) := by
    rw [hprod]
    exact hP.eq_prod_roots
  have hdegree : P.roots.toList.length = P.natDegree := by
    rw [Multiset.length_toList, ← hP.natDegree_eq_card_roots]
  rw [← hdegree, factorized_laguerre_dispersion P P.leadingCoeff r hfac
    (Polynomial.leadingCoeff_ne_zero.mpr hpne) x hx]
  apply mul_pos (sq_pos_of_ne_zero hx)
  obtain ⟨a, b, ha, hb, hab⟩ := hdist
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp
    (Multiset.mem_toList.mpr ((Polynomial.mem_roots hpne).mpr ha))
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp
    (Multiset.mem_toList.mpr ((Polynomial.mem_roots hpne).mpr hb))
  apply dispersion_positive_of_distinct _ i j
  intro hij
  have heq := inv_injective hij
  change x - P.roots.toList.get i = x - P.roots.toList.get j at heq
  rw [hi, hj] at heq
  exact hab (by linarith)

end LeanPaper.StrictLaguerreGeneral

#print axioms LeanPaper.StrictLaguerreGeneral.laguerre_strict_of_distinct_roots
