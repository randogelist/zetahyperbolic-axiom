import Theorem_4_1_Spectral_Irrationality_Measure_Criterion
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Polynomial comparison from complex-root separation

This proves the local comparison in Theorem 4.1 for arbitrary integer
polynomials with complex roots, without assuming a symmetric pencil or
assuming the comparison conclusion itself.
-/
noncomputable section
open Polynomial
namespace LeanPaper.Section4ComplexComparison

private theorem root_factor_bound (z w r : ℂ) (δ : ℝ) (hδ : 0 < δ)
    (hr : δ ≤ ‖w-r‖) :
    ‖z-r‖ ≤ Real.exp (‖z-w‖ / δ) * ‖w-r‖ := by
  have he : 0 ≤ ‖z-w‖ / δ := by positivity
  have hratio : ‖z-w‖ ≤ (‖z-w‖ / δ) * ‖w-r‖ := by
    calc
      ‖z-w‖ = (‖z-w‖ / δ) * δ := by field_simp
      _ ≤ (‖z-w‖ / δ) * ‖w-r‖ := mul_le_mul_of_nonneg_left hr he
  calc
    ‖z-r‖ = ‖(z-w)+(w-r)‖ := by congr 1; ring
    _ ≤ ‖z-w‖ + ‖w-r‖ := norm_add_le _ _
    _ ≤ (1 + ‖z-w‖ / δ) * ‖w-r‖ := by nlinarith
    _ ≤ Real.exp (‖z-w‖ / δ) * ‖w-r‖ := by
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      linarith [Real.add_one_le_exp (‖z-w‖ / δ)]

private theorem roots_product_bound (s : Multiset ℂ) (z w : ℂ) (δ : ℝ) (hδ : 0 < δ)
    (hsep : ∀ r ∈ s, δ ≤ ‖w-r‖) :
    ‖(s.map (fun r => z-r)).prod‖ ≤
      Real.exp ((s.card : ℝ) * (‖z-w‖ / δ)) * ‖(s.map (fun r => w-r)).prod‖ := by
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons r s ih =>
    have hr := hsep r (by simp)
    have hs : ∀ r ∈ s, δ ≤ ‖w-r‖ := fun r hr => hsep r (by simp [hr])
    have hi := ih hs
    simp only [Multiset.map_cons, Multiset.prod_cons, norm_mul, Multiset.card_cons,
      Nat.cast_add, Nat.cast_one]
    calc
      ‖z-r‖ * ‖(s.map (fun r => z-r)).prod‖
          ≤ (Real.exp (‖z-w‖ / δ) * ‖w-r‖) *
            (Real.exp ((s.card : ℝ) * (‖z-w‖ / δ)) * ‖(s.map (fun r => w-r)).prod‖) :=
        mul_le_mul (root_factor_bound z w r δ hδ hr) hi (norm_nonneg _) (by positivity)
      _ = Real.exp (((s.card : ℝ)+1) * (‖z-w‖ / δ)) *
            (‖w-r‖ * ‖(s.map (fun r => w-r)).prod‖) := by
        rw [add_mul, one_mul, Real.exp_add]
        ring

/-- Root separation alone supplies nonvanishing and the factor-two estimate. -/
theorem polynomial_comparison (P : ℂ[X]) (w z : ℂ) (δ : ℝ)
    (hδ : 0 < δ) (hPw : P.eval w ≠ 0)
    (hsep : ∀ r ∈ P.roots, δ ≤ ‖w-r‖)
    (hclose : ‖z-w‖ ≤ δ / (8 * ((P.natDegree : ℝ) + 1))) :
    P.eval z ≠ 0 ∧ ‖P.eval z‖ ≤ 2 * ‖P.eval w‖ := by
  have hP : P ≠ 0 := by intro h; simp [h] at hPw
  have hd : 0 < 8 * ((P.natDegree : ℝ) + 1) := by positivity
  have hclose' : ‖z-w‖ < δ := by
    apply hclose.trans_lt
    apply (div_lt_iff₀ hd).2
    have hn : (0 : ℝ) ≤ P.natDegree := Nat.cast_nonneg _
    nlinarith
  have hsum : (P.natDegree : ℝ) * (‖z-w‖ / δ) ≤ 1/4 := by
    have hmul := (le_div_iff₀ hd).mp hclose
    rw [← mul_div_assoc, div_le_iff₀ hδ]
    have hn : (0 : ℝ) ≤ P.natDegree := Nat.cast_nonneg _
    nlinarith [norm_nonneg (z-w)]
  constructor
  · intro hz
    have hzroot : z ∈ P.roots := (Polynomial.mem_roots hP).2 hz
    have h := hsep z hzroot
    rw [norm_sub_rev] at h
    linarith
  · have hs := IsAlgClosed.splits P
    rw [hs.eval_eq_prod_roots z, hs.eval_eq_prod_roots w, norm_mul, norm_mul]
    have hp := roots_product_bound P.roots z w δ hδ hsep
    rw [← hs.natDegree_eq_card_roots] at hp
    have hexp : Real.exp ((P.natDegree : ℝ) * (‖z-w‖ / δ)) ≤ 2 := by
      calc
        _ ≤ Real.exp (1/4 : ℝ) := Real.exp_le_exp.mpr hsum
        _ ≤ 1 / (1 - (1/4 : ℝ)) :=
          Real.exp_bound_div_one_sub_of_interval (by norm_num) (by norm_num)
        _ ≤ 2 := by norm_num
    have hprod := hp.trans (mul_le_mul_of_nonneg_right hexp (norm_nonneg _))
    nlinarith [mul_le_mul_of_nonneg_left hprod (norm_nonneg P.leadingCoeff)]

private theorem eval_real_cast (P : ℤ[X]) (x : ℝ) :
    (P.map (algebraMap ℤ ℂ)).eval (x : ℂ) =
      (ManuscriptChain.RealTransfer.evalReal P x : ℂ) := by
  have hmap : (P.map (algebraMap ℤ ℝ)).map Complex.ofRealHom =
      P.map (algebraMap ℤ ℂ) := by
    rw [Polynomial.map_map]
    congr 1
  rw [← hmap]
  exact Polynomial.eval_map_apply Complex.ofRealHom x

/-- The exact real local-comparison radius used by the index construction,
now justified for the arbitrary complex roots of an integer polynomial. -/
theorem integer_comparison (P : ℤ[X]) (ξ x ρ : ℝ) (K : ℕ)
    (hvalue : ManuscriptChain.RealTransfer.evalReal P ξ ≠ 0)
    (hsep : ∀ r ∈ (P.map (algebraMap ℤ ℂ)).roots,
      Real.exp (-ρ * K) ≤ ‖(ξ : ℂ) - r‖)
    (hclose : |x-ξ| ≤ ManuscriptChain.Spectral.comparisonRadius P.natDegree
      (Real.exp (ρ * K))) :
    ManuscriptChain.RealTransfer.evalReal P x ≠ 0 ∧
      |ManuscriptChain.RealTransfer.evalReal P x| ≤
        2 * |ManuscriptChain.RealTransfer.evalReal P ξ| := by
  have hnat : (P.map (algebraMap ℤ ℂ)).natDegree = P.natDegree :=
    Polynomial.natDegree_map_eq_of_injective (show Function.Injective (algebraMap ℤ ℂ)
      from Int.cast_injective) _
  have hv : (P.map (algebraMap ℤ ℂ)).eval (ξ : ℂ) ≠ 0 := by
    rw [eval_real_cast]
    exact_mod_cast hvalue
  have hx : ‖(x : ℂ) - (ξ : ℂ)‖ ≤ Real.exp (-ρ * K) /
      (8 * (((P.map (algebraMap ℤ ℂ)).natDegree : ℝ)+1)) := by
    rw [hnat, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    have hr : Real.exp (-ρ * K) / (8 * ((P.natDegree : ℝ)+1)) =
        ManuscriptChain.Spectral.comparisonRadius P.natDegree (Real.exp (ρ * K)) := by
      unfold ManuscriptChain.Spectral.comparisonRadius
      rw [neg_mul, Real.exp_neg]
      simp only [one_div, div_eq_mul_inv, mul_inv_rev]
      ring
    rw [hr]
    exact hclose
  have h := polynomial_comparison (P.map (algebraMap ℤ ℂ)) ξ x
    (Real.exp (-ρ * K)) (Real.exp_pos _) hv hsep hx
  rw [eval_real_cast, eval_real_cast] at h
  simpa only [Complex.ofReal_ne_zero, Complex.norm_real, Real.norm_eq_abs] using h

#print axioms polynomial_comparison
#print axioms integer_comparison

end LeanPaper.Section4ComplexComparison
