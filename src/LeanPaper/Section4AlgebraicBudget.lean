import LeanPaper.Section4ConjugateBounds
import LeanPaper.Section4IndexSelection
import Mathlib.Analysis.Complex.Exponential

/-! # Uniform logarithmic index budget for Proposition 4.2

The coefficient factors and all conjugates are controlled uniformly for
minimal polynomials of bounded degree. No resultant bound or index budget is
assumed: the finite resultant bound is proved in `Section4ConjugateBounds`.
-/
noncomputable section
open Filter Topology Polynomial
namespace LeanPaper.Section4AlgebraicBudget
open Section4Resultant Section4IndexSelection

lemma eventually_degree_factor (q : ℕ → ℕ) (lam : ℝ) (hlam : 0 ≤ lam)
    (hq : ∀ᶠ K : ℕ in atTop, (q K : ℝ) ≤ lam*K) :
    ∀ᶠ K : ℕ in atTop, (q K : ℝ)+1 ≤ Real.exp K := by
  filter_upwards [hq, eventually_ge_atTop ⌈2*(lam+1)⌉₊,
    eventually_ge_atTop 1] with K hqK hlarge hpos
  have hK : 2*(lam+1) ≤ (K : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hlarge)
  have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast hpos
  have hm := mul_le_mul_of_nonneg_right hK (Nat.cast_nonneg K : (0 : ℝ) ≤ K)
  have he := Real.pow_div_factorial_le_exp (K : ℝ) (Nat.cast_nonneg K) 2
  norm_num at he
  nlinarith

/-- Uniformly in `m ≤ d`, the entire upper resultant estimate tends below
one at the selected height index. The quadratic gap absorbs every displayed
linear or polynomial coefficient cost. -/
theorem eventually_conjugate_budget
    (Q : ℕ → ℤ[X]) (d : ℕ) (lam ε L c : ℝ)
    (hlam : 0 ≤ lam) (hL : 0 ≤ L) (hc : 0 < c)
    (hgap : ((d-1 : ℕ) : ℝ)*L + lam/c < ε)
    (hdegree : ∀ᶠ K : ℕ in atTop, ((Q K).natDegree : ℝ) ≤ lam*K)
    (hheight : ∀ᶠ K : ℕ in atTop, naiveHeight (Q K) ≤ Real.exp (L*(K : ℝ)^2)) :
    ∀ᶠ B : ℕ in atTop, ∀ m : ℕ, m ≤ d →
      2*Real.exp (-ε*(gridIndex 1 c B : ℝ)^2) *
        ((((Q (gridIndex 1 c B)).natDegree : ℝ)+1)*naiveHeight (Q (gridIndex 1 c B)))^(m-1) *
        (Real.sqrt ((m : ℝ)+1)*(B : ℝ))^(Q (gridIndex 1 c B)).natDegree < 1 := by
  let a : ℝ := ε-((d-1 : ℕ) : ℝ)*L-lam/c
  let C : ℝ := ((d-1 : ℕ) : ℝ)+lam*((d : ℝ)+1)+lam/c
  have ha : 0 < a := by dsimp [a]; linarith
  have hindex := gridIndex_tendsto 1 (by omega) c hc
  have hpoly := eventually_degree_factor (fun K => (Q K).natDegree) lam hlam hdegree
  have hquad : ∀ᶠ K : ℕ in atTop,
      ((((d-1 : ℕ) : ℝ)*L+lam/c-ε)*(K : ℝ)^2+C*K) ≤ -(K : ℝ) := by
    filter_upwards [eventually_ge_atTop ⌈(C+1)/a⌉₊] with K hK
    have hh : (C+1)/a ≤ (K : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hK)
    have hm := mul_le_mul_of_nonneg_right ((div_le_iff₀ ha).mp hh)
      (Nat.cast_nonneg K : (0 : ℝ) ≤ K)
    dsimp [a] at hm
    nlinarith
  have hsmall : ∀ᶠ K : ℕ in atTop, 2*Real.exp (-(K : ℝ)) < 1 :=
    ((Real.tendsto_exp_neg_atTop_nhds_zero.comp tendsto_natCast_atTop_atTop).const_mul 2).eventually
      (by simpa using gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [eventually_gt_atTop 0, hindex.eventually hdegree,
    hindex.eventually hheight, hindex.eventually hpoly, hindex.eventually hquad,
    hindex.eventually hsmall] with B hB hq hH hp hquadratic hS
  intro m hmd
  let K := gridIndex 1 c B
  let q := (Q K).natDegree
  have hBpos : (0 : ℝ) < B := by exact_mod_cast hB
  have hlog := Real.log_nonneg (show (1 : ℝ) ≤ B by exact_mod_cast (Nat.succ_le_iff.mpr hB))
  have hupper : Real.log (B : ℝ) ≤ ((K : ℝ)+1)/c := by
    apply (le_div_iff₀ hc).2
    have hu := (gridIndex_bounds 1 (by omega) c hc B hB).2
    dsimp [K]
    norm_num at hu
    nlinarith
  have hHnon : 0 ≤ naiveHeight (Q K) := (complexPolynomial (Q K)).supNorm_nonneg
  have hcoef : (((q : ℝ)+1)*naiveHeight (Q K))^(m-1) ≤
      Real.exp ((((d-1 : ℕ) : ℝ))*((K : ℝ)+L*(K : ℝ)^2)) := by
    calc
      _ ≤ (Real.exp ((K : ℝ)+L*(K : ℝ)^2))^(m-1) := by
        apply pow_le_pow_left₀ (by positivity)
        rw [Real.exp_add]
        exact mul_le_mul hp hH (by positivity) (Real.exp_pos _).le
      _ ≤ (Real.exp ((K : ℝ)+L*(K : ℝ)^2))^(d-1) :=
        pow_le_pow_right₀ (Real.one_le_exp_iff.mpr (by positivity)) (Nat.sub_le_sub_right hmd 1)
      _ = _ := (Real.exp_nat_mul _ _).symm
  have hsqrt : Real.sqrt ((m : ℝ)+1) ≤ Real.exp ((d : ℝ)+1) := by
    have hm : (m : ℝ) ≤ d := by exact_mod_cast hmd
    have hsq : Real.sqrt ((m : ℝ)+1) ≤ (m : ℝ)+1 :=
      Real.sqrt_le_self_iff.mpr (Or.inr (by have := Nat.cast_nonneg (α := ℝ) m; linarith))
    linarith [Real.add_one_le_exp ((d : ℝ)+1)]
  have hbase : Real.sqrt ((m : ℝ)+1)*(B : ℝ) ≤
      Real.exp ((d : ℝ)+1+Real.log B) := by
    rw [Real.exp_add, Real.exp_log hBpos]
    exact mul_le_mul_of_nonneg_right hsqrt hBpos.le
  have hconj : (Real.sqrt ((m : ℝ)+1)*(B : ℝ))^q ≤
      Real.exp (lam*(K : ℝ)*((d : ℝ)+1+((K : ℝ)+1)/c)) := by
    calc
      _ ≤ (Real.exp ((d : ℝ)+1+Real.log B))^q := pow_le_pow_left₀ (by positivity) hbase _
      _ = Real.exp ((q : ℝ)*((d : ℝ)+1+Real.log B)) := (Real.exp_nat_mul _ _).symm
      _ ≤ _ := by
        apply Real.exp_le_exp.mpr
        apply mul_le_mul hq (by linarith) (by positivity) (by positivity)
  have hexponent : -ε*(K : ℝ)^2 +
      (((d-1 : ℕ) : ℝ))*((K : ℝ)+L*(K : ℝ)^2) +
      lam*(K : ℝ)*((d : ℝ)+1+((K : ℝ)+1)/c) ≤ -(K : ℝ) := by
    convert hquadratic using 1 <;> dsimp [C, K] <;> ring
  calc
    _ ≤ 2*Real.exp (-ε*(K : ℝ)^2) *
        Real.exp ((((d-1 : ℕ) : ℝ))*((K : ℝ)+L*(K : ℝ)^2)) *
        Real.exp (lam*(K : ℝ)*((d : ℝ)+1+((K : ℝ)+1)/c)) := by
      apply mul_le_mul _ hconj (by positivity) (by positivity)
      exact mul_le_mul_of_nonneg_left hcoef (by positivity)
    _ = 2*Real.exp (-ε*(K : ℝ)^2 +
        (((d-1 : ℕ) : ℝ))*((K : ℝ)+L*(K : ℝ)^2) +
        lam*(K : ℝ)*((d : ℝ)+1+((K : ℝ)+1)/c)) := by
      rw [Real.exp_add, Real.exp_add]; ring
    _ ≤ 2*Real.exp (-(K : ℝ)) := by gcongr
    _ < 1 := hS

#print axioms eventually_conjugate_budget
end LeanPaper.Section4AlgebraicBudget
