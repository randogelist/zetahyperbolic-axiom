import Theorem_3_1_Hyperbolic_Weight
import Mathlib.Analysis.Calculus.SmoothSeries

/-!
# Theorem 3.8(2): differentiating the actual Laplace-scaled density

This supplies the derivative of the actual exponential series at every positive
scale. Differentiation of the infinite sum is justified by a summable bound on
an open neighborhood, rather than postulated. The subsequent exchange with the
improper moment integral remains a distinct obligation.
-/

noncomputable section
open scoped BigOperators Topology
open Set

namespace LeanPaper.LaplaceDensityDerivative

def exponentialSeries (m : ℕ) (c τ : ℝ) : ℝ :=
  ∑' n : ℕ, ((n + 1 : ℕ) : ℝ)^m * Real.exp (-(c * τ) * ((n + 1 : ℕ) : ℝ))

theorem summable_terms (m : ℕ) {c τ : ℝ} (hc : 0 < c) (hτ : 0 < τ) :
    Summable (fun n : ℕ => ((n + 1 : ℕ) : ℝ)^m *
      Real.exp (-(c * τ) * ((n + 1 : ℕ) : ℝ))) :=
  (summable_nat_add_iff 1).mpr
    (Real.summable_pow_mul_exp_neg_nat_mul m (mul_pos hc hτ))

theorem term_hasDerivAt (m n : ℕ) (c τ : ℝ) :
    HasDerivAt
      (fun t : ℝ => ((n + 1 : ℕ) : ℝ)^m *
        Real.exp (-(c * t) * ((n + 1 : ℕ) : ℝ)))
      (-c * ((n + 1 : ℕ) : ℝ)^(m + 1) *
        Real.exp (-(c * τ) * ((n + 1 : ℕ) : ℝ))) τ := by
  have hlinear : HasDerivAt (fun t : ℝ => -(c * t) * ((n + 1 : ℕ) : ℝ))
      (-c * ((n + 1 : ℕ) : ℝ)) τ := by
    simpa only [id, mul_one] using
      (((hasDerivAt_id τ).const_mul c).neg.mul_const ((n + 1 : ℕ) : ℝ))
  convert hlinear.exp.const_mul (((n + 1 : ℕ) : ℝ)^m) using 1 <;>
    simp only [pow_succ] <;> ring

/-- The derivative series is uniformly bounded on `τ > a` by its value at a
fixed positive scale. This is the needed summable local majorant. -/
theorem term_derivative_bound (m n : ℕ) {c a τ : ℝ}
    (hc : 0 < c) (haτ : a ≤ τ) :
    ‖-c * ((n + 1 : ℕ) : ℝ)^(m + 1) *
        Real.exp (-(c * τ) * ((n + 1 : ℕ) : ℝ))‖ ≤
      c * (((n + 1 : ℕ) : ℝ)^(m + 1) *
        Real.exp (-(c * a) * ((n + 1 : ℕ) : ℝ))) := by
  have hn : (0 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by positivity
  have hexp : Real.exp (-(c * τ) * ((n + 1 : ℕ) : ℝ)) ≤
      Real.exp (-(c * a) * ((n + 1 : ℕ) : ℝ)) := by
    apply Real.exp_le_exp.mpr
    have h := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left haτ hc.le) hn
    linarith
  rw [norm_mul, norm_mul, norm_neg, Real.norm_eq_abs, abs_of_pos hc,
    Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hn _),
    Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  simpa only [mul_assoc] using
    mul_le_mul_of_nonneg_left hexp (mul_nonneg hc.le (pow_nonneg hn _))

/-- Differentiation of the infinite series on the entire positive scale axis. -/
theorem exponentialSeries_hasDerivAt (m : ℕ) {c τ : ℝ}
    (hc : 0 < c) (hτ : 0 < τ) :
    HasDerivAt (exponentialSeries m c)
      (-c * exponentialSeries (m + 1) c τ) τ := by
  let g (n : ℕ) (t : ℝ) := ((n + 1 : ℕ) : ℝ)^m *
    Real.exp (-(c * t) * ((n + 1 : ℕ) : ℝ))
  let g' (n : ℕ) (t : ℝ) := -c * ((n + 1 : ℕ) : ℝ)^(m + 1) *
    Real.exp (-(c * t) * ((n + 1 : ℕ) : ℝ))
  let bound (n : ℕ) := c * (((n + 1 : ℕ) : ℝ)^(m + 1) *
    Real.exp (-(c * (τ / 2)) * ((n + 1 : ℕ) : ℝ)))
  have hhalf : 0 < τ / 2 := half_pos hτ
  have hmem : τ ∈ Ioi (τ / 2) := by dsimp; linarith
  have hs : Summable bound := (summable_terms (m + 1) hc hhalf).mul_left c
  have hd : ∀ n t, t ∈ Ioi (τ / 2) → HasDerivAt (g n) (g' n t) t := by
    intro n t _
    exact term_hasDerivAt m n c t
  have hb : ∀ n t, t ∈ Ioi (τ / 2) → ‖g' n t‖ ≤ bound n := by
    intro n t ht
    exact term_derivative_bound m n hc (le_of_lt ht)
  have h := hasDerivAt_tsum_of_isPreconnected hs isOpen_Ioi isPreconnected_Ioi
    hd hb hmem (summable_terms m hc hτ) hmem
  have heq : (∑' n, g' n τ) = -c * exponentialSeries (m + 1) c τ := by
    simp only [g', exponentialSeries, mul_assoc, tsum_mul_left]
  rw [heq] at h
  exact h

/-- Exactly the density in the printed Laplace scaling, with the fixed y-power. -/
def laplaceDensity (k : ℕ) (τ y : ℝ) : ℝ :=
  (2 * (2 * Real.pi)^(2 * k) / (Nat.factorial (2 * k) : ℝ)) *
    y^(2 * k + 1) * exponentialSeries (2 * k) (2 * Real.pi * y) τ

theorem laplaceDensity_one (k : ℕ) (y : ℝ) :
    laplaceDensity k 1 y = ManuscriptChain.Hyperbolic.density k y := by
  simp only [laplaceDensity, exponentialSeries, ManuscriptChain.Hyperbolic.density,
    ManuscriptChain.Hyperbolic.exponentialTerm, mul_one]

/-- Actual pointwise density derivative, valid for every positive scale and y. -/
theorem laplaceDensity_hasDerivAt (k : ℕ) {τ y : ℝ}
    (hτ : 0 < τ) (hy : 0 < y) :
    HasDerivAt (fun t => laplaceDensity k t y)
      ((2 * (2 * Real.pi)^(2 * k) / (Nat.factorial (2 * k) : ℝ)) *
        y^(2 * k + 1) *
        (-(2 * Real.pi * y) * exponentialSeries (2 * k + 1) (2 * Real.pi * y) τ)) τ :=
  (exponentialSeries_hasDerivAt (2 * k) (by positivity : 0 < 2 * Real.pi * y) hτ).const_mul _

end LeanPaper.LaplaceDensityDerivative

#print axioms LeanPaper.LaplaceDensityDerivative.exponentialSeries_hasDerivAt
#print axioms LeanPaper.LaplaceDensityDerivative.laplaceDensity_hasDerivAt
