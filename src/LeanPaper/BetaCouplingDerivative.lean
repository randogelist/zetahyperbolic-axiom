import LeanPaper.CentralFactorialSecant

/-!
# Correction to the displayed beta coupling in Theorem 6.4(1)

The literal printed differential operator is `D - (4/pi^2) D^3`.
On `1/(2 cosh(pi*y/2))` it is negative for positive `y`. Its printed
positive closed form instead requires multiplying that operator by `-pi`.
This is independent of the valid odd-square residue sign cancellation.
-/

noncomputable section

namespace LeanPaper.BetaCouplingDerivative
open CentralFactorialSecant

lemma halfSech_differentiable : Differentiable ℝ halfSech := by
  intro z
  exact ((hasDerivAt_sechPower 1 z).const_mul (1 / 2 : ℝ)).differentiableAt

lemma halfSech_deriv_differentiable : Differentiable ℝ (deriv halfSech) := by
  unfold halfSech
  rw [deriv_const_mul_sech, deriv_sechPower]
  intro z
  exact ((((Real.hasDerivAt_sinh z).const_mul (-(1 : ℝ))).mul
    (hasDerivAt_sechPower 2 z)).const_mul (1 / 2 : ℝ)).differentiableAt

lemma halfSech_second : deriv (deriv halfSech) =
    fun z => halfSech z - sechPower 3 z := by
  unfold halfSech
  rw [deriv_twice_const_mul_sech]
  funext z
  norm_num <;> ring

lemma halfSech_second_differentiable :
    Differentiable ℝ (deriv (deriv halfSech)) := by
  rw [halfSech_second]
  exact halfSech_differentiable.sub
    (fun z => (hasDerivAt_sechPower 3 z).differentiableAt)

lemma halfSech_third : deriv (deriv (deriv halfSech)) =
    fun z => deriv halfSech z - deriv (sechPower 3) z := by
  rw [halfSech_second]
  funext z
  exact deriv_sub (halfSech_differentiable z)
    (hasDerivAt_sechPower 3 z).differentiableAt

lemma deriv_scale (f : ℝ → ℝ) (hf : Differentiable ℝ f) (a : ℝ) :
    deriv (fun y => f (a * y)) = fun y => a * deriv f (a * y) := by
  funext y
  have h := ((hf (a * y)).hasDerivAt).comp y (hasDerivAt_const_mul a)
  simpa only [Function.comp_def, mul_comm] using h.deriv

lemma deriv_scale_twice (f : ℝ → ℝ) (hf : Differentiable ℝ f)
    (hf' : Differentiable ℝ (deriv f)) (a : ℝ) :
    deriv (deriv (fun y => f (a * y))) =
      fun y => a ^ 2 * deriv (deriv f) (a * y) := by
  rw [deriv_scale f hf]
  funext y
  have hd : DifferentiableAt ℝ (fun y => deriv f (a * y)) y :=
    (hf' (a * y)).comp y (hasDerivAt_const_mul a).differentiableAt
  rw [deriv_const_mul a hd, deriv_scale (deriv f) hf']
  ring

lemma deriv_scale_thrice (f : ℝ → ℝ) (hf : Differentiable ℝ f)
    (hf' : Differentiable ℝ (deriv f))
    (hf'' : Differentiable ℝ (deriv (deriv f))) (a : ℝ) :
    deriv (deriv (deriv (fun y => f (a * y)))) =
      fun y => a ^ 3 * deriv (deriv (deriv f)) (a * y) := by
  rw [deriv_scale_twice f hf hf']
  funext y
  have hd : DifferentiableAt ℝ (fun y => deriv (deriv f) (a * y)) y :=
    (hf'' (a * y)).comp y (hasDerivAt_const_mul a).differentiableAt
  rw [deriv_const_mul (a ^ 2) hd, deriv_scale (deriv (deriv f)) hf'']
  ring

/-- The exact function inside the manuscript's printed differential operator. -/
def scaledHalfSech (y : ℝ) : ℝ := halfSech ((Real.pi / 2) * y)

lemma scaledHalfSech_eq (y : ℝ) :
    scaledHalfSech y = 1 / (2 * Real.cosh (Real.pi * y / 2)) := by
  have he : (Real.pi / 2) * y = Real.pi * y / 2 := by ring
  have hc := (Real.cosh_pos (Real.pi * y / 2)).ne'
  unfold scaledHalfSech halfSech sechPower
  rw [he]
  field_simp [hc] <;> ring

/-- The literal left side of the printed equality in Theorem 6.4(1). -/
def printedCoupledWeight (y : ℝ) : ℝ :=
  y ^ 4 / 24 * (-(4 / Real.pi ^ 2) * deriv (deriv (deriv scaledHalfSech)) y +
    deriv scaledHalfSech y)

/-- Exact correction: the printed operator produces `-pi`, not `pi^2`. -/
theorem printedCoupledWeight_eq (y : ℝ) :
    printedCoupledWeight y =
      -Real.pi * y ^ 4 / 16 * Real.sinh ((Real.pi / 2) * y) *
        (Real.cosh ((Real.pi / 2) * y))⁻¹ ^ 4 := by
  unfold printedCoupledWeight scaledHalfSech
  rw [deriv_scale_thrice halfSech halfSech_differentiable
    halfSech_deriv_differentiable halfSech_second_differentiable,
    deriv_scale halfSech halfSech_differentiable,
    halfSech_third, deriv_sechPower]
  norm_num only [Nat.cast_ofNat]
  have hc := (Real.cosh_pos ((Real.pi / 2) * y)).ne'
  field_simp [Real.pi_ne_zero, hc]
  <;> ring

theorem printedCoupledWeight_neg {y : ℝ} (hy : 0 < y) :
    printedCoupledWeight y < 0 := by
  rw [printedCoupledWeight_eq]
  have hs : 0 < Real.sinh ((Real.pi / 2) * y) :=
    Real.sinh_pos_iff.mpr (by positivity)
  have hc : 0 < Real.cosh ((Real.pi / 2) * y) := Real.cosh_pos _
  have ha : -Real.pi * y ^ 4 / 16 < 0 :=
    div_neg_of_neg_of_pos
      (mul_neg_of_neg_of_pos (neg_neg_of_pos Real.pi_pos) (pow_pos hy 4)) (by norm_num)
  exact mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos ha hs)
    (pow_pos (inv_pos.mpr hc) 4)

/-- Multiplication by `-pi` repairs both the sign and the normalization. -/
theorem correctedCoupledWeight_eq (y : ℝ) :
    -Real.pi * printedCoupledWeight y =
      Real.pi ^ 2 * y ^ 4 / 16 * Real.sinh ((Real.pi / 2) * y) *
        (Real.cosh ((Real.pi / 2) * y))⁻¹ ^ 4 := by
  rw [printedCoupledWeight_eq]
  ring

theorem correctedCoupledWeight_pos {y : ℝ} (hy : 0 < y) :
    0 < -Real.pi * printedCoupledWeight y :=
  mul_pos_of_neg_of_neg (neg_neg_of_pos Real.pi_pos) (printedCoupledWeight_neg hy)

end LeanPaper.BetaCouplingDerivative

#print axioms LeanPaper.BetaCouplingDerivative.printedCoupledWeight_eq
#print axioms LeanPaper.BetaCouplingDerivative.printedCoupledWeight_neg
#print axioms LeanPaper.BetaCouplingDerivative.correctedCoupledWeight_eq
