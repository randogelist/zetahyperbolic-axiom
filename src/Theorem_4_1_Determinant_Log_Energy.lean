import Theorem_4_1_Leading_Coefficient_Gap
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Linarith

/-!
# Exact finite-K log-energy conservation for the ORIGINAL primitive pencil

This is a manuscript-connected algebraic identity, not an asymptotic input:

  log |LC(P)| + (-log P(zeta(s))) = log |det M| - log det G.

The Gram determinant is strictly positive and the primitive evaluation is
strictly positive on every admissible parameter. The required limit/rate
estimates in Section 4/6/8 are still explicit hypotheses. The criterion
below reduces the rate problem to bounds on THREE ACTUAL LOGARITHMS.
-/

noncomputable section

namespace ManuscriptChain.FiniteEnergy

open GeneralIrrationality LeadingCoefficientGap

/-- Actual primitive leading coefficient, on the logarithmic scale. -/
def leadingLog (p : Real.Parameters) : ℝ :=
  _root_.Real.log (leadingSize p)

/-- Actual positive-definite Bose--Einstein Gram determinant, log scale. -/
def gramLog (p : Real.Parameters) : ℝ :=
  _root_.Real.log ((Real.gram p (Real.zeta p.weight)).det)

/-- Absolute determinant of the exact simple-pole derivative, log scale. -/
def derivativeLog (p : Real.Parameters) : ℝ :=
  _root_.Real.log |(Real.derivativeMatrix p).det|

/-- Spectral determinant energy, without assigning any conjectural limit. -/
def determinantEnergy (p : Real.Parameters) : ℝ :=
  derivativeLog p - gramLog p

/-- Decay exponent of the ACTUAL primitive polynomial at the odd-zeta center. -/
def valueDecayLog (p : Real.Parameters) : ℝ :=
  -_root_.Real.log
    (RealTransfer.evalReal (primitivePolynomial p) (Real.zeta p.weight))

/-- Exact log decomposition of the concrete evaluated primitive polynomial. -/
theorem primitive_eval_log_identity (p : Real.Parameters) (hp : Real.Admissible p) :
    _root_.Real.log
      (RealTransfer.evalReal (primitivePolynomial p) (Real.zeta p.weight)) =
      _root_.Real.log (leadingSize p) +
      _root_.Real.log ((Real.gram p (Real.zeta p.weight)).det) -
      _root_.Real.log |(Real.derivativeMatrix p).det| := by
  have hleading : 0 < leadingSize p :=
    lt_of_lt_of_le (by norm_num) (leadingSize_ge_one p)
  have hgram : 0 < (Real.gram p (Real.zeta p.weight)).det :=
    (GRAM_POSITIVE p hp).det_pos
  have hslope : 0 < |(Real.derivativeMatrix p).det| :=
    abs_pos.mpr (General.derivative_nonsingular p)
  calc
    _ = _root_.Real.log (leadingSize p * determinantRatio p) := by
      rw [primitivePolynomial_eval_eq]
    _ = _root_.Real.log (leadingSize p) +
          _root_.Real.log (determinantRatio p) := by
      rw [_root_.Real.log_mul hleading.ne' (determinantRatio_pos p hp).ne']
    _ = _root_.Real.log (leadingSize p) +
          _root_.Real.log ((Real.gram p (Real.zeta p.weight)).det) -
          _root_.Real.log |(Real.derivativeMatrix p).det| := by
      rw [determinantRatio, _root_.Real.log_div hgram.ne' hslope.ne']
      ring

/-- Exact FINITE-K potential conservation; no asymptotic assumptions. -/
theorem finite_potential_conservation (p : Real.Parameters)
    (hp : Real.Admissible p) :
    leadingLog p + valueDecayLog p = determinantEnergy p := by
  dsimp [leadingLog, valueDecayLog, determinantEnergy, derivativeLog, gramLog]
  rw [primitive_eval_log_identity p hp]
  ring

/-- Same conservation law after K² normalization (valid even for K=0). -/
theorem finite_potential_conservation_per_K_sq (p : Real.Parameters)
    (hp : Real.Admissible p) :
    leadingLog p / ((p.K : ℝ) ^ 2) +
      valueDecayLog p / ((p.K : ℝ) ^ 2) =
      determinantEnergy p / ((p.K : ℝ) ^ 2) := by
  rw [← add_div]
  exact congrArg (fun x : ℝ => x / ((p.K : ℝ) ^ 2))
    (finite_potential_conservation p hp)

/-- For admissible pencils the ONE OPEN normalized decay premise is equivalent
  to a strictly positive quadratic gap between actual determinant energy and
  actual primitive leading-coefficient height. Neither direction assumes RH,
  irrationality or an artificial growth estimate. -/
theorem normalizedQuadraticDecay_iff_energy_gap
    (p : ℕ → Real.Parameters) (hp : ∀ n, Real.Admissible (p n)) :
    NormalizedQuadraticDecay p ↔
      ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ, ∀ n, n₀ ≤ n →
        leadingLog (p n) - determinantEnergy (p n) ≤
          -c * ((p n).K : ℝ) ^ 2 := by
  constructor
  · rintro ⟨c, hc, n₀, hupper⟩
    refine ⟨c, hc, n₀, ?_⟩
    intro n hn
    have hpositive := primitivePolynomial_eval_pos (p n) (hp n)
    have hlog :
        _root_.Real.log
          (RealTransfer.evalReal (primitivePolynomial (p n))
            (Real.zeta (p n).weight)) ≤
          -c * ((p n).K : ℝ) ^ 2 := by
      calc
        _ ≤ _root_.Real.log (_root_.Real.exp (-c * ((p n).K : ℝ) ^ 2)) :=
          _root_.Real.log_le_log hpositive (hupper n hn)
        _ = _ := _root_.Real.log_exp _
    have hconserve := finite_potential_conservation (p n) (hp n)
    dsimp [valueDecayLog] at hconserve
    linarith
  · rintro ⟨c, hc, n₀, hgap⟩
    refine ⟨c, hc, n₀, ?_⟩
    intro n hn
    have hconserve := finite_potential_conservation (p n) (hp n)
    dsimp [valueDecayLog] at hconserve
    have hlog :
        _root_.Real.log
          (RealTransfer.evalReal (primitivePolynomial (p n))
            (Real.zeta (p n).weight)) ≤
          -c * ((p n).K : ℝ) ^ 2 := by
      have hbound := hgap n hn
      linarith
    have hexp := _root_.Real.exp_le_exp.mpr hlog
    simpa only [_root_.Real.exp_log
      (primitivePolynomial_eval_pos (p n) (hp n))] using hexp

/-- Three *concrete* logarithmic determinant/height bounds suffice for decay.
  Their strict numerical separation remains to be proved independently. -/
theorem normalizedQuadraticDecay_of_three_log_rates
    (p : ℕ → Real.Parameters) (hp : ∀ n, Real.Admissible (p n))
    (A B C : ℝ) (hABC : A + B < C) (n₀ : ℕ)
    (hleading : ∀ n, n₀ ≤ n →
      leadingLog (p n) ≤ A * ((p n).K : ℝ) ^ 2)
    (hgram : ∀ n, n₀ ≤ n →
      gramLog (p n) ≤ B * ((p n).K : ℝ) ^ 2)
    (hderivative : ∀ n, n₀ ≤ n →
      C * ((p n).K : ℝ) ^ 2 ≤ derivativeLog (p n)) :
    NormalizedQuadraticDecay p := by
  apply (normalizedQuadraticDecay_iff_energy_gap p hp).2
  refine ⟨C - (A + B), sub_pos.mpr hABC, n₀, ?_⟩
  intro n hn
  have hL := hleading n hn
  have hG := hgram n hn
  have hD := hderivative n hn
  dsimp [leadingLog] at hL
  dsimp [gramLog] at hG
  dsimp [derivativeLog] at hD
  dsimp [leadingLog, determinantEnergy, derivativeLog, gramLog]
  nlinarith

end ManuscriptChain.FiniteEnergy
