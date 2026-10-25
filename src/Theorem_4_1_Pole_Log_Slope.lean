import Theorem_4_1_Determinant_Log_Energy
import Theorem_2_5_Lagrange_Pole_Diagonalization

/-!
# Stage 08: finite, exact decomposition of the actual slope determinant

The Lagrange-pole diagonalization of Section 2 gives
    det M = det(V)^2 * prod_a gamma_a.
This module transports that RATIONAL determinant factorization into the
REAL logarithmic energy entering Section 4. No asymptotic hypothesis is used
for any equality below. A separate conditional estimate uses ACTUAL finite
pole products, Gram determinants and primitive leading coefficients.

Nothing here proves a quadratic rate gap, an Euler--Maclaurin estimate,
or irrationality of zeta(5) without the displayed quantitative hypotheses.
-/

noncomputable section
open scoped BigOperators

namespace ManuscriptChain.PoleLogSlope

open LeadingCoefficientGap GeneralIrrationality FiniteEnergy PoleDiagonalization

/-- Absolute Vandermonde determinant at the negative-square poles. -/
def vandermondeSize (p : Real.Parameters) : ℝ :=
  |((poleVandermonde p).det : ℝ)|

/-- Absolute value of the product of the EXACT rational residue weights. -/
def poleProductSize (p : Real.Parameters) : ℝ :=
  |((∏ a : Fin p.h, poleWeight p a : ℚ) : ℝ)|

/-- The Vandermonde factor never vanishes, for any parameter tuple. -/
theorem vandermondeSize_pos (p : Real.Parameters) :
    0 < vandermondeSize p := by
  unfold vandermondeSize
  apply abs_pos.mpr
  exact_mod_cast poleVandermonde_det_ne_zero p

/-- Every residue weight is nonzero, including the empty product case. -/
theorem poleProductSize_pos (p : Real.Parameters) :
    0 < poleProductSize p := by
  unfold poleProductSize
  apply abs_pos.mpr
  have hq : (∏ a : Fin p.h, poleWeight p a) ≠ (0 : ℚ) :=
    Finset.prod_ne_zero_iff.mpr (fun a _ => poleWeight_ne_zero p a)
  exact_mod_cast hq

/-- Exact original real matrix determinant as an un-normalized pole product.
This does not use matrix eigenvalues or any decay estimates. -/
theorem real_derivative_det_pole_product (p : Real.Parameters) :
    (Real.derivativeMatrix p).det =
      ((poleVandermonde p).det : ℝ) ^ 2 *
        ((∏ a : Fin p.h, poleWeight p a : ℚ) : ℝ) := by
  have hrat :
      (((rationalDerivativeMatrix p).det : ℚ) : ℝ) =
        ((poleVandermonde p).det : ℝ) ^ 2 *
          ((∏ a : Fin p.h, poleWeight p a : ℚ) : ℝ) := by
    exact_mod_cast rationalDerivativeMatrix_det p
  calc
    (Real.derivativeMatrix p).det =
        (((rationalDerivativeMatrix p).det : ℚ) : ℝ) := by
      rw [Rat.cast_det]
      rfl
    _ = _ := hrat

/-- No sign guess: the absolute determinant factors into two positive sizes. -/
theorem derivative_abs_pole_product (p : Real.Parameters) :
    |(Real.derivativeMatrix p).det| =
      vandermondeSize p ^ 2 * poleProductSize p := by
  unfold vandermondeSize poleProductSize
  rw [real_derivative_det_pole_product, abs_mul, abs_pow]

/-- Exact logarithmic slope formula for the actual finite Lagrange pencil:
log |det M| = 2 log |det V| + log |prod gamma_a|. -/
theorem derivative_log_pole_split (p : Real.Parameters) :
    derivativeLog p =
      2 * _root_.Real.log (vandermondeSize p) +
        _root_.Real.log (poleProductSize p) := by
  unfold derivativeLog
  rw [derivative_abs_pole_product]
  rw [_root_.Real.log_mul (pow_pos (vandermondeSize_pos p) 2).ne'
    (poleProductSize_pos p).ne']
  rw [show vandermondeSize p ^ 2 =
    vandermondeSize p * vandermondeSize p by ring]
  rw [_root_.Real.log_mul (vandermondeSize_pos p).ne'
    (vandermondeSize_pos p).ne']
  ring

/-- Exact finite-K conservation expressed using explicitly finite pole data. -/
theorem finite_energy_pole_product (p : Real.Parameters)
    (hp : Real.Admissible p) :
    leadingLog p + valueDecayLog p =
      (2 * _root_.Real.log (vandermondeSize p) +
        _root_.Real.log (poleProductSize p)) - gramLog p := by
  rw [finite_potential_conservation p hp]
  unfold determinantEnergy
  rw [derivative_log_pole_split]

/-- The actual quadratic decay follows from four *named*, independently
verifiable real bounds, after the slope determinant is eliminated in favor
of its exact Lagrange pole product. The strict inequality and each uniform
bound are OPEN INPUTS, not assertions proved by this module. -/
theorem normalizedQuadraticDecay_of_pole_log_rates
    (p : ℕ → Real.Parameters) (hp : ∀ n, Real.Admissible (p n))
    (A B C D : ℝ) (hgap : A + B < 2 * C + D) (n₀ : ℕ)
    (hleading : ∀ n, n₀ ≤ n →
      leadingLog (p n) ≤ A * ((p n).K : ℝ) ^ 2)
    (hgram : ∀ n, n₀ ≤ n →
      gramLog (p n) ≤ B * ((p n).K : ℝ) ^ 2)
    (hvandermonde : ∀ n, n₀ ≤ n →
      C * ((p n).K : ℝ) ^ 2 ≤
        _root_.Real.log (vandermondeSize (p n)))
    (hpoles : ∀ n, n₀ ≤ n →
      D * ((p n).K : ℝ) ^ 2 ≤
        _root_.Real.log (poleProductSize (p n))) :
    NormalizedQuadraticDecay p := by
  apply normalizedQuadraticDecay_of_three_log_rates p hp
    A B (2 * C + D) hgap n₀ hleading hgram
  intro n hn
  rw [derivative_log_pole_split]
  have hv := hvandermonde n hn
  have hw := hpoles n hn
  linarith

end ManuscriptChain.PoleLogSlope
