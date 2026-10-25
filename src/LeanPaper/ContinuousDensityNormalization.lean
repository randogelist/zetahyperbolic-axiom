import LeanPaper.RebuildKernelBridge
import MAIN_CHAIN_ASSEMBLED
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Normalization correction in Proposition 3.2 (PDF pp. 7–8)

Equation (3.1) has coefficient `2 (2π)^(2k)/(2k)!`. The continuous
coefficient printed in Proposition 3.2 is `(2π)^s/(2 Γ(s))`; it is `π/2`
times that coefficient at `s=2k+1`. Thus the claimed coincidence of pencils
at odd integers is false as printed. The corrected coefficient is
`2 (2π)^(s-1)/Γ(s)`. This module retains both definitions and proves their
exact odd specializations, including an actual matrix-entry discrepancy.
-/
noncomputable section
open scoped BigOperators
open MeasureTheory Set
namespace LeanPaper.ContinuousDensityNormalization
open ManuscriptChain

def exponentialTerm (s : ℝ) (n : ℕ) (y : ℝ) : ℝ :=
  ((n + 1 : ℕ) : ℝ) ^ (s - 1) *
    _root_.Real.exp (-(2 * _root_.Real.pi * y) * ((n + 1 : ℕ) : ℝ))

def printedDensity (s y : ℝ) : ℝ :=
  (2 * _root_.Real.pi) ^ s / (2 * _root_.Real.Gamma s) *
    y ^ s * ∑' n : ℕ, exponentialTerm s n y

def correctedDensity (s y : ℝ) : ℝ :=
  (2 * (2 * _root_.Real.pi) ^ (s - 1) / _root_.Real.Gamma s) *
    y ^ s * ∑' n : ℕ, exponentialTerm s n y

theorem correctedDensity_odd (k : ℕ) (y : ℝ) :
    correctedDensity (2 * (k : ℝ) + 1) y = Hyperbolic.density k y := by
  simp only [correctedDensity, exponentialTerm, add_sub_cancel_right]
  rw [show 2 * (k : ℝ) = ((2 * k : ℕ) : ℝ) by push_cast; rfl]
  simp only [_root_.Real.Gamma_nat_eq_factorial]
  rw [show ((2 * k : ℕ) : ℝ) + 1 = ((2 * k + 1 : ℕ) : ℝ) by push_cast; rfl]
  simp only [_root_.Real.rpow_natCast, _root_.Real.Gamma_nat_eq_factorial]
  rfl

theorem printedDensity_odd (k : ℕ) (y : ℝ) :
    printedDensity (2 * (k : ℝ) + 1) y =
      (_root_.Real.pi / 2) * Hyperbolic.density k y := by
  simp only [printedDensity, exponentialTerm, add_sub_cancel_right]
  rw [show 2 * (k : ℝ) = ((2 * k : ℕ) : ℝ) by push_cast; rfl]
  simp only [_root_.Real.Gamma_nat_eq_factorial]
  rw [show ((2 * k : ℕ) : ℝ) + 1 = ((2 * k + 1 : ℕ) : ℝ) by push_cast; rfl]
  simp only [_root_.Real.rpow_natCast, _root_.Real.Gamma_nat_eq_factorial,
    Hyperbolic.density, Hyperbolic.exponentialTerm, pow_succ]
  ring

theorem printedDensity_ne_odd (k : ℕ) {y : ℝ} (hy : 0 < y) :
    printedDensity (2 * (k : ℝ) + 1) y ≠ Hyperbolic.density k y := by
  rw [printedDensity_odd]
  intro h
  have hd := Hyperbolic.density_pos k hy
  have hp : 0 < _root_.Real.pi / 2 - 1 := by linarith [_root_.Real.pi_gt_three]
  have hprod := mul_pos hp hd
  nlinarith

def printedMoment (p : Real.Parameters) (s : ℝ) (i j : Fin p.h) : ℝ :=
  ∫ y : ℝ in Ioi 0,
    ((Zetahyperbolic.D_real p.N (y ^ 2)) ^ (2 * p.m) * y ^ (2 * (i.val + j.val)) /
      Zetahyperbolic.D_real p.K (y ^ 2)) * printedDensity s y

theorem printedMoment_odd (p : Real.Parameters) (hp : Real.Admissible p) (i j : Fin p.h) :
    printedMoment p (2 * (p.k : ℝ) + 1) i j =
      (_root_.Real.pi / 2) * Real.gram p (Real.zeta p.weight) i j := by
  unfold printedMoment
  simp_rw [printedDensity_odd]
  rw [Hyperbolic.gram_eq_weighted_integral p hp
    (Hyperbolic.poleIntegralIdentity p.k hp.k_pos) i j, ← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro y _
  unfold ConcreteMoment.weightedDensity
  ring

theorem printedMoment_diagonal_ne (p : Real.Parameters) (hp : Real.Admissible p)
    (i : Fin p.h) :
    printedMoment p (2 * (p.k : ℝ) + 1) i i ≠
      Real.gram p (Real.zeta p.weight) i i := by
  rw [printedMoment_odd p hp]
  intro h
  have hpos := (GRAM_POSITIVE p hp).diag_pos (i := i)
  have hpi : 0 < _root_.Real.pi / 2 - 1 := by linarith [_root_.Real.pi_gt_three]
  have hprod := mul_pos hpi hpos
  nlinarith

end LeanPaper.ContinuousDensityNormalization
