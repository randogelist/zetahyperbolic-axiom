import Mathlib.Tactic
import Mathlib.NumberTheory.Padics.PadicVal.Basic

/-!
# Theorem 6.17: an obstruction to the printed local-index argument

The manuscript defines `H_M^(beta,s)` using the first `M` odd denominators,
not using odd denominators bounded by `M`.  Its proof of 6.17(3)(ii)
confuses those two cutoffs.  The permitted choice `q=11, rho=3` already
puts the denominator 11 into the alleged integral lower block.

This disproves that intermediate arithmetic assertion, not the full
conditional theorem. A corrected local block computation is required.
-/
namespace LeanPaper.BetaHarmonicIndexObstruction

/-- The manuscript's alternating odd harmonic sum. -/
def oddHarmonic (s M : ℕ) : ℚ :=
  ∑ j ∈ Finset.range M, (-1 : ℚ)^j / ((2*j+1 : ℕ) : ℚ)^s

/-- All the local-index hypotheses in the printed argument hold. -/
theorem permitted_lower_index : Nat.Prime 11 ∧ 3 < (11-1)/2 ∧
    2*3 ≤ 11-3 ∧ 2*3 < 11 := by norm_num

/-- Nevertheless the q-divisible odd denominator is already in the lower sum. -/
theorem lower_sum_contains_pole : 5 ∈ Finset.range (2*3) ∧ 2*5+1=11 := by norm_num

/-- Exact rational value avoids any numerical or floating-point inference. -/
theorem oddHarmonic_two_six : oddHarmonic 2 6 = (10956424 : ℚ)/12006225 := by
  norm_num [oddHarmonic, Finset.sum_range_succ]

/-- In reduced form the denominator has an 11-factor, and the numerator does not. -/
theorem lower_sum_not_eleven_integral :
    11 ∣ (oddHarmonic 2 6).den ∧ ¬ (11 : ℤ) ∣ (oddHarmonic 2 6).num := by
  norm_num [oddHarmonic, Finset.sum_range_succ]

/-- The top-weight beta-only moment used by the displayed universal pencil. -/
def betaTwoMoment (n l : ℕ) : ℚ :=
  if n=l then -oddHarmonic 2 (2*n)
  else (oddHarmonic 1 (2*n) - oddHarmonic 1 (2*l)) /
    (4*((n : ℚ)-l))

/-- The manuscript basis vector `x^(4*rho)+2*x^(4*(rho+(q+1)/2))`. -/
def betaTwoBasisDiagonal (q rho : ℕ) : ℚ :=
  betaTwoMoment rho rho + 4*betaTwoMoment (rho+(q+1)/2) (rho+(q+1)/2) +
    4*betaTwoMoment rho (rho+(q+1)/2)

/-- A permitted prime makes the corrected leading diagonal coefficient vanish. -/
theorem forty_one_leading_cancellation : Nat.Prime 41 ∧ 41 > 2+5 ∧
    (5*(3 : ℤ)^2-4)=41 := by norm_num

/-- An exact finite arithmetic obstruction to the printed scalar-block calculation. -/
theorem forty_one_diagonal_pole_drop :
    ¬ 41 ∣ ((41 : ℚ)*betaTwoBasisDiagonal 41 11).den ∧
    ¬ (41 : ℤ) ∣ ((41 : ℚ)*betaTwoBasisDiagonal 41 11).num := by
  norm_num [betaTwoBasisDiagonal, betaTwoMoment, oddHarmonic, Finset.sum_range_succ]

/-- The error is in the integer cutoff itself, independently of the exponent. -/
theorem odd_denominator_membership (q M : ℕ) (hq : Odd q)
    (hM : (q-1)/2 < M) :
    ∃ j ∈ Finset.range M, 2*j+1=q := by
  obtain ⟨a, rfl⟩ := hq
  refine ⟨a, ?_, ?_⟩
  · exact Finset.mem_range.mpr (by omega)
  · omega

end LeanPaper.BetaHarmonicIndexObstruction
