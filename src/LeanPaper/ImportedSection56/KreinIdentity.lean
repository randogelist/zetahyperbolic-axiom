import LeanPaper.ImportedSection56.DualAffineAlgebra
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# Principal Theorem 5.2(2): exact weight-seven Krein polarization

We prove the finite algebra at the heart of the paper's genuine two-variable
weight-seven kernel, including every binomial coefficient, its 1/1440
normalization, and bilinear polarization. The finite identities are exact
for arbitrary real moment channels. The infinite identity is proved for
summable mode sequences by termwise equality, not by silently dropping
uncontrolled modes.

An analytic Fubini/Tonelli bridge identifying these channels with the
actual integrals remains a separate theorem; the finite identities alone
do NOT prove polynomial positive/negative cones of Theorem 5.2(3).
-/

noncomputable section
open scoped BigOperators
namespace PaperOrder.PrincipalTheorems

/-- The six-term binomial pairing of the logarithmic weight-five kernel. -/
def weightSevenPairing (a b : ℕ → ℝ) : ℝ :=
  (1 / 720 : ℝ) *
    ∑ ν ∈ Finset.range 6, (Nat.choose 5 ν : ℝ) * a ν * b (5 - ν)

/-- Three paired plus/minus channels: genuine 1/1440 prefactor. -/
def weightSevenKreinPairing (a b : ℕ → ℝ) : ℝ :=
  (1 / 1440 : ℝ) *
    ∑ ν ∈ Finset.range 3, (Nat.choose 5 ν : ℝ) *
      ((a ν + a (5 - ν)) * (b ν + b (5 - ν)) -
       (a ν - a (5 - ν)) * (b ν - b (5 - ν)))

/-- An exact instance of the binomial identity used before Krein pairing. -/
theorem weightSeven_binomial (u v : ℝ) :
    (u + v) ^ 5 =
      ∑ ν ∈ Finset.range 6,
        (Nat.choose 5 ν : ℝ) * u ^ ν * v ^ (5 - ν) := by
  norm_num [Finset.sum_range_succ, Nat.choose]
  <;> ring

/-- The full six-channel identity, bilinear in TWO independent inputs. -/
theorem weightSeven_Krein_bilinear (a b : ℕ → ℝ) :
    weightSevenPairing a b = weightSevenKreinPairing a b := by
  unfold weightSevenPairing weightSevenKreinPairing
  norm_num [Finset.sum_range_succ, Nat.choose]
  <;> ring

/-- Quadratic version: exactly the difference of weighted squares. -/
theorem weightSeven_Krein_quadratic (a : ℕ → ℝ) :
    weightSevenPairing a a =
      (1 / 1440 : ℝ) *
        ∑ ν ∈ Finset.range 3, (Nat.choose 5 ν : ℝ) *
          ((a ν + a (5 - ν)) ^ 2 - (a ν - a (5 - ν)) ^ 2) := by
  simpa only [weightSevenKreinPairing, pow_two] using
    (weightSeven_Krein_bilinear a a)

/-- Exact cutoff identity for ANY number of modes. -/
theorem weightSeven_Krein_finite_modes
    (M : ℕ) (a b : ℕ → ℕ → ℝ) :
    (∑ m ∈ Finset.range M, weightSevenPairing (a m) (b m)) =
      ∑ m ∈ Finset.range M, weightSevenKreinPairing (a m) (b m) := by
  apply Finset.sum_congr rfl
  intro m hm
  exact weightSeven_Krein_bilinear (a m) (b m)

/-- The infinite algebra is valid whenever the mode series is summable.
This does not itself prove the analytic representation of the kernel. -/
theorem weightSeven_Krein_infinite_modes
    (a b : ℕ → ℕ → ℝ)
    (hsum : Summable (fun m => weightSevenPairing (a m) (b m))) :
    Summable (fun m => weightSevenKreinPairing (a m) (b m)) ∧
      (∑' m, weightSevenPairing (a m) (b m)) =
        ∑' m, weightSevenKreinPairing (a m) (b m) := by
  have hfun : (fun m : ℕ => weightSevenPairing (a m) (b m)) =
      (fun m : ℕ => weightSevenKreinPairing (a m) (b m)) := by
    funext m
    exact weightSeven_Krein_bilinear (a m) (b m)
  constructor
  · rw [← hfun]
    exact hsum
  · rw [hfun]

end PaperOrder.PrincipalTheorems

#print axioms PaperOrder.PrincipalTheorems.weightSeven_binomial
#print axioms PaperOrder.PrincipalTheorems.weightSeven_Krein_bilinear
#print axioms PaperOrder.PrincipalTheorems.weightSeven_Krein_quadratic
#print axioms PaperOrder.PrincipalTheorems.weightSeven_Krein_infinite_modes
