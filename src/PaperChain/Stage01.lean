import Zetahyperbolic.Section2Checked

/-!
Stage 1: actual Section 2 finite simple-pole functional, from the frozen
Section2Checked input. Removes the unnecessary r != 1 restriction in the
previous integer-pole difference theorem; r = 0 remains legitimately excluded.
The full rational-function lift from the generating function is not asserted.
-/

open scoped BigOperators
open Polynomial
namespace PaperChain

open Zetahyperbolic

theorem stage01_pullback_monomial (k e : ℕ) (hk : 1 ≤ k) :
    muMonomial k e = (-1 : ℚ) ^ e * tauMonomial k (2 * e + 2 * k + 1) :=
  pullback_identity_monomial k e hk

theorem stage01_pullback_simple_pole (k j : ℕ) (hk : 1 ≤ k) (hj : 1 ≤ j) :
    muPolePoly k j =
      C (-tauMonomial k (2 * k - 1)) -
        C ((j : ℚ) ^ (2 * k) / 2) *
          (tauPolePoly k (j : ℤ) + tauPolePoly k (-(j : ℤ))) :=
  pullback_identity_pole k j hk hj

theorem stage01_tau_reflection_monomial (k d : ℕ) (hk : 1 ≤ k) :
    (-1 : ℚ) ^ d *
      (∑ i ∈ Finset.range (d + 1), (Nat.choose d i : ℚ) * tauMonomial k i) =
        -tauMonomial k d :=
  tau_reflection_monomial k d hk

theorem stage01_tau_reflection_pole (k : ℕ) (r : ℤ) :
    -tauPolePoly k (-1 - r) = -tauPolePoly k r :=
  tau_reflection_pole k r

/-- The original certified lemma covered r != 0,1. Here the r=1 case is
resolved using H_0=0 and H_1=1, so the paper's entire r != 0 domain is covered. -/
theorem stage01_tau_difference_all_nonzero (k : ℕ) (r : ℤ) (hr : r ≠ 0) :
    tauPolePoly k (r - 1) - tauPolePoly k r =
      C (-((r : ℚ) ^ (2 * k + 1))⁻¹) := by
  by_cases hr1 : r = 1
  · subst r
    have hH1 : harmonicWeight (2 * k + 1) 1 = 1 := by
      simpa [harmonicWeight_zero] using harmonicWeight_succ (2 * k + 1) 0
    simp [tauPolePoly, dIndex, harmonicWeight_zero, hH1] <;> ring
  · exact tau_difference_pole k r hr hr1

end PaperChain
