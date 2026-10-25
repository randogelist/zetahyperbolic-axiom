import PaperChain.Stage09

/-!
Stage 10: Dirichlet beta parity sign cancellation. Importantly, the
raw product of the character and Vandermonde signs is (-1)^N, and hence
positivity of γ_j still requires the global orientation factor when N is odd.
The beta/zeta analytic and q-adic endpoints remain open.
-/

namespace PaperChain

/-- Exact character-by-Vandermonde sign is independent of pole index j.
Any unconditional claim of strictly positive γ requires the missing
orientation/global-factor argument when N is odd. -/
theorem stage10_character_vandermonde_sign (N j : ℕ) (hNj : N ≤ j) :
    (-1 : ℤ) ^ j * (-1 : ℤ) ^ (j - N) = (-1 : ℤ) ^ N := by
  have hj : j = N + (j - N) := (Nat.add_sub_of_le hNj).symm
  have hbase : (-1 : ℤ) ^ j = (-1 : ℤ) ^ N * (-1 : ℤ) ^ (j - N) := by
    calc
      (-1 : ℤ) ^ j = (-1 : ℤ) ^ (N + (j - N)) :=
        congrArg (fun n : ℕ => (-1 : ℤ) ^ n) hj
      _ = (-1 : ℤ) ^ N * (-1 : ℤ) ^ (j - N) := by
        rw [pow_add]
  calc
    (-1 : ℤ) ^ j * (-1 : ℤ) ^ (j - N) =
        (-1 : ℤ) ^ N * (-1 : ℤ) ^ (j - N) * (-1 : ℤ) ^ (j - N) := by
          rw [hbase]
    _ = (-1 : ℤ) ^ N * ((-1 : ℤ) ^ (j - N)) ^ 2 := by ring
    _ = (-1 : ℤ) ^ N := by
      have hpow : ((-1 : ℤ) ^ (j - N)) ^ 2 = 1 := by
        rw [← pow_mul, show (j - N) * 2 = 2 * (j - N) by omega, pow_mul]
        norm_num
      simp [hpow]

/-- Even starting pole-index N gives a genuinely positive sign product. -/
theorem stage10_even_start_positive (N j : ℕ) (hNj : N ≤ j)
    (hN : Even N) :
    (-1 : ℤ) ^ j * (-1 : ℤ) ^ (j - N) = 1 := by
  rw [stage10_character_vandermonde_sign N j hNj, hN.neg_one_pow]

/-- A rigorous slot for the separate zeta-beta rational approximation claim.
The convergence constant must be linked to actual Padé approximants. -/
def BetaPadeRate (error : ℕ → ℝ) (C : ℝ) : Prop :=
  0 < C ∧ ∀ h, |error h| ≤ C * (3 + 2 * Real.sqrt 2) ^ (-(2 * (h : ℤ)))

end PaperChain
