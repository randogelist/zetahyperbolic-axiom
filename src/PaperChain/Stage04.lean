import PaperChain.Stage03

/-!
Stage 4: theorem 3.4's proposed exact degree profile is entered with
the integer/natural arithmetic separated from the *unproved* equality to
the actual leading principal minor degree. Likewise actual interlacing,
Jacobi, Stieltjes and strict Newton hypotheses remain explicit.
-/

namespace PaperChain

/-- Natural-number version of the rank-law right side. -/
def expectedMinorDegree (r T : ℕ) : ℕ :=
  max 0 (min r (2 * r - T - 1))

theorem stage04_expected_degree_le_size (r T : ℕ) :
    expectedMinorDegree r T ≤ r := by
  simpa [expectedMinorDegree] using Nat.min_le_left r (2 * r - T - 1)

theorem stage04_expected_degree_zero (r T : ℕ)
    (h : 2 * r ≤ T + 1) : expectedMinorDegree r T = 0 := by
  simp [expectedMinorDegree]
  omega

/-- Explicit open manuscript obligation; not assumed as an axiom anywhere.
Degree equality needs a NONCANCELLATION witness, not just vanishing entries. -/
def ExactMinorRankLaw (degree : ℕ → ℕ) (T h : ℕ) : Prop :=
  ∀ r, r ≤ h → degree r = expectedMinorDegree r T

/-- An interlacing statement referring to concrete finite lists of roots. -/
def InterlacesFiniteRootLists (small large : List ℝ) : Prop :=
  ∀ i, i + 1 < small.length → i + 1 < large.length →
    large[i]! ≤ small[i]! ∧ small[i]! ≤ large[i + 1]!

end PaperChain
