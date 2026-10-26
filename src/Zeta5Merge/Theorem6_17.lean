import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.NormNum

/-!
# Theorem 6.17: corrected even-beta index window

For the basis `A_ρ(x) = x^(4ρ) + x^(4(ρ+ℓ))`, use
`h = floor((q+1)/4)`, `ℓ = floor((q+3)/4)` and `K = (q-1)/2`.
The harmonic sum `H_(2n)` has indices `0 ≤ ν < 2n` and odd
 denominators `2ν+1`.  This file checks the precise integer window,
including both congruence classes of odd `q` modulo four.

These are combinatorial theorems.  No q-adic valuation of the complete
matrix or determinant is asserted here: that additionally requires the
harmonic-sum valuation and matrix-congruence arguments.
-/

namespace Zeta5Merge.Theorem6_17

/-- Number of basis rows. -/
def height (q : ℕ) : ℕ := (q + 1) / 4
/-- The parity-dependent shift; it is not always equal to `height q`. -/
def shift (q : ℕ) : ℕ := (q + 3) / 4
/-- Highest index in the polynomial basis, before multiplying by four. -/
def degree (q : ℕ) : ℕ := (q - 1) / 2

/-- Exact parameter relations valid for every odd integer `q ≥ 3`. -/
theorem parameters {q : ℕ} (hq : 3 ≤ q) (hodd : q % 2 = 1) :
    0 < height q ∧ 0 < shift q ∧ height q ≤ shift q ∧
    shift q ≤ height q + 1 ∧
    height q + shift q - 1 = degree q ∧
    2 * degree q + 1 = q := by
  unfold height shift degree
  omega

/-- Both monomial indices of every row lie in `0,...,K`. -/
theorem row_indices {q ρ : ℕ} (hq : 3 ≤ q) (hodd : q % 2 = 1)
    (hρ : ρ < height q) :
    ρ < shift q ∧ ρ < ρ + shift q ∧ ρ + shift q ≤ degree q ∧ degree q < q := by
  unfold height shift degree at *
  omega

/-- The low sum ends before the index of the denominator `q`; the high
sum includes that index but stops before any denominator `2q` or larger. -/
theorem harmonic_windows {q ρ : ℕ} (hq : 3 ≤ q) (hodd : q % 2 = 1)
    (hρ : ρ < height q) :
    2 * ρ ≤ (q - 1) / 2 ∧
    (q - 1) / 2 < 2 * (ρ + shift q) ∧
    2 * (ρ + shift q) ≤ q - 1 := by
  unfold height shift at *
  omega

/-- Every odd denominator of the low harmonic sum is strictly below `q`. -/
theorem low_denominator_lt {q ρ ν : ℕ} (hq : 3 ≤ q) (hodd : q % 2 = 1)
    (hρ : ρ < height q) (hν : ν < 2 * ρ) : 2 * ν + 1 < q := by
  have := harmonic_windows hq hodd hρ
  omega

/-- No denominator in any low harmonic sum is divisible by `q`. -/
theorem low_no_multiple {q ρ ν : ℕ} (hq : 3 ≤ q) (hodd : q % 2 = 1)
    (hρ : ρ < height q) (hν : ν < 2 * ρ) : ¬ q ∣ 2 * ν + 1 := by
  exact Nat.not_dvd_of_pos_of_lt (by omega) (low_denominator_lt hq hodd hρ hν)

/-- In every high sum, the unique index with a `q`-divisible odd
 denominator is `(q-1)/2`, where the denominator is exactly `q`. -/
theorem high_multiple_iff {q ρ ν : ℕ} (hq : 3 ≤ q) (hodd : q % 2 = 1)
    (hρ : ρ < height q) (hν : ν < 2 * (ρ + shift q)) :
    (q ∣ 2 * ν + 1) ↔ ν = (q - 1) / 2 := by
  have hw := harmonic_windows hq hodd hρ
  have heq : 2 * ((q - 1) / 2) + 1 = q := by omega
  constructor
  · intro hdvd
    have hsmall : 2 * ν + 1 < 2 * q := by omega
    have he : 2 * ν + 1 = q := Nat.eq_of_dvd_of_lt_two_mul (by omega) hdvd hsmall
    omega
  · intro he
    rw [he, heq]

/-- Existence and uniqueness, with the high-sum truncation included in
 the predicate. In particular the first high row also contains `q`. -/
theorem high_unique_multiple {q ρ : ℕ} (hq : 3 ≤ q) (hodd : q % 2 = 1)
    (hρ : ρ < height q) :
    ∃! ν : ℕ, ν < 2 * (ρ + shift q) ∧ q ∣ 2 * ν + 1 := by
  have hw := harmonic_windows hq hodd hρ
  refine ⟨(q - 1) / 2, ⟨hw.2.1, ?_⟩, ?_⟩
  · have heq : 2 * ((q - 1) / 2) + 1 = q := by omega
    rw [heq]
  · intro ν hν
    exact (high_multiple_iff hq hodd hρ hν.1).mp hν.2

/-- Every nonzero difference of two allowed monomial indices is a
 `q`-unit at the divisibility level. -/
theorem index_difference_not_dvd {q n l : ℕ} (hq : 3 ≤ q) (hodd : q % 2 = 1)
    (hn : n ≤ degree q) (hl : l ≤ degree q) (hne : n ≠ l) :
    ¬ q ∣ max n l - min n l := by
  have hp := parameters hq hodd
  have hpos : 0 < max n l - min n l := by omega
  have hlt : max n l - min n l < q := by omega
  exact Nat.not_dvd_of_pos_of_lt hpos hlt

/-- The shift itself is nonzero and strictly below `q`. -/
theorem shift_not_dvd {q : ℕ} (hq : 3 ≤ q) (hodd : q % 2 = 1) :
    ¬ q ∣ shift q := by
  have hp := parameters hq hodd
  have hlt : shift q < q := by
    unfold shift
    omega
  exact Nat.not_dvd_of_pos_of_lt hp.2.1 hlt

/-- Supports from different rows never overlap. -/
theorem row_support_disjoint {q ρ σ : ℕ} (hq : 3 ≤ q) (hodd : q % 2 = 1)
    (hρ : ρ < height q) (hσ : σ < height q) (hne : ρ ≠ σ) :
    ρ ≠ σ + shift q ∧ ρ + shift q ≠ σ ∧ ρ + shift q ≠ σ + shift q := by
  have hρ' := row_indices hq hodd hρ
  have hσ' := row_indices hq hodd hσ
  omega

/-- At `q ≡ 1 (mod 4)`, the shift must be `h+1`. -/
theorem shift_mod_four_one {q : ℕ} (hmod : q % 4 = 1) :
    shift q = height q + 1 := by
  unfold shift height
  omega

/-- At `q ≡ 3 (mod 4)`, the shift equals `h`. -/
theorem shift_mod_four_three {q : ℕ} (hmod : q % 4 = 3) :
    shift q = height q := by
  unfold shift height
  omega

/-- Regression for the missed first row of the previous proposed repair. -/
theorem q41_regression :
    height 41 = 10 ∧ shift 41 = 11 ∧ degree 41 = 20 ∧
    ¬ ((41 - 1) / 2 < 2 * height 41) ∧
    (41 - 1) / 2 < 2 * shift 41 := by
  norm_num [height, shift, degree]

#print axioms parameters
#print axioms low_no_multiple
#print axioms high_unique_multiple
#print axioms index_difference_not_dvd
#print axioms q41_regression

end Zeta5Merge.Theorem6_17
