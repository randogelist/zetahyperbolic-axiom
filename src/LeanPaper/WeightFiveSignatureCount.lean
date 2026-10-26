import LeanPaper.SlopeSignature
import Mathlib.Tactic

/-!
# Manuscript 3.3 — actual weight-five normalized signature

For the genuine weight-five family (k=2, m=3, N=3n, K=30n),
the positive and negative inertia of the actual normalized pencil
are floor(27n/2) and ceil(27n/2), respectively.
No root-simplicity, off-diagonal total positivity, or Carleman
determinacy claim is made.
-/

noncomputable section
open QuadraticForm
open ManuscriptChain

namespace LeanPaper.WeightFiveSignatureCount

def weightFiveParameters (n : ℕ) : Real.Parameters :=
  ⟨2, 3, 3 * n, 30 * n⟩

theorem weightFive_admissible (n : ℕ) (hn : 0 < n) :
    Real.Admissible (weightFiveParameters n) := by
  constructor
  · norm_num [weightFiveParameters]
  · norm_num [weightFiveParameters]
  · change 0 < 3 * n
    omega
  · change 3 * n < 30 * n
    omega

theorem weightFive_dimension (n : ℕ) :
    (weightFiveParameters n).h = 27 * n := by
  change 30 * n - 3 * n = 27 * n
  omega

private theorem weightFive_even_floor (n : ℕ) :
    (if Even (3 * n) then (27 * n + 1) / 2 else 27 * n / 2) =
      27 * n / 2 := by
  by_cases h : Even (3 * n)
  · rw [if_pos h]
    have hn : Even n := (Nat.even_mul.mp h).resolve_left (by decide)
    have hh : Even (27 * n) := hn.mul_left 27
    have hm := Nat.even_iff.mp hh
    omega
  · rw [if_neg h]

private theorem weightFive_odd_ceil (n : ℕ) :
    (if Even (3 * n) then 27 * n / 2 else (27 * n + 1) / 2) =
      (27 * n + 1) / 2 := by
  by_cases h : Even (3 * n)
  · rw [if_pos h]
    have hn : Even n := (Nat.even_mul.mp h).resolve_left (by decide)
    have hh : Even (27 * n) := hn.mul_left 27
    have hm := Nat.even_iff.mp hh
    omega
  · rw [if_neg h]

/-- Actual normalized weight-five signature counts, with multiplicities. -/
theorem actual_weightFive_signature_counts (n : ℕ) (hn : 0 < n) :
    sigPos (OperatorNormDisk.whitened
      (Real.manuscriptPencil (weightFiveParameters n))).toQuadraticForm' =
      27 * n / 2 ∧
    sigNeg (OperatorNormDisk.whitened
      (Real.manuscriptPencil (weightFiveParameters n))).toQuadraticForm' =
      (27 * n + 1) / 2 := by
  have h := LeanPaper.SlopeSignature.actual_normalized_signature_counts
    (weightFiveParameters n) (weightFive_admissible n hn)
  constructor
  · calc
      _ = (if Even (weightFiveParameters n).N
          then ((weightFiveParameters n).h + 1) / 2
          else (weightFiveParameters n).h / 2) := h.1
      _ = (if Even (3 * n) then (27 * n + 1) / 2
          else 27 * n / 2) := by
            rw [weightFive_dimension]
            rfl
      _ = 27 * n / 2 := weightFive_even_floor n
  · calc
      _ = (if Even (weightFiveParameters n).N
          then (weightFiveParameters n).h / 2
          else ((weightFiveParameters n).h + 1) / 2) := h.2
      _ = (if Even (3 * n) then 27 * n / 2
          else (27 * n + 1) / 2) := by
            rw [weightFive_dimension]
            rfl
      _ = (27 * n + 1) / 2 := weightFive_odd_ceil n

end LeanPaper.WeightFiveSignatureCount
