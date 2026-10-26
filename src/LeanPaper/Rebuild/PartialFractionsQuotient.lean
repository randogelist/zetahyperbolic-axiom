import LeanPaper.Rebuild.PartialFractionsCore

/-!
Identifies the polynomial part of the coprime simple-pole
decomposition with the *actual* Euclidean quotient in Definition 2.1.
-/

noncomputable section
open scoped BigOperators
open Polynomial

namespace ManuscriptChain.PartialFractions

theorem polynomial_eq_C_of_degree_lt_one {f : ℚ[X]} (hf : f.degree < 1) :
    f = Polynomial.C (f.coeff 0) := by
  have hnat : f.natDegree < 1 := by
    by_cases hzero : f = 0
    · simp [hzero]
    · exact (Polynomial.natDegree_lt_iff_degree_lt hzero).2 hf
  ext n
  cases n with
  | zero => simp
  | succ n =>
      have hcoeff : f.coeff (n + 1) = 0 :=
        Polynomial.coeff_eq_zero_of_natDegree_lt (by omega : f.natDegree < n + 1)
      simp [hcoeff]

theorem data_remainder_constant (p : Real.Parameters) (d a : ℕ)
    (ha : a ∈ Finset.Icc (p.N + 1) p.K) :
    (data p d).remainder a = C (((data p d).remainder a).coeff 0) := by
  apply polynomial_eq_C_of_degree_lt_one
  have hdeg := (data p d).remainder_degree a ha
  simpa only [Polynomial.degree_X_add_C] using hdeg

theorem data_quotient_eq_div (p : Real.Parameters) (d : ℕ) :
    (data p d).quotient = kernelNumerator p d / Real.tailD p := by
  classical
  let s := Finset.Icc (p.N + 1) p.K
  let g : ℕ → ℚ[X] := fun a => X + C ((a : ℚ) ^ 2)
  let fd := data p d
  let rem : ℚ[X] := ∑ a ∈ s, fd.remainder a * ∏ b ∈ s.erase a, g b
  have hg (a : ℕ) : (g a).Monic := monic_X_add_C _
  have hmonic : (Real.tailD p).Monic :=
    monic_prod_of_monic s g (fun a _ => hg a)
  have hdegree : rem.degree < (Real.tailD p).degree := by
    change (∑ a ∈ s, fd.remainder a * ∏ b ∈ s.erase a, g b).degree <
      (∏ a ∈ s, g a).degree
    refine (degree_sum_le _ _).trans_lt ((Finset.sup_lt_iff ?_).2 ?_)
    · rw [bot_lt_iff_ne_bot, degree_ne_bot]
      exact hmonic.ne_zero
    · intro a ha
      rw [← Finset.mul_prod_erase s g ha, mul_comm (g a), (hg a).degree_mul]
      refine (degree_mul_le _ _).trans_lt ?_
      have hnb : (∏ b ∈ s.erase a, g b).degree ≠ ⊥ := by
        rw [degree_ne_bot]
        exact (monic_prod_of_monic _ g (fun b _ => hg b)).ne_zero
      rw [add_comm, WithBot.add_lt_add_iff_left hnb]
      exact fd.remainder_degree a ha
  have hidentity : rem + Real.tailD p * fd.quotient = kernelNumerator p d := by
    rw [fd.numerator_eq]
    change rem + Real.tailD p * fd.quotient =
      fd.quotient * Real.tailD p + rem
    ring
  have hu := div_modByMonic_unique fd.quotient rem hmonic ⟨hidentity, hdegree⟩
  rw [divByMonic_eq_div _ hmonic] at hu
  exact hu.1.symm

theorem data_quotient_eq_actual (p : Real.Parameters) (i j : ℕ) :
    (data p (i + j)).quotient = Real.quotient p i j := by
  rw [data_quotient_eq_div]
  rfl

end ManuscriptChain.PartialFractions
