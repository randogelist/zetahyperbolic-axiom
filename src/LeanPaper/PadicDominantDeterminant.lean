import Mathlib.NumberTheory.Padics.PadicNorm
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Tactic

/-!
# A unique dominant determinant term over the rationals

If every diagonal entry has p-adic norm one and every off-diagonal entry has
norm strictly below one, the identity permutation is the unique norm-one
term in the determinant. The remaining finite sum has norm below one, so
the determinant has norm one and valuation zero. Zero off-diagonal entries
are allowed. Scalar normalization then gives an exact determinant valuation.

These are finite matrix theorems. They do not assume the determinant's
nonvanishing or valuation, and they do not assert that a manuscript family
satisfies the entrywise hypotheses without the separate arithmetic proof.
-/

noncomputable section
open scoped BigOperators

namespace LeanPaper.PadicDominantDeterminant

variable (p : ℕ) [Fact p.Prime]

lemma norm_prod {ι : Type*} (s : Finset ι) (f : ι → ℚ) :
    padicNorm p (∏ i ∈ s, f i) = ∏ i ∈ s, padicNorm p (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      simp only [Finset.prod_insert hi, padicNorm.mul, ih]

lemma norm_perm_sign {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    padicNorm p (((Equiv.Perm.sign σ : ℤ) : ℚ)) = 1 := by
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs <;> simp [hs]

/-- A rational with p-adic norm one is nonzero and has valuation zero. -/
theorem nonzero_and_valuation_zero_of_norm_one {q : ℚ}
    (hq : padicNorm p q = 1) : q ≠ 0 ∧ padicValRat p q = 0 := by
  have hn : q ≠ 0 := by
    intro hz
    simp [hz] at hq
  refine ⟨hn, ?_⟩
  have hp : 1 < (p : ℚ) := by exact_mod_cast (Fact.out : p.Prime).one_lt
  rw [padicNorm.eq_zpow_of_nonzero hn] at hq
  have hv : -padicValRat p q = 0 :=
    (zpow_eq_one_iff_right₀ (le_of_lt (lt_trans zero_lt_one hp)) (ne_of_gt hp)).mp hq
  omega

/-- The determinant's identity-permutation term strictly dominates all others. -/
theorem det_norm_one {n : ℕ} (M : Matrix (Fin n) (Fin n) ℚ)
    (hdiag : ∀ i, padicNorm p (M i i) = 1)
    (hoff : ∀ i j, i ≠ j → padicNorm p (M i j) < 1) :
    padicNorm p M.det = 1 := by
  classical
  let term : Equiv.Perm (Fin n) → ℚ := fun σ =>
    ((Equiv.Perm.sign σ : ℤ) : ℚ) * ∏ i, M (σ i) i
  have hterm (σ : Equiv.Perm (Fin n)) :
      padicNorm p (term σ) = ∏ i, padicNorm p (M (σ i) i) := by
    dsimp only [term]
    rw [padicNorm.mul, norm_perm_sign p, one_mul, norm_prod p]
  have hid : padicNorm p (term 1) = 1 := by
    rw [hterm]
    simp [hdiag]
  have hother (σ : Equiv.Perm (Fin n)) (hσ : σ ≠ 1) :
      padicNorm p (term σ) < 1 := by
    obtain ⟨i, hi⟩ : ∃ i, σ i ≠ i := by
      by_contra! h
      apply hσ
      apply Equiv.ext
      intro i
      simpa using h i
    have hle (j : Fin n) : padicNorm p (M (σ j) j) ≤ 1 := by
      by_cases hj : σ j = j
      · simpa [hj] using (hdiag j).le
      · exact (hoff (σ j) j hj).le
    have hrest : (∏ j ∈ (Finset.univ : Finset (Fin n)).erase i,
        padicNorm p (M (σ j) j)) ≤ 1 :=
      Finset.prod_le_one (fun j _ => padicNorm.nonneg _) (fun j _ => hle j)
    rw [hterm, ← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
    calc
      _ ≤ padicNorm p (M (σ i) i) * 1 :=
        mul_le_mul_of_nonneg_left hrest (padicNorm.nonneg _)
      _ < 1 := by simpa using hoff (σ i) i hi
  have htail : padicNorm p
      (∑ σ ∈ (Finset.univ : Finset (Equiv.Perm (Fin n))).erase 1, term σ) < 1 := by
    apply padicNorm.sum_lt' _ (by norm_num)
    intro σ hσ
    exact hother σ (Finset.ne_of_mem_erase hσ)
  rw [Matrix.det_apply']
  change padicNorm p (∑ σ, term σ) = 1
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (1 : Equiv.Perm (Fin n)))]
  have hne : padicNorm p
      (∑ σ ∈ (Finset.univ : Finset (Equiv.Perm (Fin n))).erase 1, term σ) ≠
      padicNorm p (term 1) := by
    rw [hid]
    exact ne_of_lt htail
  rw [padicNorm.add_eq_max_of_ne hne, hid, max_eq_right htail.le]

/-- Nonvanishing and valuation are consequences of entrywise dominance. -/
theorem det_nonzero_and_valuation_zero {n : ℕ} (M : Matrix (Fin n) (Fin n) ℚ)
    (hdiag : ∀ i, padicNorm p (M i i) = 1)
    (hoff : ∀ i j, i ≠ j → padicNorm p (M i j) < 1) :
    M.det ≠ 0 ∧ padicValRat p M.det = 0 :=
  nonzero_and_valuation_zero_of_norm_one p (det_norm_one p M hdiag hoff)

/-- A perturbation of p-adic norm less than one preserves a unit's norm. -/
theorem norm_one_of_sub_lt_one {a c : ℚ} (hc : padicNorm p c = 1)
    (ha : padicNorm p (a - c) < 1) : padicNorm p a = 1 := by
  have hne : padicNorm p (a - c) ≠ padicNorm p c := by
    rw [hc]
    exact ne_of_lt ha
  have h := padicNorm.add_eq_max_of_ne hne
  rw [sub_add_cancel, hc, max_eq_right ha.le] at h
  exact h

/-- Diagonal entries may be specified by a fixed unit plus small errors. -/
theorem det_norm_one_of_diagonal_perturbation {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℚ) (c : ℚ) (hc : padicNorm p c = 1)
    (hdiag : ∀ i, padicNorm p (M i i - c) < 1)
    (hoff : ∀ i j, i ≠ j → padicNorm p (M i j) < 1) :
    padicNorm p M.det = 1 :=
  det_norm_one p M (fun i => norm_one_of_sub_lt_one p hc (hdiag i)) hoff

/-- Recover the unnormalized determinant valuation from any nonzero scalar. -/
theorem valuation_of_scalar_normalization {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℚ) (c : ℚ) (hc : c ≠ 0)
    (hdiag : ∀ i, padicNorm p ((c • M) i i) = 1)
    (hoff : ∀ i j, i ≠ j → padicNorm p ((c • M) i j) < 1) :
    M.det ≠ 0 ∧ padicValRat p M.det = -(n : ℤ) * padicValRat p c := by
  obtain ⟨hn, hv⟩ := det_nonzero_and_valuation_zero p (c • M) hdiag hoff
  have he : (c • M).det = c ^ n * M.det := by
    simpa using Matrix.det_smul M c
  have hM : M.det ≠ 0 := by
    intro hz
    apply hn
    rw [he, hz, mul_zero]
  refine ⟨hM, ?_⟩
  rw [he, padicValRat.mul (pow_ne_zero n hc) hM, padicValRat.pow] at hv
  linarith

/-- Scaling by p^a yields exactly -a*n, including the zero-dimensional case. -/
theorem valuation_of_prime_power_normalization {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℚ) (a : ℕ)
    (hdiag : ∀ i, padicNorm p (((p : ℚ) ^ a • M) i i) = 1)
    (hoff : ∀ i j, i ≠ j → padicNorm p (((p : ℚ) ^ a • M) i j) < 1) :
    M.det ≠ 0 ∧ padicValRat p M.det = -(a : ℤ) * (n : ℤ) := by
  have hp : p.Prime := Fact.out
  have hpq : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  obtain ⟨hn, hv⟩ := valuation_of_scalar_normalization p M ((p : ℚ) ^ a)
    (pow_ne_zero a hpq) hdiag hoff
  refine ⟨hn, ?_⟩
  rw [padicValRat.pow, padicValRat.self hp.one_lt, mul_one] at hv
  linarith

end LeanPaper.PadicDominantDeterminant

#print axioms LeanPaper.PadicDominantDeterminant.det_norm_one
#print axioms LeanPaper.PadicDominantDeterminant.det_nonzero_and_valuation_zero
#print axioms LeanPaper.PadicDominantDeterminant.det_norm_one_of_diagonal_perturbation
#print axioms LeanPaper.PadicDominantDeterminant.valuation_of_scalar_normalization
#print axioms LeanPaper.PadicDominantDeterminant.valuation_of_prime_power_normalization
