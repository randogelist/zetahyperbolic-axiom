import Mathlib.Data.Sign.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic
import LeanPaper.ImportedCharacter.PositiveSlope

/-!
# Theorem 6.4: signs of the actual odd-square residues

The manuscript includes three signs: the character, the tail derivative,
and the odd power of the oddPrefix polynomial. All three cancel. Checking only
the first two leaves `(-1)^N`, but does not refute the printed formula.
Here the oddPrefix and tail are the actual odd-square polynomials and the
residue amplitude is proved positive, rather than assumed positive.
-/

noncomputable section
open Polynomial SignType
open scoped BigOperators

namespace LeanPaper.BetaOddResidueSigns

def oddSquare (j : ℕ) : ℚ := (2 * (j : ℚ) + 1) ^ 2

def oddPrefix (N : ℕ) : ℚ[X] :=
  ∏ j ∈ Finset.range N, (X + C (oddSquare j))

def tail (N K : ℕ) : ℚ[X] :=
  ∏ j ∈ Finset.Ico N K, (X + C (oddSquare j))

lemma oddSquare_strictMono : StrictMono oddSquare := by
  intro a b hab
  unfold oddSquare
  have hab' : (a : ℚ) < b := by exact_mod_cast hab
  have ha : (0 : ℚ) ≤ a := by positivity
  nlinarith

lemma sign_prefix (N j : ℕ) (hj : N ≤ j) :
    sign ((oddPrefix N).eval (-oddSquare j)) = (-1 : SignType) ^ N := by
  simp only [oddPrefix, Polynomial.eval_prod, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
  change signHom (∏ b ∈ Finset.range N, (-oddSquare j + oddSquare b)) = _
  rw [map_prod]
  have hb (b : ℕ) (hb : b ∈ Finset.range N) :
      signHom (-oddSquare j + oddSquare b) = (-1 : SignType) := by
    apply sign_eq_neg_one_iff.mpr
    have h := oddSquare_strictMono (show b < j from
      lt_of_lt_of_le (Finset.mem_range.mp hb) hj)
    linarith
  rw [Finset.prod_congr rfl hb]
  simp

lemma tail_derivative_eval (N K j : ℕ) (hj : j ∈ Finset.Ico N K) :
    (derivative (tail N K)).eval (-oddSquare j) =
      ∏ b ∈ (Finset.Ico N K).erase j, (oddSquare b - oddSquare j) := by
  classical
  simp only [tail, derivative_prod_finset, derivative_add, derivative_X,
    derivative_C, add_zero, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_one, one_mul, mul_one,
    Polynomial.eval_prod, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
  rw [Finset.sum_eq_single j]
  · apply Finset.prod_congr rfl
    intro b hb
    ring
  · intro b hb hbj
    apply Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨Ne.symm hbj, hj⟩)
    simp
  · exact fun hn => (hn hj).elim

lemma sign_tail_derivative (N K j : ℕ) (hj : j ∈ Finset.Ico N K) :
    sign ((derivative (tail N K)).eval (-oddSquare j)) =
      (-1 : SignType) ^ (j - N) := by
  rw [tail_derivative_eval N K j hj]
  have hj' := Finset.mem_Ico.mp hj
  have hs : (Finset.Ico N K).erase j =
      Finset.Ico N j ∪ Finset.Ioo j K := by
    ext b
    simp only [Finset.mem_erase, Finset.mem_Ico, Finset.mem_Ioo, Finset.mem_union]
    omega
  have hd : Disjoint (Finset.Ico N j) (Finset.Ioo j K) := by
    rw [Finset.disjoint_left]
    intro b hb hc
    have := Finset.mem_Ico.mp hb
    have := Finset.mem_Ioo.mp hc
    omega
  change signHom (∏ b ∈ (Finset.Ico N K).erase j,
    (oddSquare b - oddSquare j)) = _
  rw [hs, Finset.prod_union hd, map_mul, map_prod, map_prod]
  have hl (b : ℕ) (hb : b ∈ Finset.Ico N j) :
      signHom (oddSquare b - oddSquare j) = (-1 : SignType) := by
    apply sign_eq_neg_one_iff.mpr
    exact sub_neg.mpr (oddSquare_strictMono (Finset.mem_Ico.mp hb).2)
  have hr (b : ℕ) (hb : b ∈ Finset.Ioo j K) :
      signHom (oddSquare b - oddSquare j) = (1 : SignType) := by
    apply sign_eq_one_iff.mpr
    exact sub_pos.mpr (oddSquare_strictMono (Finset.mem_Ioo.mp hb).1)
  rw [Finset.prod_congr rfl hl, Finset.prod_congr rfl hr]
  simp

/-- The literal residue in Theorem 6.4(2), with its oddPrefix sign retained. -/
def residue (N K m j : ℕ) : ℚ :=
  (2 * (j : ℚ) + 1) ^ 3 * (-1 : ℚ) ^ j *
    ((oddPrefix N).eval (-oddSquare j)) ^ (2 * m - 1) /
      (derivative (tail N K)).eval (-oddSquare j)

/-- Every residue in the actual printed odd-square formula is positive. -/
theorem residue_pos (N K m j : ℕ) (hm : 1 ≤ m) (hj : j ∈ Finset.Ico N K) :
    0 < residue N K m j := by
  apply sign_eq_one_iff.mp
  have hj' := Finset.mem_Ico.mp hj
  have hodd : Odd (2 * m - 1) := ⟨m - 1, by omega⟩
  have hp : sign (2 * (j : ℚ) + 1) = (1 : SignType) :=
    sign_eq_one_iff.mpr (by positivity)
  have hn : sign (-1 : ℚ) = (-1 : SignType) :=
    sign_eq_neg_one_iff.mpr (by norm_num)
  change signHom ((2 * (j : ℚ) + 1) ^ 3 * (-1 : ℚ) ^ j *
    ((oddPrefix N).eval (-oddSquare j)) ^ (2 * m - 1) /
      (derivative (tail N K)).eval (-oddSquare j)) = 1
  rw [map_div₀, map_mul, map_mul, map_pow, map_pow, map_pow]
  change sign (2 * (j : ℚ) + 1) ^ 3 * sign (-1 : ℚ) ^ j *
    sign ((oddPrefix N).eval (-oddSquare j)) ^ (2 * m - 1) /
      sign ((derivative (tail N K)).eval (-oddSquare j)) = 1
  rw [hp, hn, sign_prefix N j hj'.1, sign_tail_derivative N K j hj,
    one_pow, one_mul]
  rw [← pow_mul, Nat.mul_comm N, pow_mul, hodd.neg_one_pow]
  change ((-1 : SignType) ^ j * (-1 : SignType) ^ N) *
    (-1 : SignType) ^ (j - N) = 1
  rw [← pow_add, ← pow_add]
  have he : j + N + (j - N) = 2 * j := by omega
  rw [he, pow_mul]
  norm_num

def nodes (N K : ℕ) (a : Fin (K - N)) : ℝ :=
  -(oddSquare (N + a.val) : ℝ)

lemma nodes_injective (N K : ℕ) : Function.Injective (nodes N K) := by
  intro a b hab
  have hreal : (oddSquare (N + a.val) : ℝ) = (oddSquare (N + b.val) : ℝ) :=
    neg_injective hab
  have hrat : oddSquare (N + a.val) = oddSquare (N + b.val) := by
    exact_mod_cast hreal
  have hnat := oddSquare_strictMono.injective hrat
  apply Fin.ext
  omega

/-- The actual Vandermonde/residue matrix displayed in Theorem 6.4(2). -/
def slope (N K m : ℕ) : Matrix (Fin (K - N)) (Fin (K - N)) ℝ :=
  PaperAdvances.Theorem3_9_ShiftedPole.poleM (nodes N K)
    (fun a => (residue N K m (N + a.val) : ℝ))

/-- The displayed actual finite slope is positive definite in every dimension. -/
theorem slope_posDef (N K m : ℕ) (hm : 1 ≤ m) : (slope N K m).PosDef := by
  apply PaperAdvances.Theorem3_9_PositiveSlope.poleM_posDef
  · exact nodes_injective N K
  · intro a
    exact_mod_cast residue_pos N K m (N + a.val) hm
      (Finset.mem_Ico.mpr ⟨by omega, by have := a.isLt; omega⟩)

end LeanPaper.BetaOddResidueSigns

#print axioms LeanPaper.BetaOddResidueSigns.tail_derivative_eval
#print axioms LeanPaper.BetaOddResidueSigns.residue_pos
#print axioms LeanPaper.BetaOddResidueSigns.slope_posDef
