import LeanPaper.BeukersHarmonicRemainders
import LeanPaper.PadicDominantDeterminant
import LeanPaper.ImportedSection56.DualAffineAlgebra

/-!
# Theorem 6.3(1): the actual two-monomial prime matrix

The coefficient rows here are exactly the polynomials `x^r + x^(r+q)`.
All four rational moments and the slope `2 I` are identified before applying
the local arithmetic estimates. The false positive-cone assertion in 6.3(2)
is independent and is not used.
-/

noncomputable section
open scoped BigOperators
open Matrix Polynomial

namespace ManuscriptChain.Beukers.PrimeMatrix

def lowerIndex {q : ℕ} (i : Fin q) : Fin (2 * q - 1 + 1) :=
  ⟨i.val, by have := i.isLt; omega⟩

def upperIndex {q : ℕ} (i : Fin q) : Fin (2 * q - 1 + 1) :=
  ⟨i.val + q, by have := i.isLt; omega⟩

@[simp] lemma lowerIndex_eq_iff {q : ℕ} (i j : Fin q) :
    lowerIndex i = lowerIndex j ↔ i = j := by
  constructor
  · intro h
    apply Fin.ext
    simpa only [lowerIndex] using
      congrArg (fun x : Fin (2 * q - 1 + 1) => x.val) h
  · rintro rfl
    rfl

@[simp] lemma upperIndex_eq_iff {q : ℕ} (i j : Fin q) :
    upperIndex i = upperIndex j ↔ i = j := by
  constructor
  · intro h
    have hv := congrArg Fin.val h
    apply Fin.ext
    dsimp [upperIndex] at hv
    omega
  · rintro rfl
    rfl

@[simp] lemma lowerIndex_ne_upperIndex {q : ℕ} (i j : Fin q) :
    lowerIndex i ≠ upperIndex j := by
  intro h
  have hv := congrArg Fin.val h
  have hi := i.isLt
  dsimp [lowerIndex, upperIndex] at hv
  omega

@[simp] lemma upperIndex_ne_lowerIndex {q : ℕ} (i j : Fin q) :
    upperIndex i ≠ lowerIndex j := Ne.symm (lowerIndex_ne_upperIndex j i)

/-- Exactly two coefficient-one monomials in the manuscript's degree window. -/
def coefficients (q : ℕ) : Fin q → Fin (2 * q - 1 + 1) → ℚ :=
  fun i r => (if r = lowerIndex i then 1 else 0) +
    (if r = upperIndex i then 1 else 0)

def basisPolynomial {q : ℕ} (i : Fin q) : ℚ[X] :=
  X ^ i.val + X ^ (i.val + q)

theorem coefficients_eq_coeff {q : ℕ} (i : Fin q) (r : Fin (2 * q - 1 + 1)) :
    coefficients q i r = (basisPolynomial i).coeff r.val := by
  simp [coefficients, basisPolynomial, Polynomial.coeff_X_pow, Fin.ext_iff,
    lowerIndex, upperIndex, eq_comm]

lemma sum_coefficients_mul {q : ℕ} (i : Fin q) (f : Fin (2 * q - 1 + 1) → ℚ) :
    (∑ r, coefficients q i r * f r) = f (lowerIndex i) + f (upperIndex i) := by
  simp [coefficients, add_mul, Finset.sum_add_distrib]

/-- Disjoint two-monomial rows are genuinely independent. -/
theorem coefficients_vecMul_injective (q : ℕ) :
    Function.Injective
      (coefficients q : Matrix (Fin q) (Fin (2 * q - 1 + 1)) ℚ).vecMul := by
  intro a b hab
  funext i
  have h := congrFun hab (lowerIndex i)
  simpa [Matrix.vecMul, dotProduct, coefficients, mul_add, mul_ite] using h

lemma slope_entry {q : ℕ} (i j : Fin q) :
    (∑ r, coefficients q i r * coefficients q j r) = if i = j then 2 else 0 := by
  rw [sum_coefficients_mul]
  by_cases hij : i = j
  · subst j
    norm_num [coefficients]
  · simp [coefficients, hij]

lemma constant_entry {q : ℕ} (i j : Fin q) :
    (∑ r, ∑ t, coefficients q i r * coefficients q j t *
      Real.dualConstant 7 r.val t.val) =
    Real.dualConstant 7 i.val j.val + Real.dualConstant 7 i.val (j.val + q) +
      Real.dualConstant 7 (i.val + q) j.val +
      Real.dualConstant 7 (i.val + q) (j.val + q) := by
  have he : (∑ r, ∑ t, coefficients q i r * coefficients q j t *
      Real.dualConstant 7 r.val t.val) =
      ∑ r, coefficients q i r *
        (∑ t, coefficients q j t * Real.dualConstant 7 r.val t.val) := by
    apply Finset.sum_congr rfl
    intro r hr
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t ht
    ring
  rw [he, sum_coefficients_mul, sum_coefficients_mul, sum_coefficients_mul]
  dsimp [lowerIndex, upperIndex]
  ring

/-- Evaluation of the original rational dual pencil at a rational argument. -/
def matrix (q : ℕ) (x : ℚ) : Matrix (Fin q) (Fin q) ℚ :=
  fun i j => (Real.dualEntry 7 (coefficients q) i j).eval x

theorem matrix_entry {q : ℕ} (x : ℚ) (i j : Fin q) :
    matrix q x i j =
      Real.dualConstant 7 i.val j.val + Real.dualConstant 7 i.val (j.val + q) +
      Real.dualConstant 7 (i.val + q) j.val +
      Real.dualConstant 7 (i.val + q) (j.val + q) +
      (if i = j then 2 * x else 0) := by
  simp only [matrix, Real.dualEntry, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X, constant_entry, slope_entry]
  split_ifs <;> ring

/-- The literal scalar diagonal at zero, including all four moments. -/
def zeroDiagonal (q r : ℕ) : ℚ :=
  -Real.harmonic 7 r - Real.harmonic 7 (r + q) +
    (Real.harmonic 6 r - Real.harmonic 6 (r + q)) / (3 * (-(q : ℚ)))

theorem matrix_diagonal {q : ℕ} (x : ℚ) (i : Fin q) :
    matrix q x i i = 2 * x + zeroDiagonal q i.val := by
  have hq : (q : ℚ) ≠ 0 := by
    exact_mod_cast (show q ≠ 0 by have := i.isLt; omega)
  have hne : i.val ≠ i.val + q := by have := i.isLt; omega
  rw [matrix_entry, PaperOrder.CoreAlgebra.dualConstant_swap 7 (i.val + q) i.val]
  simp only [zeroDiagonal, Real.dualConstant, if_true, hne, if_false]
  norm_num only [Nat.reduceSub, Nat.cast_ofNat]
  push_cast
  rw [show (i.val : ℚ) - ((i.val : ℚ) + q) = -(q : ℚ) by ring]
  field_simp [hq] <;> ring

theorem determinant_eq_dualDelta (q : ℕ) (x : ℚ) :
    (matrix q x).det = (Real.dualDelta 7 (coefficients q)).eval x := by
  unfold matrix Real.dualDelta
  exact ((Polynomial.evalRingHom x).map_det _).symm

lemma padicNorm_add_lt_one (q : ℕ) [Fact q.Prime] {a b : ℚ}
    (ha : padicNorm q a < 1) (hb : padicNorm q b < 1) :
    padicNorm q (a + b) < 1 :=
  lt_of_le_of_lt padicNorm.nonarchimedean (max_lt ha hb)

/-- The actual rational-X diagonal is a small perturbation of -2/3. -/
theorem normalized_diagonal_remainder (q : ℕ) [Fact q.Prime] (hq5 : 5 ≤ q)
    (x : ℚ) (hx : padicNorm q x ≤ 1) (i : Fin q) :
    padicNorm q ((((q : ℚ) ^ 7 • matrix q x) i i) - (-2 / 3 : ℚ)) < 1 := by
  change padicNorm q ((q : ℚ) ^ 7 * matrix q x i i - (-2 / 3 : ℚ)) < 1
  rw [matrix_diagonal]
  have he : (q : ℚ) ^ 7 * (2 * x + zeroDiagonal q i.val) - (-2 / 3 : ℚ) =
      (q : ℚ) ^ 7 * (2 * x) + ((q : ℚ) ^ 7 * zeroDiagonal q i.val + 2 / 3) := by ring
  rw [he]
  apply padicNorm_add_lt_one q (scaled_integral_two_mul_norm_lt q hq5 x hx)
  exact scaled_Aq_diagonal_remainder_norm_lt q i.val hq5 i.isLt

theorem normalized_diagonal_norm (q : ℕ) [Fact q.Prime] (hq5 : 5 ≤ q)
    (x : ℚ) (hx : padicNorm q x ≤ 1) (i : Fin q) :
    padicNorm q (((q : ℚ) ^ 7 • matrix q x) i i) = 1 :=
  LeanPaper.PadicDominantDeterminant.norm_one_of_sub_lt_one q
    (padicNorm_negative_two_thirds_eq_one q hq5)
    (normalized_diagonal_remainder q hq5 x hx i)

/-- Distinct basis rows occupy distinct residue classes in all four moments. -/
theorem normalized_offdiagonal_norm (q : ℕ) [Fact q.Prime] (hq5 : 5 ≤ q)
    (x : ℚ) (i j : Fin q) (hij : i ≠ j) :
    padicNorm q (((q : ℚ) ^ 7 • matrix q x) i j) < 1 := by
  have hv : i.val ≠ j.val := fun h => hij (Fin.ext h)
  have hi := i.isLt
  have hj := j.isLt
  have h00 : i.val % q ≠ j.val % q := by
    simpa only [Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] using hv
  have h01 : i.val % q ≠ (j.val + q) % q := by simpa using h00
  have h10 : (i.val + q) % q ≠ j.val % q := by simpa using h00
  have h11 : (i.val + q) % q ≠ (j.val + q) % q := by simpa using h00
  have hn00 := scaled_dualConstant_distinct_residues_norm_lt q i.val j.val hq5
    (by omega) (by omega) h00
  have hn01 := scaled_dualConstant_distinct_residues_norm_lt q i.val (j.val + q) hq5
    (by omega) (by omega) h01
  have hn10 := scaled_dualConstant_distinct_residues_norm_lt q (i.val + q) j.val hq5
    (by omega) (by omega) h10
  have hn11 := scaled_dualConstant_distinct_residues_norm_lt q (i.val + q) (j.val + q) hq5
    (by omega) (by omega) h11
  change padicNorm q ((q : ℚ) ^ 7 * matrix q x i j) < 1
  rw [matrix_entry, if_neg hij, add_zero]
  simp only [mul_add]
  exact padicNorm_add_lt_one q
    (padicNorm_add_lt_one q (padicNorm_add_lt_one q hn00 hn01) hn10) hn11

/-- Every q-integral rational argument has the same exact determinant valuation. -/
theorem matrix_det_valuation (q : ℕ) [Fact q.Prime] (hq5 : 5 ≤ q)
    (x : ℚ) (hx : padicNorm q x ≤ 1) :
    (matrix q x).det ≠ 0 ∧ padicValRat q (matrix q x).det = -7 * (q : ℤ) := by
  exact LeanPaper.PadicDominantDeterminant.valuation_of_prime_power_normalization q
    (matrix q x) 7 (normalized_diagonal_norm q hq5 x hx)
    (normalized_offdiagonal_norm q hq5 x)

/-- Full original Theorem 6.3(1), for its actual Aq coefficient family.
The valuation at every rational argument of q-unit denominator is included. -/
theorem theorem_6_3_1 (q : ℕ) [Fact q.Prime] (hq5 : 5 ≤ q) :
    padicValRat q ((Real.dualDelta 7 (coefficients q)).eval 0) = -7 * (q : ℤ) ∧
    (Real.dualDelta 7 (coefficients q)).eval 0 ≠ 0 ∧
    ∀ a b : ℤ, ¬(q : ℤ) ∣ b →
      (Real.dualDelta 7 (coefficients q)).eval ((a : ℚ) / (b : ℚ)) ≠ 0 ∧
      padicValRat q ((Real.dualDelta 7 (coefficients q)).eval
        ((a : ℚ) / (b : ℚ))) = -7 * (q : ℤ) := by
  have hzero := matrix_det_valuation q hq5 0 (by simp)
  rw [determinant_eq_dualDelta] at hzero
  refine ⟨hzero.2, hzero.1, ?_⟩
  intro a b hb
  have hx : padicNorm q ((a : ℚ) / (b : ℚ)) ≤ 1 := by
    rw [padicNorm.div, (padicNorm.int_eq_one_iff b).mpr hb, div_one]
    exact padicNorm.of_int a
  have h := matrix_det_valuation q hq5 ((a : ℚ) / (b : ℚ)) hx
  rwa [determinant_eq_dualDelta] at h

/-- The printed congruence modulo Z_q is too strong at q=7; the weaker
remainder bound used below is sufficient for the unchanged determinant claim. -/
theorem seven_diagonal_remainder_exact :
    zeroDiagonal 7 0 + 2 / (3 * (7 : ℚ) ^ 7) =
      -(18809799306101 : ℚ) / 19595520000000 := by
  norm_num [zeroDiagonal, Real.harmonic, Finset.sum_range_succ]

theorem seven_diagonal_remainder_not_integral :
    7 ∣ (zeroDiagonal 7 0 + 2 / (3 * (7 : ℚ) ^ 7)).den ∧
      ¬(7 : ℤ) ∣ (zeroDiagonal 7 0 + 2 / (3 * (7 : ℚ) ^ 7)).num := by
  rw [seven_diagonal_remainder_exact]
  norm_num

end ManuscriptChain.Beukers.PrimeMatrix

#print axioms ManuscriptChain.Beukers.PrimeMatrix.matrix_entry
#print axioms ManuscriptChain.Beukers.PrimeMatrix.coefficients_vecMul_injective
#print axioms ManuscriptChain.Beukers.PrimeMatrix.matrix_det_valuation
#print axioms ManuscriptChain.Beukers.PrimeMatrix.theorem_6_3_1
#print axioms ManuscriptChain.Beukers.PrimeMatrix.seven_diagonal_remainder_not_integral
