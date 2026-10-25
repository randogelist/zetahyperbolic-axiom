import Mathlib

/-!
# Theorem 6.9: corrected finite triple-pole architecture

The corrected kernel uses `∏_{j=1}^n (t-j)^6 / (n!)^5`.
This module makes the triple-pole functional explicit and proves its exact
Hermite congruence and determinant identity. There are three jets at each of
`3m` nodes, hence dimension `9m`.

The actual Laurent-coefficient formulas of the corrected kernel, invertibility
of the particular manuscript's Hermite interpolation table, and the claimed
q-adic leading congruences/valuation are not asserted here. The determinant
nonvanishing result displays precisely the finite hypotheses it needs.
-/

namespace Zetahyperbolic.TriplePoleRepair

noncomputable section
open scoped BigOperators Matrix
open Polynomial

/-- Corrected numerator, including the normalization omitted in the manuscript. -/
def kernelNumerator (n : ℕ) : ℚ[X] :=
  C (((Nat.factorial (6 * n) : ℚ) ^ 3) / (Nat.factorial n : ℚ) ^ 5) *
    ∏ j ∈ Finset.range n, (X - C ((j + 1 : ℕ) : ℚ)) ^ 6

/-- Every prescribed pole has order three before any cancellation. -/
def kernelDenominator (n : ℕ) : ℚ[X] :=
  ∏ k ∈ Finset.range (6 * n + 1), (X + C (k : ℚ)) ^ 3

/-- Rational evaluation away from the poles; total division is used at poles. -/
def correctedKernel (n : ℕ) (t : ℚ) : ℚ :=
  (kernelNumerator n).eval t / (kernelDenominator n).eval t

/-- The old shift had an unwanted zero at zero; the corrected numerator does not. -/
theorem kernelNumerator_eval_zero_ne_zero (n : ℕ) :
    (kernelNumerator n).eval 0 ≠ 0 := by
  classical
  simp only [kernelNumerator, eval_mul, eval_C, eval_prod, eval_pow,
    eval_sub, eval_X]
  apply mul_ne_zero
  · apply div_ne_zero <;> apply pow_ne_zero <;> exact_mod_cast Nat.factorial_ne_zero _
  · apply Finset.prod_ne_zero_iff.mpr
    intro j hj
    apply pow_ne_zero
    have h : ((j + 1 : ℕ) : ℚ) ≠ 0 := by positivity
    simpa using neg_ne_zero.mpr h

/-- Divided Taylor coefficient: jet 0 is P(a), jet 1 is P'(a),
and jet 2 is P''(a)/2. Taylor coefficients avoid factorial conventions. -/
def jet (P : ℚ[X]) (a : ℚ) (r : ℕ) : ℚ :=
  (Polynomial.taylor a P).coeff r

/-- Multiplication by P transforms the three principal-part coefficients.
Here `c 0,c 1,c 2` denote the simple, double, and triple coefficients. -/
def multipliedPoleCoefficients (a : ℚ) (c : Fin 3 → ℚ) (P : ℚ[X]) : Fin 3 → ℚ :=
  ![c 0 * jet P a 0 + c 1 * jet P a 1 + c 2 * jet P a 2,
    c 1 * jet P a 0 + c 2 * jet P a 1,
    c 2 * jet P a 0]

/-- Explicit triple-pole residue functional, with the three pole values u. -/
def poleFunctional (a : ℚ) (c u : Fin 3 → ℚ) (P : ℚ[X]) : ℚ :=
  ∑ r, u r * multipliedPoleCoefficients a c P r

/-- Coefficients of the equivalent three-jet functional. -/
def jetWeights (c u : Fin 3 → ℚ) : Fin 3 → ℚ :=
  ![c 0 * u 0 + c 1 * u 1 + c 2 * u 2,
    c 1 * u 0 + c 2 * u 1,
    c 2 * u 0]

def jetFunctional (a : ℚ) (w : Fin 3 → ℚ) (P : ℚ[X]) : ℚ :=
  w 0 * jet P a 0 + w 1 * jet P a 1 + w 2 * jet P a 2

/-- Collecting the three Laurent levels yields this exact identity. -/
theorem poleFunctional_eq_jetFunctional (a : ℚ) (c u : Fin 3 → ℚ) (P : ℚ[X]) :
    poleFunctional a c u P = jetFunctional a (jetWeights c u) P := by
  simp [poleFunctional, multipliedPoleCoefficients, jetFunctional, jetWeights,
    Fin.sum_univ_succ]
  ring

/-- The anti-triangular Hermite block for a three-jet functional. -/
def localBlock (w : Fin 3 → ℚ) : Matrix (Fin 3) (Fin 3) ℚ :=
  !![w 0, w 1, w 2; w 1, w 2, 0; w 2, 0, 0]

theorem localBlock_det (w : Fin 3 → ℚ) :
    (localBlock w).det = -(w 2) ^ 3 := by
  simp [localBlock, Matrix.det_fin_three]
  ring

theorem localBlock_det_ne_zero (w : Fin 3 → ℚ) (hw : w 2 ≠ 0) :
    (localBlock w).det ≠ 0 := by
  rw [localBlock_det]
  exact neg_ne_zero.mpr (pow_ne_zero _ hw)

private theorem jet_mul_zero (P Q : ℚ[X]) (a : ℚ) :
    jet (P * Q) a 0 = jet P a 0 * jet Q a 0 := by
  simp [jet, Polynomial.taylor_mul]

private theorem jet_mul_one (P Q : ℚ[X]) (a : ℚ) :
    jet (P * Q) a 1 = jet P a 0 * jet Q a 1 + jet P a 1 * jet Q a 0 := by
  simp [jet, Polynomial.taylor_mul, Polynomial.mul_coeff_one]

private theorem jet_mul_two (P Q : ℚ[X]) (a : ℚ) :
    jet (P * Q) a 2 = jet P a 0 * jet Q a 2 +
      jet P a 1 * jet Q a 1 + jet P a 2 * jet Q a 0 := by
  simp only [jet, Polynomial.taylor_mul, Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j => (Polynomial.taylor a P).coeff i * (Polynomial.taylor a Q).coeff j) 2]
  norm_num [Finset.sum_range_succ]

/-- Exact product-rule congruence for each pole, without any q-adic input. -/
theorem local_congruence (P Q : ℚ[X]) (a : ℚ) (w : Fin 3 → ℚ) :
    jetFunctional a w (P * Q) =
      ∑ r : Fin 3, ∑ s : Fin 3,
        jet P a r * localBlock w r s * jet Q a s := by
  rw [jetFunctional, jet_mul_zero, jet_mul_one, jet_mul_two]
  simp [localBlock, Fin.sum_univ_succ]
  ring

/-- Three jets at each of n nodes. -/
abbrev JetIndex (n : ℕ) := Fin 3 × Fin n

/-- The corrected number of rows and columns for 3m nodes is 9m. -/
theorem dimension_9m (m : ℕ) : Fintype.card (JetIndex (3 * m)) = 9 * m := by
  simp [JetIndex]
  omega

/-- Jet evaluation table for an arbitrary polynomial family of the correct size. -/
def jetTable {n : ℕ} (nodes : Fin n → ℚ) (basis : JetIndex n → ℚ[X]) :
    Matrix (JetIndex n) (JetIndex n) ℚ :=
  fun i j => jet (basis i) (nodes j.2) j.1

/-- Gram/Hankel matrix of the sum of the explicit pole functionals. -/
def momentMatrix {n : ℕ} (nodes : Fin n → ℚ) (c u : Fin n → Fin 3 → ℚ)
    (basis : JetIndex n → ℚ[X]) : Matrix (JetIndex n) (JetIndex n) ℚ :=
  fun i j => ∑ a, poleFunctional (nodes a) (c a) (u a) (basis i * basis j)

/-- Hermite congruence. No basis invertibility is needed for the identity. -/
theorem hermite_congruence {n : ℕ} (nodes : Fin n → ℚ) (c u : Fin n → Fin 3 → ℚ)
    (basis : JetIndex n → ℚ[X]) :
    momentMatrix nodes c u basis =
      jetTable nodes basis * Matrix.blockDiagonal (fun a => localBlock (jetWeights (c a) (u a))) *
        (jetTable nodes basis).transpose := by
  ext i j
  simp only [momentMatrix, poleFunctional_eq_jetFunctional, local_congruence,
    Matrix.mul_apply, Matrix.transpose_apply, jetTable, Fintype.sum_prod_type,
    Matrix.blockDiagonal_apply, Finset.sum_mul]
  simp only [mul_ite, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ,
    if_true]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.sum_comm]

/-- Exact determinant factorization; the triple coefficient and simple-pole
functional value control the block anti-diagonal. -/
theorem momentMatrix_det {n : ℕ} (nodes : Fin n → ℚ) (c u : Fin n → Fin 3 → ℚ)
    (basis : JetIndex n → ℚ[X]) :
    (momentMatrix nodes c u basis).det =
      (jetTable nodes basis).det ^ 2 * ∏ a, -(c a 2 * u a 0) ^ 3 := by
  rw [hermite_congruence, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose,
    Matrix.det_blockDiagonal]
  simp only [localBlock_det]
  change (jetTable nodes basis).det * (∏ a, -(c a 2 * u a 0) ^ 3) *
    (jetTable nodes basis).det = _
  ring

/-- The finite nonvanishing criterion. A manuscript application must establish
the interpolation determinant and the specific nonzero pole data. -/
theorem momentMatrix_det_ne_zero {n : ℕ} (nodes : Fin n → ℚ)
    (c u : Fin n → Fin 3 → ℚ) (basis : JetIndex n → ℚ[X])
    (hbasis : (jetTable nodes basis).det ≠ 0)
    (htriple : ∀ a, c a 2 ≠ 0) (hpole : ∀ a, u a 0 ≠ 0) :
    (momentMatrix nodes c u basis).det ≠ 0 := by
  rw [momentMatrix_det]
  apply mul_ne_zero (pow_ne_zero _ hbasis)
  apply Finset.prod_ne_zero_iff.mpr
  intro a ha
  exact neg_ne_zero.mpr (pow_ne_zero _ (mul_ne_zero (htriple a) (hpole a)))

end
end Zetahyperbolic.TriplePoleRepair

#print axioms Zetahyperbolic.TriplePoleRepair.hermite_congruence
#print axioms Zetahyperbolic.TriplePoleRepair.momentMatrix_det_ne_zero
