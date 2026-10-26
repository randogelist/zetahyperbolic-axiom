import Mathlib

/-!
# Theorem 6.10(2): vanishing quadratic coefficient-Gram growth

The determinant is that of the actual integral coefficient Gram matrix CCᵀ.
The proof uses a factorial determinant bound, weaker than the printed Hadamard
finite bound but sufficient to prove the same zero quadratic growth rate.
Polynomial entry growth is stated with an arbitrary natural exponent; every
fixed nonnegative real exponent is bounded by such an exponent on K≥1.
-/
noncomputable section
open Matrix Filter
open scoped BigOperators Topology

namespace ManuscriptChain.CoefficientGramGrowth

def intGram {h K : ℕ} (C : Matrix (Fin h) (Fin (K+1)) ℤ) : Matrix (Fin h) (Fin h) ℤ :=
  C * C.transpose

def realGram {h K : ℕ} (C : Matrix (Fin h) (Fin (K+1)) ℤ) : Matrix (Fin h) (Fin h) ℝ :=
  (C.map (Int.castRingHom ℝ)) * (C.map (Int.castRingHom ℝ)).transpose

theorem map_intGram {h K : ℕ} (C : Matrix (Fin h) (Fin (K+1)) ℤ) :
    (intGram C).map (Int.castRingHom ℝ) = realGram C := by
  ext i j
  simp [intGram, realGram, Matrix.mul_apply]

theorem det_realGram_eq_int {h K : ℕ} (C : Matrix (Fin h) (Fin (K+1)) ℤ) :
    (realGram C).det = ((intGram C).det : ℝ) := by
  rw [← map_intGram]
  exact ((Int.castRingHom ℝ).map_det (intGram C)).symm

/-- Full row rank is the precise coefficient-space independence condition. -/
theorem realGram_posDef {h K : ℕ} (C : Matrix (Fin h) (Fin (K+1)) ℤ)
    (hC : Function.Injective (C.map (Int.castRingHom ℝ)).vecMul) :
    (realGram C).PosDef := by
  have hh := Matrix.PosDef.mul_conjTranspose_self (C.map (Int.castRingHom ℝ)) hC
  simpa [realGram, Matrix.conjTranspose_eq_transpose_of_trivial] using hh

/-- Integer discreteness supplies the lower determinant bound. -/
theorem one_le_det {h K : ℕ} (C : Matrix (Fin h) (Fin (K+1)) ℤ)
    (hC : Function.Injective (C.map (Int.castRingHom ℝ)).vecMul) :
    1 ≤ (realGram C).det := by
  have hh := (realGram_posDef C hC).det_pos
  rw [det_realGram_eq_int] at hh ⊢
  have hi : (0 : ℤ) < (intGram C).det := by exact_mod_cast hh
  exact_mod_cast (show (1 : ℤ) ≤ (intGram C).det by omega)

/-- Polynomially bounded entries give a uniform exponential-of-K-log-K bound. -/
theorem det_upper {h K A : ℕ} (C : Matrix (Fin h) (Fin (K+1)) ℤ)
    (hsize : h ≤ K+1)
    (hentry : ∀ i j, |(C i j : ℝ)| ≤ ((K+1 : ℕ) : ℝ)^A) :
    (realGram C).det ≤ (((K+1 : ℕ) : ℝ)^((2*A+2)*(K+1))) := by
  have hbase : (1 : ℝ) ≤ (K+1 : ℕ) := by exact_mod_cast (Nat.succ_le_succ (Nat.zero_le K))
  have hGram : ∀ i j, |realGram C i j| ≤ ((K+1 : ℕ) : ℝ)^(2*A+1) := by
    intro i j
    unfold realGram
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply]
    calc
      |∑ r : Fin (K+1), (C i r : ℝ) * (C j r : ℝ)|
          ≤ ∑ r : Fin (K+1), |(C i r : ℝ) * (C j r : ℝ)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _r : Fin (K+1), ((K+1 : ℕ) : ℝ)^A * ((K+1 : ℕ) : ℝ)^A := by
        apply Finset.sum_le_sum
        intro r _
        rw [abs_mul]
        exact mul_le_mul (hentry i r) (hentry j r) (abs_nonneg _) (by positivity)
      _ = ((K+1 : ℕ) : ℝ)^(2*A+1) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        rw [← pow_add, pow_succ, show A+A = 2*A by omega]
        exact mul_comm _ _
  have hdet : |(realGram C).det| ≤ (h.factorial : ℝ) *
      (((K+1 : ℕ) : ℝ)^(2*A+1))^h := by
    simpa using
      (Matrix.det_le (abv := AbsoluteValue.abs) hGram)
  have hfac : (h.factorial : ℝ) ≤ (((K+1 : ℕ) : ℝ)^h) := by
    have hh : h.factorial ≤ (K+1)^h :=
      (Nat.factorial_le_pow h).trans (Nat.pow_le_pow_left hsize h)
    exact_mod_cast hh
  calc
    (realGram C).det ≤ |(realGram C).det| := le_abs_self _
    _ ≤ (h.factorial : ℝ) * (((K+1 : ℕ) : ℝ)^(2*A+1))^h := hdet
    _ ≤ (((K+1 : ℕ) : ℝ)^h) * (((K+1 : ℕ) : ℝ)^(2*A+1))^h := by gcongr
    _ = (((K+1 : ℕ) : ℝ)^((2*A+2)*h)) := by rw [← mul_pow, ← pow_succ', ← pow_mul]
    _ ≤ (((K+1 : ℕ) : ℝ)^((2*A+2)*(K+1))) :=
      pow_le_pow_right₀ hbase (Nat.mul_le_mul_left _ hsize)

/-- Main asymptotic assertion of Theorem 6.10(2). No determinant growth
hypothesis is assumed; it is derived from coefficient growth and row rank. -/
theorem normalized_log_det_tendsto_zero
    (h : ℕ → ℕ) (C : ∀ K, Matrix (Fin (h K)) (Fin (K+1)) ℤ) (A : ℕ)
    (hsize : ∀ K, h K ≤ K+1)
    (hrows : ∀ K, Function.Injective ((C K).map (Int.castRingHom ℝ)).vecMul)
    (hentry : ∀ K i j, |(C K i j : ℝ)| ≤ ((K+1 : ℕ) : ℝ)^A) :
    Tendsto (fun K => Real.log (realGram (C K)).det / (K : ℝ)^2) atTop (𝓝 0) := by
  have hlog : Tendsto (fun K : ℕ => Real.log (K : ℝ)/(K : ℝ)) atTop (𝓝 0) := by
    simpa [Function.comp_def] using (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp
      tendsto_natCast_atTop_atTop
  have hconst : Tendsto (fun K : ℕ => Real.log 2/(K : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hupper := (hconst.add hlog).const_mul (2 * ((2*A+2 : ℕ) : ℝ))
  simp only [add_zero, mul_zero] at hupper
  apply squeeze_zero' _ _ hupper
  · filter_upwards with K
    exact div_nonneg (Real.log_nonneg (one_le_det (C K) (hrows K))) (sq_nonneg _)
  · filter_upwards [eventually_ge_atTop 1] with K hK
    have hKR : (1 : ℝ) ≤ K := by exact_mod_cast hK
    have hKpos : (0 : ℝ) < K := lt_of_lt_of_le zero_lt_one hKR
    have hdetpos : 0 < (realGram (C K)).det := (realGram_posDef (C K) (hrows K)).det_pos
    have hlogbound := Real.log_le_log hdetpos (det_upper (C K) (hsize K) (hentry K))
    rw [Real.log_pow] at hlogbound
    have hlogK : 0 ≤ Real.log (K : ℝ) := Real.log_nonneg hKR
    have hlogtwo : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    have hlogsucc : Real.log ((K+1 : ℕ) : ℝ) ≤ Real.log 2 + Real.log K := by
      rw [← Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hKpos.ne']
      apply Real.log_le_log (by positivity)
      push_cast
      linarith
    have hdim : (((2*A+2)*(K+1) : ℕ) : ℝ) ≤ 2*(2*A+2 : ℕ)*(K : ℝ) := by
      push_cast
      nlinarith
    have hbound : Real.log (realGram (C K)).det ≤
        2*(2*A+2 : ℕ)*(K : ℝ)*(Real.log 2 + Real.log K) :=
      hlogbound.trans (mul_le_mul hdim hlogsucc (by positivity) (by positivity))
    apply (div_le_iff₀ (sq_pos_of_pos hKpos)).2
    convert hbound using 1 <;> (try field_simp [ne_of_gt hKpos]) <;> (try ring)

end ManuscriptChain.CoefficientGramGrowth

#print axioms ManuscriptChain.CoefficientGramGrowth.normalized_log_det_tendsto_zero
