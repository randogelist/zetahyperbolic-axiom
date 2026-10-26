import LeanPaper.BeukersIntegralPencil
import LeanPaper.BeukersDenominator

/-!
# Theorem 6.2: actual asymmetric Beukers moments

The additional geometric denominator is treated by an absolutely integrable
series of actual adjacent moments. Thus the zeta-six term is identified with
the printed unit-square integral, rather than postulated as an affine symbol.
-/

noncomputable section
open MeasureTheory Set
open scoped BigOperators

namespace ManuscriptChain.Beukers

/-- The first exact integral asserted in Theorem 6.2(1). -/
theorem adjacent_moment (m : ℕ) :
    (∫ z, z.1 ^ m * z.2 ^ (m + 1) * density z ∂squareMeasure) =
      1 / (6 * ((m + 1 : ℕ) : ℝ) ^ 6) := by
  have hne : m ≠ m + 1 := by omega
  have he : offdiagonalRational m (m + 1) = Real.dualConstant 7 m (m + 1) := by
    simp [offdiagonalRational, Real.dualConstant, hne]
  rw [offdiagonal_moment_eq_rat m (m + 1) hne, he,
    LeanPaper.BeukersDenominator.adjacent_dualConstant]
  push_cast <;> rfl

lemma integral_norm_adjacent_moment (m : ℕ) :
    (∫ z, ‖z.1 ^ m * z.2 ^ (m + 1) * density z‖ ∂squareMeasure) =
      1 / (6 * ((m + 1 : ℕ) : ℝ) ^ 6) := by
  rw [← adjacent_moment m]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioo)] with z hz
  exact _root_.Real.norm_of_nonneg
    (mul_nonneg (mul_nonneg (pow_nonneg hz.1.1.le _) (pow_nonneg hz.2.1.le _))
      (density_strictly_positive_on_square z hz).le)

lemma summable_integral_norm_adjacent (r : ℕ) :
    Summable (fun n : ℕ =>
      ∫ z, ‖z.1 ^ (r + n) * z.2 ^ (r + n + 1) * density z‖ ∂squareMeasure) := by
  simp_rw [integral_norm_adjacent_moment]
  have h := (Real.zeta_tail_summable (s := 6) (by norm_num) r).mul_left (1 / 6 : ℝ)
  convert h using 1
  funext n
  rw [one_div_mul_one_div]

/-- The literal extra-denominator integrand in equation (6.2). -/
def shiftedKernel (r : ℕ) (z : ℝ × ℝ) : ℝ :=
  (z.1 * z.2) ^ r * z.2 / (1 - z.1 * z.2) * density z

lemma shiftedKernel_eq_tsum (r : ℕ) {z : ℝ × ℝ} (hz : z ∈ square) :
    shiftedKernel r z =
      ∑' n : ℕ, z.1 ^ (r + n) * z.2 ^ (r + n + 1) * density z := by
  have hxy0 : 0 < z.1 * z.2 := mul_pos hz.1.1 hz.2.1
  have hxy1 : z.1 * z.2 < 1 := by
    have h := mul_lt_mul_of_pos_right hz.1.2 hz.2.1
    nlinarith [hz.2.2]
  have hnorm : ‖z.1 * z.2‖ < 1 := by
    simpa only [_root_.Real.norm_eq_abs, abs_of_pos hxy0] using hxy1
  have h := (hasSum_geometric_of_norm_lt_one hnorm).mul_left
    ((z.1 * z.2) ^ r * z.2 * density z)
  have he : (fun n : ℕ => z.1 ^ (r + n) * z.2 ^ (r + n + 1) * density z) =
      (fun n : ℕ => ((z.1 * z.2) ^ r * z.2 * density z) * (z.1 * z.2) ^ n) := by
    funext n
    simp only [pow_add, pow_one, mul_pow]
    ring
  rw [he, h.tsum_eq]
  unfold shiftedKernel
  ring

/-- The second integral in Theorem 6.2(1), with the series/integral exchange proved. -/
theorem shiftedKernel_integral (r : ℕ) :
    (∫ z, shiftedKernel r z ∂squareMeasure) =
      (1 / 6 : ℝ) * (Real.zeta 6 - (Real.harmonic 6 r : ℝ)) := by
  calc
    _ = ∫ z, ∑' n : ℕ, z.1 ^ (r + n) * z.2 ^ (r + n + 1) * density z
        ∂squareMeasure := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioo)] with z hz
      exact shiftedKernel_eq_tsum r hz
    _ = ∑' n : ℕ, ∫ z, z.1 ^ (r + n) * z.2 ^ (r + n + 1) * density z
        ∂squareMeasure :=
      (integral_tsum_of_summable_integral_norm
        (fun n => density_monomial_integrable (r + n) (r + n + 1))
        (summable_integral_norm_adjacent r)).symm
    _ = ∑' n : ℕ, (1 / 6 : ℝ) * (1 / ((r + n + 1 : ℕ) : ℝ) ^ 6) := by
      apply tsum_congr
      intro n
      rw [adjacent_moment]
      rw [one_div_mul_one_div]
    _ = _ := by rw [tsum_mul_left, Real.zeta_tail_sum (s := 6) (by norm_num) r]

/-- The actual extra-denominator kernel is integrable for every shift. -/
theorem shiftedKernel_integrable (r : ℕ) : Integrable (shiftedKernel r) squareMeasure := by
  apply Integrable.of_integral_ne_zero
  rw [shiftedKernel_integral]
  have hpos : 0 < Real.zeta 6 - (Real.harmonic 6 r : ℝ) := by
    rw [← Real.zeta_tail_sum (s := 6) (by norm_num) r]
    exact (Real.zeta_tail_summable (s := 6) (by norm_num) r).tsum_pos
      (fun n => by positivity) 0 (by positivity)
  positivity

/-- Evaluation of the second, asymmetric polynomial in the printed integral. -/
def shiftedPolynomialKernel {K : ℕ} (c : Fin (K + 1) → ℚ) (z : ℝ × ℝ) : ℝ :=
  coefficientEval c (z.1 * z.2) * z.2 / (1 - z.1 * z.2) * density z

theorem shiftedPolynomialKernel_eq_sum {K : ℕ} (c : Fin (K + 1) → ℚ)
    (z : ℝ × ℝ) :
    shiftedPolynomialKernel c z = ∑ r : Fin (K + 1), (c r : ℝ) * shiftedKernel r.val z := by
  unfold shiftedPolynomialKernel coefficientEval
  simp only [Finset.sum_mul, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro r hr
  unfold shiftedKernel
  ring

theorem shiftedPolynomialKernel_integrable {K : ℕ} (c : Fin (K + 1) → ℚ) :
    Integrable (shiftedPolynomialKernel c) squareMeasure := by
  have h : Integrable (fun z => ∑ r : Fin (K + 1), (c r : ℝ) * shiftedKernel r.val z)
      squareMeasure := by
    apply integrable_finset_sum
    intro r hr
    exact (shiftedKernel_integrable r.val).const_mul _
  apply h.congr
  exact Filter.Eventually.of_forall (fun z => (shiftedPolynomialKernel_eq_sum c z).symm)

def diagonalCoefficient {K : ℕ} (c : Fin (K + 1) → ℚ) : ℚ := ∑ r, c r * c r
def linearCoefficient {K : ℕ} (c : Fin (K + 1) → ℚ) : ℚ := ∑ r, c r
def constantCoefficient {K : ℕ} (c : Fin (K + 1) → ℚ) : ℚ :=
  ∑ r, ∑ t, c r * c t * Real.dualConstant 7 r.val t.val
def harmonicSixCoefficient {K : ℕ} (c : Fin (K + 1) → ℚ) : ℚ :=
  ∑ r, c r * Real.harmonic 6 r.val

theorem shiftedPolynomialKernel_integral {K : ℕ} (c : Fin (K + 1) → ℚ) :
    (∫ z, shiftedPolynomialKernel c z ∂squareMeasure) =
      (1 / 6 : ℝ) * ((linearCoefficient c : ℝ) * Real.zeta 6 -
        (harmonicSixCoefficient c : ℝ)) := by
  simp_rw [shiftedPolynomialKernel_eq_sum]
  rw [integral_finset_sum]
  · simp_rw [integral_const_mul, shiftedKernel_integral]
    have he (r : Fin (K + 1)) :
        (c r : ℝ) * ((1 / 6 : ℝ) * (Real.zeta 6 - (Real.harmonic 6 r.val : ℝ))) =
        (1 / 6 : ℝ) * ((c r : ℝ) * Real.zeta 6 -
          (c r : ℝ) * (Real.harmonic 6 r.val : ℝ)) := by ring
    simp_rw [he]
    rw [← Finset.mul_sum, Finset.sum_sub_distrib, ← Finset.sum_mul]
    simp [linearCoefficient, harmonicSixCoefficient]
  · intro r hr
    exact (shiftedKernel_integrable r.val).const_mul _

theorem polynomial_pair_integral_affine {K : ℕ} (c : Fin (K + 1) → ℚ) :
    (∫ z, coefficientEval c z.1 * coefficientEval c z.2 * density z ∂squareMeasure) =
      (constantCoefficient c : ℝ) + (diagonalCoefficient c : ℝ) * Real.zeta 7 := by
  have h := integral_polynomial_pair_eq_dualEntry (fun _ : Fin 1 => c) 0 0
  simpa [Real.dualEntry, constantCoefficient, diagonalCoefficient] using h

/-- The printed rational correction, using the already identified dual moments.
Expanding `dualConstant` gives the diagonal harmonic-seven terms and the
off-diagonal harmonic-six divided differences with the manuscript's signs. -/
def simultaneousRationalPart {K : ℕ} (c : Fin (K + 1) → ℚ) (α β : ℤ) : ℚ :=
  -(α : ℚ) * constantCoefficient c + (β : ℚ) * harmonicSixCoefficient c

/-- Explicit identification with the printed diagonal and off-diagonal formula. -/
theorem simultaneousRationalPart_eq_printed {K : ℕ}
    (c : Fin (K + 1) → ℚ) (α β : ℤ) :
    simultaneousRationalPart c α β =
      (α : ℚ) * (∑ r, c r ^ 2 * Real.harmonic 7 r.val) -
      (α : ℚ) / 6 * (∑ r, ∑ t ∈ Finset.univ.erase r,
        c r * c t * (Real.harmonic 6 r.val - Real.harmonic 6 t.val) /
          ((r.val : ℚ) - (t.val : ℚ))) +
      (β : ℚ) * (∑ r, c r * Real.harmonic 6 r.val) := by
  classical
  have hs (r : Fin (K + 1)) :
      (∑ t, c r * c t * Real.dualConstant 7 r.val t.val) =
      -(c r ^ 2 * Real.harmonic 7 r.val) +
        (1 / 6 : ℚ) * (∑ t ∈ Finset.univ.erase r,
          c r * c t * (Real.harmonic 6 r.val - Real.harmonic 6 t.val) /
            ((r.val : ℚ) - (t.val : ℚ))) := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ r)]
    have he : (∑ t ∈ Finset.univ.erase r, c r * c t *
        Real.dualConstant 7 r.val t.val) =
        (1 / 6 : ℚ) * (∑ t ∈ Finset.univ.erase r,
          c r * c t * (Real.harmonic 6 r.val - Real.harmonic 6 t.val) /
            ((r.val : ℚ) - (t.val : ℚ))) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro t ht
      have hne : r.val ≠ t.val := by
        simpa only [Fin.val_inj] using Ne.symm (Finset.ne_of_mem_erase ht)
      simp only [Real.dualConstant, hne, if_false]
      norm_num only [Nat.reduceSub, Nat.cast_ofNat]
      ring
    rw [he]
    simp only [Real.dualConstant, if_true]
    ring
  have hc : constantCoefficient c =
      -(∑ r, c r ^ 2 * Real.harmonic 7 r.val) +
        (1 / 6 : ℚ) * (∑ r, ∑ t ∈ Finset.univ.erase r,
          c r * c t * (Real.harmonic 6 r.val - Real.harmonic 6 t.val) /
            ((r.val : ℚ) - (t.val : ℚ))) := by
    unfold constantCoefficient
    simp_rw [hs]
    rw [Finset.sum_add_distrib, Finset.sum_neg_distrib, ← Finset.mul_sum]
  unfold simultaneousRationalPart harmonicSixCoefficient
  rw [hc]
  ring

/-- The literal density-weighted integrand from Theorem 6.2(2). -/
def simultaneousKernel {K : ℕ} (c : Fin (K + 1) → ℚ) (α β : ℤ)
    (z : ℝ × ℝ) : ℝ :=
  ((α : ℝ) * coefficientEval c z.1 * coefficientEval c z.2 +
    6 * (β : ℝ) * coefficientEval c (z.1 * z.2) * z.2 / (1 - z.1 * z.2)) * density z

theorem simultaneousKernel_eq {K : ℕ} (c : Fin (K + 1) → ℚ) (α β : ℤ)
    (z : ℝ × ℝ) :
    simultaneousKernel c α β z =
      (α : ℝ) * (coefficientEval c z.1 * coefficientEval c z.2 * density z) +
        (6 * (β : ℝ)) * shiftedPolynomialKernel c z := by
  unfold simultaneousKernel shiftedPolynomialKernel
  ring

theorem simultaneousKernel_integrable {K : ℕ} (c : Fin (K + 1) → ℚ) (α β : ℤ) :
    Integrable (simultaneousKernel c α β) squareMeasure := by
  apply (((polynomial_pair_integrable c c).const_mul (α : ℝ)).add
    ((shiftedPolynomialKernel_integrable c).const_mul (6 * (β : ℝ)))).congr
  exact Filter.Eventually.of_forall (fun z => (simultaneousKernel_eq c α β z).symm)

/-- The actual single integral is the simultaneous zeta-seven/zeta-six form. -/
theorem simultaneousKernel_integral {K : ℕ} (c : Fin (K + 1) → ℚ) (α β : ℤ) :
    (∫ z, simultaneousKernel c α β z ∂squareMeasure) =
      (α : ℝ) * (diagonalCoefficient c : ℝ) * Real.zeta 7 +
      (β : ℝ) * (linearCoefficient c : ℝ) * Real.zeta 6 -
      (simultaneousRationalPart c α β : ℝ) := by
  simp_rw [simultaneousKernel_eq]
  rw [integral_add ((polynomial_pair_integrable c c).const_mul (α : ℝ))
    ((shiftedPolynomialKernel_integrable c).const_mul (6 * (β : ℝ))),
    integral_const_mul, integral_const_mul, polynomial_pair_integral_affine,
    shiftedPolynomialKernel_integral]
  unfold simultaneousRationalPart
  push_cast
  ring

/-- The integer-coefficient form has exactly the same `6*d_K^7` denominator. -/
theorem simultaneousRationalPart_denominator (K : ℕ) (c : Fin (K + 1) → ℤ) (α β : ℤ) :
    6 * (LeanPaper.BeukersDenominator.commonDenominator K : ℚ) ^ 7 *
      simultaneousRationalPart (fun r => (c r : ℚ)) α β ∈
        LeanPaper.BeukersDenominator.integerRationals := by
  let S := LeanPaper.BeukersDenominator.integerRationals
  let d : ℚ := LeanPaper.BeukersDenominator.commonDenominator K
  have hc (r : Fin (K + 1)) : (c r : ℚ) ∈ S := ⟨c r, rfl⟩
  have hα : (α : ℚ) ∈ S := ⟨α, rfl⟩
  have hβ : (β : ℚ) ∈ S := ⟨β, rfl⟩
  have hconstant : 6 * d ^ 7 * constantCoefficient (fun r => (c r : ℚ)) ∈ S := by
    unfold constantCoefficient
    rw [Finset.mul_sum]
    apply Subring.sum_mem
    intro r hr
    rw [Finset.mul_sum]
    apply Subring.sum_mem
    intro t ht
    have h := S.mul_mem (S.mul_mem (hc r) (hc t))
      (LeanPaper.BeukersDenominator.dualConstant_seven_denominator K r.val t.val
        (by omega) (by omega))
    convert h using 1 <;> dsimp [d] <;> ring
  have hsix : 6 * d ^ 7 * harmonicSixCoefficient (fun r => (c r : ℚ)) ∈ S := by
    unfold harmonicSixCoefficient
    rw [Finset.mul_sum]
    apply Subring.sum_mem
    intro r hr
    have h := S.mul_mem (LeanPaper.BeukersDenominator.nat_mem 6)
      (S.mul_mem (LeanPaper.BeukersDenominator.nat_mem
        (LeanPaper.BeukersDenominator.commonDenominator K))
        (S.mul_mem (hc r)
          (LeanPaper.BeukersDenominator.harmonic_denominator 6 K r.val (by omega))))
    convert h using 1 <;> dsimp [d] <;> ring
  have h := S.add_mem (S.neg_mem (S.mul_mem hα hconstant)) (S.mul_mem hβ hsix)
  change 6 * d ^ 7 * simultaneousRationalPart (fun r => (c r : ℚ)) α β ∈ S
  convert h using 1 <;> unfold simultaneousRationalPart <;> ring

/-- Full Theorem 6.2 on the actual Beukers measure. The rational part is
constructed above from the exact harmonic divided differences; its common
denominator is proved here, not assumed as an arithmetic budget. -/
theorem theorem_6_2 (K : ℕ) (c : Fin (K + 1) → ℤ) (α β : ℤ) :
    (∀ m : ℕ, (∫ z, z.1 ^ m * z.2 ^ (m + 1) ∂beukersMeasure) =
      1 / (6 * ((m + 1 : ℕ) : ℝ) ^ 6)) ∧
    (∀ r : ℕ, (∫ z, (z.1 * z.2) ^ r * z.2 / (1 - z.1 * z.2) ∂beukersMeasure) =
      (1 / 6 : ℝ) * (Real.zeta 6 - (Real.harmonic 6 r : ℝ))) ∧
    (∫ z, (α : ℝ) * coefficientEval (fun r => (c r : ℚ)) z.1 *
        coefficientEval (fun r => (c r : ℚ)) z.2 +
      6 * (β : ℝ) * coefficientEval (fun r => (c r : ℚ)) (z.1 * z.2) * z.2 /
        (1 - z.1 * z.2) ∂beukersMeasure) =
      (α : ℝ) * (diagonalCoefficient (fun r => (c r : ℚ)) : ℝ) * Real.zeta 7 +
      (β : ℝ) * (linearCoefficient (fun r => (c r : ℚ)) : ℝ) * Real.zeta 6 -
      (simultaneousRationalPart (fun r => (c r : ℚ)) α β : ℝ) ∧
    6 * (LeanPaper.BeukersDenominator.commonDenominator K : ℚ) ^ 7 *
      simultaneousRationalPart (fun r => (c r : ℚ)) α β ∈
        LeanPaper.BeukersDenominator.integerRationals := by
  refine ⟨?_, ?_, ?_, simultaneousRationalPart_denominator K c α β⟩
  · intro m
    rw [integral_beukersMeasure]
    exact adjacent_moment m
  · intro r
    rw [integral_beukersMeasure]
    exact shiftedKernel_integral r
  · rw [integral_beukersMeasure]
    exact simultaneousKernel_integral (fun r => (c r : ℚ)) α β

end ManuscriptChain.Beukers

#print axioms ManuscriptChain.Beukers.adjacent_moment
#print axioms ManuscriptChain.Beukers.shiftedKernel_integral
#print axioms ManuscriptChain.Beukers.shiftedKernel_integrable
#print axioms ManuscriptChain.Beukers.simultaneousKernel_integral
#print axioms ManuscriptChain.Beukers.simultaneousRationalPart_eq_printed
#print axioms ManuscriptChain.Beukers.simultaneousRationalPart_denominator
#print axioms ManuscriptChain.Beukers.theorem_6_2
