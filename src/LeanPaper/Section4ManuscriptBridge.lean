import LeanPaper.ImportedSection4.Theorem_4_6_Leading_Coefficient_Determinant_Barrier
import LeanPaper.ImportedSection4.Theorem_4_7_Finite_Root_Cluster_Count
import LeanPaper.ImportedSection4.Proposition_4_3_ComplexPadicDisk
import Theorem_4_1_Leading_Coefficient_Gap

/-!
# Finite arithmetic and clustering inputs for the actual manuscript pencil

The imported Section 4 inequalities are applied to the constructed primitive
integer polynomial and the constructed spectral factors of the manuscript.
Every size, average, and p-adic-center nonvanishing condition remains explicit.
No determinant asymptotic, numerical root fraction, or irrationality endpoint
is inferred from these finite identities.
-/

noncomputable section
open scoped BigOperators
open Polynomial

namespace LeanPaper.Section4ManuscriptBridge
open ManuscriptChain
open GeneralIrrationality LeadingCoefficientGap

/-- The actual integer leading coefficient equals the center value times
the inverse Gram/slope determinant ratio, in absolute value. -/
theorem primitive_leading_barrier_identity
    (p : Real.Parameters) (hp : Real.Admissible p) :
    (((|(primitivePolynomial p).leadingCoeff| : ℤ) : ℝ)) =
      |RealTransfer.evalReal (primitivePolynomial p) (Real.zeta p.weight)| *
        |1 / determinantRatio p| := by
  have hratio : 0 < determinantRatio p := determinantRatio_pos p hp
  have hlead : 0 < leadingSize p := lt_of_lt_of_le (by norm_num) (leadingSize_ge_one p)
  rw [Int.cast_abs]
  change leadingSize p = _
  rw [primitivePolynomial_eval_eq,
    abs_of_pos (mul_pos hlead hratio), abs_of_pos (one_div_pos.mpr hratio)]
  field_simp [hratio.ne']

/-- A finite upper bound on the relative determinant gives an actual
lower bound on the manuscript primitive polynomial's center value. -/
theorem primitive_evaluation_lower_of_inverse_ratio_bound
    (p : Real.Parameters) (hp : Real.Admissible p) (T : ℝ)
    (hT : 0 < T) (hbound : |1 / determinantRatio p| ≤ T) :
    1 / T ≤ |RealTransfer.evalReal (primitivePolynomial p) (Real.zeta p.weight)| := by
  exact PaperOrder.Section4.theorem_4_6_reciprocal_evaluation_lower_bound
    (primitivePolynomial p).leadingCoeff
    (RealTransfer.evalReal (primitivePolynomial p) (Real.zeta p.weight))
    (1 / determinantRatio p) T
    (Polynomial.leadingCoeff_ne_zero.mpr (primitivePolynomial_isPrimitive p).ne_zero)
    (primitive_leading_barrier_identity p hp) hT hbound

/-- Logarithmic magnitudes of the actual nonzero spectral factors. -/
def spectralExponent (p : Real.Parameters) (hp : Real.Admissible p)
    (i : Fin p.h) : ℝ :=
  _root_.Real.log |(General.factorization p (GRAM_POSITIVE p hp)).beta i|

/-- The finite list preserves multiplicities and has exactly p.h entries. -/
def spectralExponentList (p : Real.Parameters) (hp : Real.Admissible p) : List ℝ :=
  List.ofFn (spectralExponent p hp)

/-- The finite counting estimate now concerns the actual manuscript spectrum.
Uniform upper and average lower bounds are not supplied by this theorem. -/
theorem manuscript_spectral_cluster_fraction
    (p : Real.Parameters) (hp : Real.Admissible p) (U τ μ : ℝ)
    (hU : τ < U)
    (hcap : ∀ i : Fin p.h, spectralExponent p hp i ≤ U)
    (haverage : μ * (p.h : ℝ) ≤ ∑ i : Fin p.h, spectralExponent p hp i) :
    (μ - τ) / (U - τ) * (p.h : ℝ) ≤
      (PaperOrder.Section4.countAtLeastThreshold τ (spectralExponentList p hp) : ℝ) := by
  have hcount :
    (μ - τ) / (U - τ) * ((spectralExponentList p hp).length : ℝ) ≤
      (PaperOrder.Section4.countAtLeastThreshold τ (spectralExponentList p hp) : ℝ)
      := PaperOrder.Section4.theorem_4_7_cluster_fraction_lower_bound
        (spectralExponentList p hp) U τ μ hU
        (by
          intro x hx
          obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
          exact hcap i)
        (by simpa [spectralExponentList, List.sum_ofFn] using haverage)
  simpa [spectralExponentList] using hcount

/-- Every counted exponent gives an actual determinant root within the
corresponding exponential radius of the odd-zeta center. -/
theorem manuscript_large_exponent_gives_close_root
    (p : Real.Parameters) (hp : Real.Admissible p) (τ : ℝ) (i : Fin p.h)
    (hlarge : τ ≤ spectralExponent p hp i) :
    let r := (General.factorization p (GRAM_POSITIVE p hp)).root i
    Real.evalQ (Real.delta p) r = 0 ∧
      |r - Real.zeta p.weight| ≤ _root_.Real.exp (-τ) := by
  let c := General.factorization p (GRAM_POSITIVE p hp)
  have hbeta : 0 < |c.beta i| := abs_pos.mpr (c.beta_ne_zero i)
  have hexp : _root_.Real.exp τ ≤ |c.beta i| :=
    (_root_.Real.le_log_iff_exp_le hbeta).mp hlarge
  have hroot : Real.evalQ (Real.delta p) (c.root i) = 0 := by
    simpa only [Real.manuscriptPencil_detPolynomial, Real.evalQ] using c.eval_root i
  refine ⟨hroot, ?_⟩
  have hdist : |c.root i - Real.zeta p.weight| = 1 / |c.beta i| := by
    simpa only [Real.manuscriptPencil_center] using c.root_distance i
  change |c.root i - Real.zeta p.weight| ≤ _root_.Real.exp (-τ)
  rw [hdist, _root_.Real.exp_neg, ← one_div]
  exact one_div_le_one_div_of_le (_root_.Real.exp_pos τ) hexp

/-- The complex p-adic disk theorem applies to the actual constructed
primitive integer polynomial. Its center nonvanishing and disk membership
are the precise hypotheses; no p-adic zeta identification is assumed. -/
theorem manuscript_primitive_complex_padic_disk
    (params : Real.Parameters) {q : ℕ} [Fact q.Prime]
    (ξ : ℤ_[q]) (α : ℂ_[q])
    (hQ : ((primitivePolynomial params).map (Int.castRingHom (ℤ_[q]))).eval ξ ≠ 0)
    (hα : ‖α - ((ξ : ℚ_[q]) : ℂ_[q])‖ <
      ‖((((primitivePolynomial params).map (Int.castRingHom (ℤ_[q]))).eval ξ :
        ℤ_[q]) : ℚ_[q])‖) :
    ‖((((primitivePolynomial params).map (Int.castRingHom (ℤ_[q]))).map
      (PadicInt.Coe.ringHom)).map (algebraMap ℚ_[q] ℂ_[q])).eval α‖ =
      ‖((((primitivePolynomial params).map (Int.castRingHom (ℤ_[q]))).eval ξ :
        ℤ_[q]) : ℚ_[q])‖ ∧
    ((((primitivePolynomial params).map (Int.castRingHom (ℤ_[q]))).map
      (PadicInt.Coe.ringHom)).map (algebraMap ℚ_[q] ℂ_[q])).eval α ≠ 0 := by
  exact PaperAdvances.Proposition4_3_ComplexPadicDisk.PROPOSITION_4_3_INTEGER_COMPLEX_PADIC
    (primitivePolynomial params) ξ α hQ hα

end LeanPaper.Section4ManuscriptBridge
