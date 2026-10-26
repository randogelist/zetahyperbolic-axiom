import Theorem_3_1_General_Odd_Weight_Endpoint
import Theorem_3_1_Positive_Moment_Realization
import Theorem_4_1_Spectral_Irrationality_Measure_Criterion

/-!
# General odd-zeta Diophantine application

For an arbitrary family at one fixed odd weight, primitive integer polynomials
are constructed from the actual determinant. Positive Gram matrices supply
nonzero values and local comparison on a radius constructed from the spectral
factors. Evaluation upper bounds and a compatible index budget remain explicit
quantitative hypotheses. No uniform odd-zeta irrationality claim is made.
-/

noncomputable section
open scoped BigOperators
open Polynomial

namespace ManuscriptChain.GeneralArithmetic

/-- Primitive normalization is constructed, not an additional hypothesis. -/
def primitiveNormalization (p : Real.Parameters) :
    BasisInvariance.PrimitiveNormalization (Real.delta p) :=
  BasisInvariance.primitiveNormalization (Real.delta p) (General.delta_nonzero p)

def primitivePolynomial (p : Real.Parameters) : ℤ[X] :=
  (primitiveNormalization p).polynomial

def primitiveMultiplier (p : Real.Parameters) : ℚ :=
  (primitiveNormalization p).scale

theorem primitive_isPrimitive (p : Real.Parameters) :
    (primitivePolynomial p).IsPrimitive := (primitiveNormalization p).primitive

theorem primitiveMultiplier_pos (p : Real.Parameters) :
    0 < primitiveMultiplier p := (primitiveNormalization p).scale_pos

theorem primitive_polynomial_identity (p : Real.Parameters) :
    (primitivePolynomial p).map (Int.castRingHom ℚ) =
      C (primitiveMultiplier p) * Real.delta p :=
  (primitiveNormalization p).identity

theorem primitive_real_identity (p : Real.Parameters) :
    (primitivePolynomial p).map (algebraMap ℤ ℝ) =
      C (primitiveMultiplier p : ℝ) * Real.realPolynomial (Real.delta p) := by
  have hcomp : (Rat.castHom ℝ).comp (Int.castRingHom ℚ) = Int.castRingHom ℝ := by
    ext z
    simp
  have h := congrArg (Polynomial.map (Rat.castHom ℝ)) (primitive_polynomial_identity p)
  simpa [Polynomial.map_map, hcomp, Real.realPolynomial] using h

theorem primitive_degree (p : Real.Parameters) :
    (primitivePolynomial p).natDegree = p.h := by
  have hinj : Function.Injective (Int.castRingHom ℚ) := by
    intro a b hab
    change (a : ℚ) = (b : ℚ) at hab
    exact_mod_cast hab
  have hdegree := congrArg Polynomial.natDegree (primitive_polynomial_identity p)
  rw [Polynomial.natDegree_map_eq_of_injective hinj, Polynomial.natDegree_C_mul
    (ne_of_gt (primitiveMultiplier_pos p)), General.delta_degree] at hdegree
  exact hdegree

theorem primitive_eval (p : Real.Parameters) (x : ℝ) :
    RealTransfer.evalReal (primitivePolynomial p) x =
      (primitiveMultiplier p : ℝ) * Real.evalQ (Real.delta p) x := by
  unfold RealTransfer.evalReal
  rw [primitive_real_identity]
  simp [Real.evalQ]

theorem primitive_eval_nonzero (p : Real.Parameters) (positive : General.GramPositive p) :
    RealTransfer.evalReal (primitivePolynomial p) (Real.zeta p.weight) ≠ 0 := by
  rw [primitive_eval]
  apply mul_ne_zero
  · exact_mod_cast ne_of_gt (primitiveMultiplier_pos p)
  · exact General.center_nonvanishing p positive

/-- Inverse multiplier expresses the real determinant as a scalar times Q. -/
theorem determinant_normalization (p : Real.Parameters) :
    (Real.manuscriptPencil p).detPolynomial =
      C ((primitiveMultiplier p : ℝ)⁻¹) *
        (primitivePolynomial p).map (algebraMap ℤ ℝ) := by
  rw [primitive_real_identity, ← mul_assoc, ← map_mul]
  have hs : (primitiveMultiplier p : ℝ) ≠ 0 := by
    exact_mod_cast ne_of_gt (primitiveMultiplier_pos p)
  rw [inv_mul_cancel₀ hs, map_one, one_mul]
  exact Real.manuscriptPencil_detPolynomial p

/-- Structural parameters: one fixed weight and an admissible tail. -/
structure OddWeightFamily where
  k : ℕ
  onset : ℕ
  parameters : ℕ → Real.Parameters
  k_fixed : ∀ n, (parameters n).k = k
  admissible : ∀ n, onset ≤ n → Real.Admissible (parameters n)

namespace OddWeightFamily

def center (F : OddWeightFamily) : ℝ := Real.zeta (2 * F.k + 1)

def Q (F : OddWeightFamily) (n : ℕ) : ℤ[X] := primitivePolynomial (F.parameters n)

theorem weight_eq (F : OddWeightFamily) (n : ℕ) :
    (F.parameters n).weight = 2 * F.k + 1 := by
  simp [Real.Parameters.weight, F.k_fixed n]

theorem k_pos (F : OddWeightFamily) : 0 < F.k := by
  have h := (F.admissible F.onset le_rfl).k_pos
  simpa [F.k_fixed] using h

theorem center_eq_riemannZeta (F : OddWeightFamily) :
    F.center = (riemannZeta ((2 * F.k + 1 : ℕ) : ℂ)).re := by
  apply Real.zeta_eq_riemannZeta_re
  have h := F.k_pos
  omega

theorem degree (F : OddWeightFamily) (n : ℕ) :
    (F.Q n).natDegree = (F.parameters n).h := primitive_degree _

end OddWeightFamily

def GramPositiveFamily (F : OddWeightFamily) : Prop :=
  ∀ n, F.onset ≤ n → General.GramPositive (F.parameters n)

/-- The exact maximum spectral factor, with harmless data before the onset. -/
def familySpectralBound (F : OddWeightFamily) (positive : GramPositiveFamily F) (n : ℕ) : ℝ :=
  if hn : F.onset ≤ n then
    General.spectralRadius (F.parameters n) (F.admissible n hn) (positive n hn)
  else 1

def localRadius (F : OddWeightFamily) (positive : GramPositiveFamily F) (n : ℕ) : ℝ :=
  Spectral.comparisonRadius (F.parameters n).h (familySpectralBound F positive n)

theorem familySpectralBound_pos (F : OddWeightFamily) (positive : GramPositiveFamily F)
    (n : ℕ) : 0 < familySpectralBound F positive n := by
  unfold familySpectralBound
  split
  · exact General.spectralRadius_pos _ _ _
  · norm_num

theorem localRadius_pos (F : OddWeightFamily) (positive : GramPositiveFamily F)
    (n : ℕ) : 0 < localRadius F positive n :=
  Spectral.comparisonRadius_pos _ _ (familySpectralBound_pos F positive n)

theorem family_eval_nonzero (F : OddWeightFamily) (positive : GramPositiveFamily F)
    (n : ℕ) (hn : F.onset ≤ n) : RealTransfer.evalReal (F.Q n) F.center ≠ 0 := by
  simpa [OddWeightFamily.Q, OddWeightFamily.center, F.weight_eq n] using
    primitive_eval_nonzero (F.parameters n) (positive n hn)

/-- Spectral local comparison is derived for the actual normalized family. -/
theorem localComparison (F : OddWeightFamily) (positive : GramPositiveFamily F) :
    RealTransfer.LocalComparison F.Q F.center (localRadius F positive) F.onset := by
  apply Spectral.localComparison_of_spectral F.Q F.center
    (fun n => (F.parameters n).h) (fun n => Real.manuscriptPencil (F.parameters n))
    (familySpectralBound F positive) (fun n => (primitiveMultiplier (F.parameters n) : ℝ)⁻¹)
    F.onset (fun n hn => General.factorization (F.parameters n) (positive n hn))
  · intro n _
    simp [Real.manuscriptPencil_center, OddWeightFamily.center, F.weight_eq n]
  · intro n _
    exact familySpectralBound_pos F positive n
  · intro n hn i
    simpa [familySpectralBound, hn] using
      General.beta_abs_le (F.parameters n) (F.admissible n hn) (positive n hn) i
  · intro n _
    apply inv_ne_zero
    exact_mod_cast ne_of_gt (primitiveMultiplier_pos (F.parameters n))
  · intro n _
    exact determinant_normalization (F.parameters n)

/-- Only the upper estimate is an input: nonvanishing is derived from positivity. -/
def EvaluationUpper (F : OddWeightFamily) (budget : ℕ → ℝ) : Prop :=
  ∀ n, F.onset ≤ n → |RealTransfer.evalReal (F.Q n) F.center| ≤ budget n

theorem decay (F : OddWeightFamily) (positive : GramPositiveFamily F)
    (budget : ℕ → ℝ) (upper : EvaluationUpper F budget) :
    RealTransfer.Decay F.Q F.center budget F.onset :=
  ⟨family_eval_nonzero F positive, upper⟩

/-- General arithmetic endpoint: all remaining quantitative input is explicit. -/
theorem general_measure_and_irrational
    (F : OddWeightFamily) (positive : GramPositiveFamily F)
    (budget : ℕ → ℝ) (μ b₀ : ℕ) (upper : EvaluationUpper F budget)
    (index : RealTransfer.IndexBudget F.Q (localRadius F positive) budget F.onset μ b₀) :
    RealTransfer.RationalMeasure F.center μ b₀ ∧ Irrational F.center := by
  have h := RealTransfer.conditional_measure (localComparison F positive)
    (decay F positive budget upper) index
  exact ⟨h, h.irrational⟩

/-- The same endpoint identified with Mathlib's named odd zeta value. -/
theorem general_riemannZeta_measure_and_irrational
    (F : OddWeightFamily) (positive : GramPositiveFamily F)
    (budget : ℕ → ℝ) (μ b₀ : ℕ) (upper : EvaluationUpper F budget)
    (index : RealTransfer.IndexBudget F.Q (localRadius F positive) budget F.onset μ b₀) :
    RealTransfer.RationalMeasure (riemannZeta ((2 * F.k + 1 : ℕ) : ℂ)).re μ b₀ ∧
      Irrational (riemannZeta ((2 * F.k + 1 : ℕ) : ℂ)).re := by
  rw [← F.center_eq_riemannZeta]
  exact general_measure_and_irrational F positive budget μ b₀ upper index

/-- A family of actual moment realizations supplies the analytic input. -/
theorem positivityFromMoments (F : OddWeightFamily)
    (realization : ∀ n, F.onset ≤ n → Real.PositiveMomentRealization (F.parameters n)) :
    GramPositiveFamily F :=
  fun n hn => (realization n hn).gram_posDef

theorem general_measure_and_irrational_from_moments
    (F : OddWeightFamily)
    (realization : ∀ n, F.onset ≤ n → Real.PositiveMomentRealization (F.parameters n))
    (budget : ℕ → ℝ) (μ b₀ : ℕ) (upper : EvaluationUpper F budget)
    (index : RealTransfer.IndexBudget F.Q
      (localRadius F (positivityFromMoments F realization)) budget F.onset μ b₀) :
    RealTransfer.RationalMeasure F.center μ b₀ ∧ Irrational F.center :=
  general_measure_and_irrational F (positivityFromMoments F realization)
    budget μ b₀ upper index

end ManuscriptChain.GeneralArithmetic

#print axioms ManuscriptChain.GeneralArithmetic.primitive_degree
#print axioms ManuscriptChain.GeneralArithmetic.localComparison
#print axioms ManuscriptChain.GeneralArithmetic.general_measure_and_irrational
#print axioms ManuscriptChain.GeneralArithmetic.general_measure_and_irrational_from_moments
