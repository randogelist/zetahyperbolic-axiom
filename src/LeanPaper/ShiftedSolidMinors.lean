import MAIN_CHAIN_ASSEMBLED
import Theorem_3_1_Pole_Integral_Identity
import Mathlib.Tactic

/-!
# Shifted moment positivity

The concrete moment measure is supported on the positive half-line. Multiplying
it by any monomial preserves atomlessness and nonzero mass, and every moment
remains integrable. Consequently every shifted sparse principal moment matrix
is positive definite. In particular, all solid mixed minors of the actual
Hankel matrix are strictly positive, in arbitrary order and at arbitrary offsets.

This does not yet assert positivity of mixed minors with unrelated gaps.
-/

noncomputable section
open scoped BigOperators
open MeasureTheory Set Matrix

namespace ManuscriptChain.ConcreteMoment

theorem momentMeasure_ae_pos (p : Real.Parameters) :
    ∀ᵐ t ∂momentMeasure p, 0 < t := by
  rw [momentMeasure, ae_map_iff (by fun_prop) measurableSet_Ioi]
  have hpos : ∀ᵐ y ∂weightedMeasure p, 0 < y :=
    (withDensity_absolutelyContinuous _ _).ae_le
      (ae_restrict_mem measurableSet_Ioi)
  filter_upwards [hpos] with y hy
  exact sq_pos_of_pos hy

/-- Monomial tilting of the actual positive moment measure. -/
def shiftedMomentMeasure (p : Real.Parameters) (a : ℕ) : Measure ℝ :=
  (momentMeasure p).withDensity (fun t => ENNReal.ofReal (t ^ a))

instance shiftedMomentMeasure_nullSingleton (p : Real.Parameters) (a : ℕ) :
    NullSingletonClass (shiftedMomentMeasure p a) := by
  unfold shiftedMomentMeasure
  infer_instance

theorem shiftedMomentMeasure_nonzero (p : Real.Parameters) (a : ℕ) :
    shiftedMomentMeasure p a ≠ 0 := by
  have hac : momentMeasure p ≪ shiftedMomentMeasure p a := by
    apply withDensity_absolutelyContinuous' (by fun_prop)
    filter_upwards [momentMeasure_ae_pos p] with t ht
    exact ne_of_gt (ENNReal.ofReal_pos.mpr (pow_pos ht a))
  intro hz
  rw [hz] at hac
  exact momentMeasure_nonzero p (Measure.absolutelyContinuous_zero_iff.mp hac)

theorem integrable_moment (p : Real.Parameters) (a : ℕ) :
    Integrable (fun t : ℝ => t ^ a) (momentMeasure p) :=
  (integrable_momentMeasure_iff p a).2 (integrableOn_weightedDensity_moment p a)

theorem integrable_shifted_moment (p : Real.Parameters) (a b : ℕ) :
    Integrable (fun t : ℝ => t ^ b) (shiftedMomentMeasure p a) := by
  rw [shiftedMomentMeasure,
    integrable_withDensity_iff_integrable_smul' (by fun_prop) (by simp)]
  apply (integrable_moment p (a + b)).congr
  filter_upwards [momentMeasure_ae_pos p] with t ht
  rw [ENNReal.toReal_ofReal (pow_nonneg ht.le a), smul_eq_mul, pow_add]

theorem integral_shifted_moment (p : Real.Parameters) (a b : ℕ) :
    (∫ t, t ^ b ∂shiftedMomentMeasure p a) =
      ∫ t, t ^ (a + b) ∂momentMeasure p := by
  rw [shiftedMomentMeasure,
    integral_withDensity_eq_integral_toReal_smul (by fun_prop) (by simp)]
  apply integral_congr_ae
  filter_upwards [momentMeasure_ae_pos p] with t ht
  rw [ENNReal.toReal_ofReal (pow_nonneg ht.le a), smul_eq_mul, pow_add]

/-- Positive definiteness for arbitrary distinct monomial exponents, with
an arbitrary nonnegative integral shift of the measure. -/
theorem sparse_shifted_momentMatrix_posDef (p : Real.Parameters) (a : ℕ)
    {r : ℕ} (e : Fin r → ℕ) (he : Function.Injective e) :
    Matrix.PosDef (fun i j : Fin r => ∫ t, t ^ (a + e i + e j) ∂momentMeasure p) := by
  let d := Finset.univ.sup e + 1
  let choose : Fin r → Fin d := fun i =>
    ⟨e i, Nat.lt_succ_of_le (Finset.le_sup (f := e) (Finset.mem_univ i))⟩
  have hchoose : Function.Injective choose := by
    intro i j hij
    apply he
    exact congrArg Fin.val hij
  have hpd := Moments.momentMatrix_posDef (shiftedMomentMeasure_nonzero p a)
    (fun i j : Fin d => integrable_shifted_moment p a (i.val + j.val))
  have hs := hpd.submatrix hchoose
  have heq :
      (fun i j : Fin r => ∫ t, t ^ (a + e i + e j) ∂momentMeasure p) =
        (Moments.momentMatrix (shiftedMomentMeasure p a) d).submatrix choose choose := by
    ext i j
    simp only [Matrix.submatrix_apply, Moments.momentMatrix, choose,
      integral_shifted_moment, Nat.add_assoc]
  rw [heq]
  exact hs

/-- Strict positivity of every shifted sparse principal moment determinant. -/
theorem sparse_shifted_moment_det_pos (p : Real.Parameters) (a : ℕ)
    {r : ℕ} (e : Fin r → ℕ) (he : Function.Injective e) :
    0 < Matrix.det (fun i j : Fin r =>
      ∫ t, t ^ (a + e i + e j) ∂momentMeasure p) :=
  (sparse_shifted_momentMatrix_posDef p a e he).det_pos

/-- Every solid mixed Hankel minor is strictly positive. The row and column
offsets need not coincide, and the order is arbitrary. -/
theorem solid_moment_det_pos (p : Real.Parameters) (a b r : ℕ) :
    0 < Matrix.det (fun i j : Fin r =>
      ∫ t, t ^ ((a + i.val) + (b + j.val)) ∂momentMeasure p) := by
  simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
    sparse_shifted_moment_det_pos p (a + b) (fun i : Fin r => i.val) Fin.val_injective

end ManuscriptChain.ConcreteMoment

namespace ManuscriptChain

/-- The matrix at the zeta center is the actual infinite moment kernel,
restricted to the manuscript dimension. -/
theorem gram_eq_moment (p : Real.Parameters) (hp : Real.Admissible p)
    (i j : Fin p.h) :
    Real.gram p (Real.zeta p.weight) i j =
      ∫ t, t ^ (i.val + j.val) ∂ConcreteMoment.momentMeasure p :=
  (Hyperbolic.gram_eq_weighted_integral p hp
    (Hyperbolic.poleIntegralIdentity p.k hp.k_pos) i j).trans
    (ConcreteMoment.integral_momentMeasure p _).symm

/-- Mixed minors with the same arbitrary sparse pattern at different row and
column offsets are strictly positive in every order. -/
theorem GRAM_TRANSLATED_SPARSE_MINOR_POSITIVE
    (p : Real.Parameters) (hp : Real.Admissible p) (a b : ℕ)
    {r : ℕ} (e : Fin r → ℕ) (he : Function.Injective e)
    (ha : ∀ i, a + e i < p.h) (hb : ∀ i, b + e i < p.h) :
    0 < Matrix.det ((Real.gram p (Real.zeta p.weight)).submatrix
      (fun i => (⟨a + e i, ha i⟩ : Fin p.h))
      (fun j => (⟨b + e j, hb j⟩ : Fin p.h))) := by
  have heq :
      (Real.gram p (Real.zeta p.weight)).submatrix
        (fun i => (⟨a + e i, ha i⟩ : Fin p.h))
        (fun j => (⟨b + e j, hb j⟩ : Fin p.h)) =
        (fun i j : Fin r =>
          ∫ t, t ^ (a + b + e i + e j) ∂ConcreteMoment.momentMeasure p) := by
    ext i j
    simpa only [Matrix.submatrix_apply, gram_eq_moment p hp,
      Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
  rw [heq]
  simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
    ConcreteMoment.sparse_shifted_moment_det_pos p (a + b) e he

/-- Every solid submatrix within the actual pencil has positive determinant.
No numerical bound on the order or shifts occurs in the proof. -/
theorem GRAM_SOLID_MINOR_POSITIVE (p : Real.Parameters) (hp : Real.Admissible p)
    (a b r : ℕ) (ha : a + r ≤ p.h) (hb : b + r ≤ p.h) :
    0 < Matrix.det ((Real.gram p (Real.zeta p.weight)).submatrix
      (fun i : Fin r => (⟨a + i.val, by omega⟩ : Fin p.h))
      (fun j : Fin r => (⟨b + j.val, by omega⟩ : Fin p.h))) := by
  convert ConcreteMoment.solid_moment_det_pos p a b r using 1
  congr 1
  ext i j
  exact gram_eq_moment p hp _ _

end ManuscriptChain

#print axioms ManuscriptChain.ConcreteMoment.sparse_shifted_moment_det_pos
#print axioms ManuscriptChain.GRAM_TRANSLATED_SPARSE_MINOR_POSITIVE
#print axioms ManuscriptChain.GRAM_SOLID_MINOR_POSITIVE
