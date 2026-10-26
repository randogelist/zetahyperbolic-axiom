import LeanPaper.ShiftedSolidMinors
import Mathlib.MeasureTheory.Integral.Pi

/-!
# Actual mixed-minor Andreief identity

The double-permutation proof is adapted from upload 17,
`Zeta5/Sec6/Gram.lean` (`factorial_mul_det`, `andreief`). Its two polynomial
bases are allowed to differ here. The final theorem applies the identity to
the actual manuscript Gram matrix and its actual positive moment measure.
This proves the integral identity for every mixed minor; strict positivity
still requires the sign of both generalized Vandermonde determinants.
-/
noncomputable section
open scoped BigOperators
open Matrix MeasureTheory Set

namespace LeanPaper.ActualMixedAndreief

theorem factorial_mul_det {m : ℕ} (M : Matrix (Fin m) (Fin m) ℝ) :
    (m.factorial : ℝ) * M.det =
      ∑ σ : Equiv.Perm (Fin m), ∑ τ : Equiv.Perm (Fin m),
        ((Equiv.Perm.sign σ : ℤ) : ℝ) * ((Equiv.Perm.sign τ : ℤ) : ℝ) *
          ∏ k, M (σ k) (τ k) := by
  rw [Finset.sum_comm]
  have key (τ : Equiv.Perm (Fin m)) :
      (∑ σ : Equiv.Perm (Fin m),
        ((Equiv.Perm.sign σ : ℤ) : ℝ) * ((Equiv.Perm.sign τ : ℤ) : ℝ) *
          ∏ k, M (σ k) (τ k)) = M.det := by
    have h1 := Matrix.det_permute' τ M
    rw [Matrix.det_apply'] at h1
    simp only [Matrix.submatrix_apply, id] at h1
    have hs : ((Equiv.Perm.sign τ : ℤ) : ℝ) *
        ((Equiv.Perm.sign τ : ℤ) : ℝ) = 1 := by
      rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self]
      simp
    calc
      _ = ((Equiv.Perm.sign τ : ℤ) : ℝ) *
          ∑ σ : Equiv.Perm (Fin m), ((Equiv.Perm.sign σ : ℤ) : ℝ) *
            ∏ k, M (σ k) (τ k) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun σ _ => by ring)
      _ = M.det := by rw [h1, ← mul_assoc, hs, one_mul]
  simp_rw [key]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm,
    Fintype.card_fin, nsmul_eq_mul]

/-- Andreief with two genuinely different bases. -/
theorem mixed_andreief {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [SigmaFinite μ] {m : ℕ}
    (φ ψ : Fin m → α → ℝ)
    (hint : ∀ i j, Integrable (fun x => φ i x * ψ j x) μ) :
    (m.factorial : ℝ) * (fun i j => ∫ x, φ i x * ψ j x ∂μ).det =
      ∫ x : Fin m → α,
        (fun i k => φ i (x k)).det * (fun j k => ψ j (x k)).det
          ∂(Measure.pi fun _ => μ) := by
  rw [factorial_mul_det]
  have hprod (σ τ : Equiv.Perm (Fin m)) :
      (∏ k, ∫ x, φ (σ k) x * ψ (τ k) x ∂μ) =
        ∫ x : Fin m → α, ∏ k, φ (σ k) (x k) * ψ (τ k) (x k)
          ∂(Measure.pi fun _ => μ) :=
    (integral_fintype_prod_eq_prod
      (f := fun k x => φ (σ k) x * ψ (τ k) x)).symm
  have hI (σ τ : Equiv.Perm (Fin m)) :
      Integrable (fun x : Fin m → α =>
        ∏ k, φ (σ k) (x k) * ψ (τ k) (x k)) (Measure.pi fun _ => μ) :=
    Integrable.fintype_prod (fun k => hint (σ k) (τ k))
  simp_rw [hprod, ← integral_const_mul]
  have hinner (σ : Equiv.Perm (Fin m)) :
      (∑ τ : Equiv.Perm (Fin m), ∫ x : Fin m → α,
        ((Equiv.Perm.sign σ : ℤ) : ℝ) * ((Equiv.Perm.sign τ : ℤ) : ℝ) *
          ∏ k, φ (σ k) (x k) * ψ (τ k) (x k) ∂(Measure.pi fun _ => μ)) =
      ∫ x : Fin m → α, ∑ τ : Equiv.Perm (Fin m),
        ((Equiv.Perm.sign σ : ℤ) : ℝ) * ((Equiv.Perm.sign τ : ℤ) : ℝ) *
          ∏ k, φ (σ k) (x k) * ψ (τ k) (x k) ∂(Measure.pi fun _ => μ) :=
    (integral_finsetSum _ (fun τ _ => (hI σ τ).const_mul _)).symm
  rw [Finset.sum_congr rfl (fun σ _ => hinner σ)]
  rw [← integral_finsetSum _ (fun σ _ =>
    integrable_finsetSum _ (fun τ _ => (hI σ τ).const_mul _))]
  congr 1
  funext x
  rw [Matrix.det_apply', Matrix.det_apply', Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro σ _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro τ _
  rw [Finset.prod_mul_distrib]
  ring

open ManuscriptChain

theorem actual_momentMeasure_finite (p : Real.Parameters) :
    IsFiniteMeasure (ConcreteMoment.momentMeasure p) := by
  apply (integrable_const_iff_isFiniteMeasure (by norm_num : (1 : ℝ) ≠ 0)).mp
  simpa only [pow_zero] using ConcreteMoment.integrable_moment p 0

/-- The two exponent patterns are independent, with no positivity witness
or determinant-integral identity supplied as a hypothesis. -/
theorem actual_mixed_moment_identity (p : Real.Parameters) {r : ℕ}
    (rows cols : Fin r → ℕ) :
    (r.factorial : ℝ) *
      (fun i j : Fin r => ∫ t, t^(rows i + cols j)
        ∂ConcreteMoment.momentMeasure p).det =
      ∫ t : Fin r → ℝ,
        (fun i k : Fin r => (t k)^(rows i)).det *
        (fun j k : Fin r => (t k)^(cols j)).det
        ∂(Measure.pi fun _ => ConcreteMoment.momentMeasure p) := by
  letI := actual_momentMeasure_finite p
  simpa only [← pow_add] using
    mixed_andreief (ConcreteMoment.momentMeasure p)
      (fun i t => t^(rows i)) (fun j t => t^(cols j))
      (fun i j => by
        simpa only [pow_add] using
          ConcreteMoment.integrable_moment p (rows i + cols j))

/-- Exact Andreief formula for every mixed minor of the actual matrix at zeta. -/
theorem actual_gram_mixed_minor_identity (p : Real.Parameters)
    (hp : Real.Admissible p) {r : ℕ} (rows cols : Fin r → Fin p.h) :
    (r.factorial : ℝ) *
      ((Real.gram p (Real.zeta p.weight)).submatrix rows cols).det =
      ∫ t : Fin r → ℝ,
        (fun i k : Fin r => (t k)^(rows i).val).det *
        (fun j k : Fin r => (t k)^(cols j).val).det
        ∂(Measure.pi fun _ => ConcreteMoment.momentMeasure p) := by
  have heq : (Real.gram p (Real.zeta p.weight)).submatrix rows cols =
      fun i j => ∫ t, t^((rows i).val + (cols j).val)
        ∂ConcreteMoment.momentMeasure p := by
    ext i j
    exact gram_eq_moment p hp _ _
  rw [heq]
  exact actual_mixed_moment_identity p _ _

end LeanPaper.ActualMixedAndreief

#print axioms LeanPaper.ActualMixedAndreief.mixed_andreief
#print axioms LeanPaper.ActualMixedAndreief.actual_gram_mixed_minor_identity
