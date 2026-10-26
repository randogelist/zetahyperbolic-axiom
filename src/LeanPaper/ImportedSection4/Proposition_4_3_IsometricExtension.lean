import LeanPaper.ImportedSection4.Proposition_4_3_PadicDisk
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Tactic

/-!
# Proposition 4.3: transport of the zero-free disk to an isometric
# nonarchimedean field extension

The core result is independent of p: any norm-preserving ring map of
nontrivially normed ultrametric fields transports the dominant-constant
zero-free disk. Applying the result to a translated polynomial over Z_p
supplies arbitrary p-adic integral centers and extension-valued arguments.

No algebraic-closure or arithmetic-witness hypothesis is assumed.
-/

noncomputable section
open Polynomial

namespace PaperAdvances.Proposition4_3_IsometricExtension

/-- Dominant-constant zero-free disks survive isometric extension of
nonarchimedean fields with their exact boundary norm. -/
theorem ISOMETRIC_EXTENSION_UNIT_DISK
    {K L : Type*}
    [NontriviallyNormedField K] [IsUltrametricDist K]
    [NontriviallyNormedField L] [IsUltrametricDist L]
    (φ : K →+* L) (hφ : ∀ y : K, ‖φ y‖ = ‖y‖)
    (P : K[X]) (z : L)
    (h0 : P.coeff 0 ≠ 0)
    (hcoeff : ∀ k : ℕ, 0 < k → ‖P.coeff k‖ ≤ 1)
    (hcenter : ‖P.coeff 0‖ ≤ 1)
    (hz : ‖z‖ < ‖P.coeff 0‖) :
    ‖(P.map φ).eval z‖ = ‖P.coeff 0‖ ∧
      (P.map φ).eval z ≠ 0 := by
  have hmap0 : (P.map φ).coeff 0 ≠ 0 := by
    intro heq
    apply h0
    apply norm_eq_zero.mp
    calc
      ‖P.coeff 0‖ = ‖φ (P.coeff 0)‖ := (hφ _).symm
      _ = ‖(P.map φ).coeff 0‖ := by simp only [Polynomial.coeff_map]
      _ = 0 := by rw [heq]; exact norm_zero
  have hmapcoeff (k : ℕ) (hk : 0 < k) :
      ‖(P.map φ).coeff k‖ ≤ 1 := by
    simpa only [Polynomial.coeff_map, hφ] using hcoeff k hk
  have hmapcenter : ‖(P.map φ).coeff 0‖ ≤ 1 := by
    simpa only [Polynomial.coeff_map, hφ] using hcenter
  have hmapz : ‖z‖ < ‖(P.map φ).coeff 0‖ := by
    simpa only [Polynomial.coeff_map, hφ] using hz
  have hresult :=
    PaperAdvances.Proposition4_3_PadicDisk.ultrametric_unit_coeff_disk
      (P.map φ) z hmap0 hmapcoeff hmapcenter hmapz
  refine ⟨?_, hresult.2⟩
  calc
    ‖(P.map φ).eval z‖ = ‖(P.map φ).coeff 0‖ := hresult.1
    _ = ‖P.coeff 0‖ := by simp only [Polynomial.coeff_map, hφ]

/-- Exact norm preservation for integral p-adic polynomial families,
but with evaluation in ANY isometrically extended ultrametric field. -/
theorem PROPOSITION_4_3_INTEGRAL_ISOMETRIC_EXTENSION
    {p : ℕ} [Fact p.Prime]
    {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L]
    (φ : ℚ_[p] →+* L) (hφ : ∀ y : ℚ_[p], ‖φ y‖ = ‖y‖)
    (Q : (ℤ_[p])[X]) (ξ : ℤ_[p]) (α : L)
    (hQ : Q.eval ξ ≠ 0)
    (hα : ‖α - φ (ξ : ℚ_[p])‖ <
      ‖((Q.eval ξ : ℤ_[p]) : ℚ_[p])‖) :
    ‖((Q.map (PadicInt.Coe.ringHom)).map φ).eval α‖ =
      ‖((Q.eval ξ : ℤ_[p]) : ℚ_[p])‖ ∧
    ((Q.map (PadicInt.Coe.ringHom)).map φ).eval α ≠ 0 := by
  let S : (ℤ_[p])[X] := Q.comp (Polynomial.X + Polynomial.C ξ)
  let T : (ℚ_[p])[X] := S.map (PadicInt.Coe.ringHom)
  have hS0 : S.coeff 0 = Q.eval ξ := by
    simp [S, Polynomial.coeff_zero_eq_eval_zero]
  have hT0 : T.coeff 0 = ((Q.eval ξ : ℤ_[p]) : ℚ_[p]) := by
    calc
      T.coeff 0 = (PadicInt.Coe.ringHom) (S.coeff 0) := by
        simp only [T, Polynomial.coeff_map]
      _ = (PadicInt.Coe.ringHom) (Q.eval ξ) := by rw [hS0]
      _ = ((Q.eval ξ : ℤ_[p]) : ℚ_[p]) := rfl
  have hcoeff (k : ℕ) : ‖T.coeff k‖ ≤ 1 := by
    have hmap : T.coeff k = (PadicInt.Coe.ringHom) (S.coeff k) := by
      simp only [T, Polynomial.coeff_map]
    rw [hmap]
    change ‖((S.coeff k : ℤ_[p]) : ℚ_[p])‖ ≤ 1
    exact (S.coeff k).property
  have hT0ne : T.coeff 0 ≠ 0 := by
    rw [hT0]
    exact PadicInt.coe_ne_zero.mpr hQ
  have hT0le : ‖T.coeff 0‖ ≤ 1 := by
    rw [hT0]
    exact (Q.eval ξ).property
  have hball : ‖α - φ (ξ : ℚ_[p])‖ < ‖T.coeff 0‖ := by
    simpa only [hT0] using hα
  have hraw := ISOMETRIC_EXTENSION_UNIT_DISK φ hφ T
    (α - φ (ξ : ℚ_[p])) hT0ne (fun k _ => hcoeff k) hT0le hball
  have heval : ((T.map φ)).eval (α - φ (ξ : ℚ_[p])) =
      ((Q.map (PadicInt.Coe.ringHom)).map φ).eval α := by
    -- `PadicInt.Coe.ringHom` is the subtype coercion. Make that
    -- equality explicit before cancelling the translation in L.
    have hcast : (PadicInt.Coe.ringHom) ξ = (ξ : ℚ_[p]) := rfl
    simp [T, S, Polynomial.map_comp, Polynomial.eval_comp, hcast]
  constructor
  · simpa only [heval, hT0] using hraw.1
  · simpa only [heval] using hraw.2

end PaperAdvances.Proposition4_3_IsometricExtension

#print axioms PaperAdvances.Proposition4_3_IsometricExtension.ISOMETRIC_EXTENSION_UNIT_DISK
#print axioms PaperAdvances.Proposition4_3_IsometricExtension.PROPOSITION_4_3_INTEGRAL_ISOMETRIC_EXTENSION
