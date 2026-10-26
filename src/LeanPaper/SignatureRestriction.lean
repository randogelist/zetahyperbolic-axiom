import Mathlib.LinearAlgebra.QuadraticForm.Signature
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic

/-!
# Signature bounds under restriction

These dimension inequalities are the counting form of Cauchy interlacing.
They do not presume that a restricted matrix is nonsingular.
-/
noncomputable section
open QuadraticForm QuadraticMap

namespace ManuscriptChain.SignatureRestriction

variable {E F : Type*} [AddCommGroup E] [Module ℝ E]
    [AddCommGroup F] [Module ℝ F] [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

/-- Positive index cannot increase under an injective pullback. -/
theorem sigPos_comp_le (Q : QuadraticForm ℝ F) (f : E →ₗ[ℝ] F)
    (hf : Function.Injective f) : sigPos (Q.comp f) ≤ sigPos Q := by
  obtain ⟨V, hdim, hV⟩ := exists_finrank_eq_sigPos_and_posDef (Q.comp f)
  have hp : (Q.restrict (V.map f)).PosDef := by
    rintro ⟨x, hx⟩ hx0
    obtain ⟨y, hy, rfl⟩ := hx
    apply hV ⟨y, hy⟩
    intro hy0
    apply hx0
    apply Subtype.ext
    have : y = 0 := congrArg Subtype.val hy0
    simpa [this]
  have h := le_sigPos_of_posDef Q hp
  rw [← (Submodule.equivMapOfInjective f hf V).finrank_eq, hdim] at h
  exact h

/-- Upper bound complementary to monotonicity: restricting loses at most
the codimension in the positive index. -/
theorem sigPos_le_restrict_add_codimension (Q : QuadraticForm ℝ E)
    (S : Submodule ℝ E) :
    sigPos Q + Module.finrank ℝ S ≤
      sigPos (Q.restrict S) + Module.finrank ℝ E := by
  obtain ⟨V, hdim, hV⟩ := exists_finrank_eq_sigPos_and_posDef Q
  let T := V ⊓ S
  have hTS : T ≤ S := inf_le_right
  have hp : ((Q.restrict S).restrict (T.comap S.subtype)).PosDef := by
    intro x hx
    apply hV ⟨x.val.val, x.property.1⟩
    intro hz
    apply hx
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun v : V => (v : E)) hz
  have hbound := le_sigPos_of_posDef (Q.restrict S) hp
  have hTeq := (Submodule.comapSubtypeEquivOfLe hTS).finrank_eq
  rw [hTeq] at hbound
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq V S
  have hsup := (V ⊔ S).finrank_le
  dsimp only [T] at hbound
  omega

/-- Both exact finite-dimensional signature bounds for restriction. -/
theorem signature_restriction_bounds (Q : QuadraticForm ℝ E)
    (S : Submodule ℝ E) :
    sigPos (Q.restrict S) ≤ sigPos Q ∧
      sigPos Q + Module.finrank ℝ S ≤
        sigPos (Q.restrict S) + Module.finrank ℝ E := by
  exact ⟨sigPos_comp_le Q S.subtype Subtype.val_injective,
    sigPos_le_restrict_add_codimension Q S⟩

/-- A codimension-one restriction changes the positive index by zero or one. -/
theorem sigPos_codimension_one (Q : QuadraticForm ℝ E)
    (S : Submodule ℝ E) (hcodim : Module.finrank ℝ S + 1 = Module.finrank ℝ E) :
    sigPos (Q.restrict S) ≤ sigPos Q ∧ sigPos Q ≤ sigPos (Q.restrict S) + 1 := by
  have h := signature_restriction_bounds Q S
  exact ⟨h.1, by omega⟩

/-- Full pullback bounds, with dimension of the domain rather than a chosen range. -/
theorem signature_comp_bounds (Q : QuadraticForm ℝ F) (f : E →ₗ[ℝ] F)
    (hf : Function.Injective f) :
    sigPos (Q.comp f) ≤ sigPos Q ∧
      sigPos Q + Module.finrank ℝ E ≤ sigPos (Q.comp f) + Module.finrank ℝ F := by
  let e := LinearEquiv.ofInjective f hf
  have heq : sigPos (Q.restrict f.range) = sigPos (Q.comp f) := by
    have he : (Q.restrict f.range).Equivalent ((Q.restrict f.range).comp e.toLinearMap) :=
      ⟨QuadraticMap.isometryEquivOfCompLinearEquiv (Q.restrict f.range) e⟩
    exact he.sigPos_eq
  have h := signature_restriction_bounds Q f.range
  rw [heq, LinearMap.finrank_range_of_inj hf] at h
  exact h

end ManuscriptChain.SignatureRestriction
