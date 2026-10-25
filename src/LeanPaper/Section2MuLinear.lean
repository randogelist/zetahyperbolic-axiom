import LeanPaper.Section2LagrangeFunctional
import LeanPaper.Section2RatFuncPullback

/-! The manuscript's exact simple-negative-square-pole domain is a rational
vector subspace, and the representation-independent mu value is a linear map
on it. This excludes the auxiliary zero pole used by the ambient extension. -/
noncomputable section
open scoped BigOperators
open Polynomial
namespace LeanPaper.Section2MuLinear
open Section2RepresentationIndependence Section2PoleLinearSpace
open Section2RatFuncPullback Zetahyperbolic

def zeroForm : RatMomentElem := ⟨0, 0, fun _ => 0⟩

def addForm (R S : RatMomentElem) : RatMomentElem :=
  ⟨R.polyPart+S.polyPart, max R.maxPole S.maxPole,
    fun j => effectiveResidue (muForm R) j + effectiveResidue (muForm S) j⟩

def smulForm (c : ℚ) (R : RatMomentElem) : RatMomentElem :=
  ⟨c • R.polyPart, R.maxPole, fun j => c * R.poleRes j⟩

theorem realization_add (R S : RatMomentElem) :
    muRatFunc (addForm R S) = muRatFunc R + muRatFunc S := by
  have hs : Finset.Icc 1 (max R.maxPole S.maxPole) =
      Finset.Icc 1 R.maxPole ∪ Finset.Icc 1 S.maxPole := by
    ext j
    simp only [Finset.mem_Icc, Finset.mem_union]
    omega
  have hf : muForm (addForm R S) = Section2PoleLinearSpace.addForm (muForm R) (muForm S) := by
    simp only [muForm, addForm, Section2PoleLinearSpace.addForm, hs]
  rw [muRatFunc, hf, Section2PoleLinearSpace.realization_add]
  rfl

theorem realization_smul (c : ℚ) (R : RatMomentElem) :
    muRatFunc (smulForm c R) = (algebraMap ℚ (RatFunc ℚ) c) * muRatFunc R := by
  exact Section2PoleLinearSpace.realization_smul _ c (muForm R)

def MuSpace : Submodule ℚ (RatFunc ℚ) where
  carrier := MuDomain
  zero_mem' := ⟨zeroForm, by simp [muRatFunc, muForm, zeroForm, realization]⟩
  add_mem' := by
    rintro f g ⟨R, rfl⟩ ⟨S, rfl⟩
    exact ⟨addForm R S, realization_add R S⟩
  smul_mem' := by
    rintro c f ⟨R, rfl⟩
    refine ⟨smulForm c R, ?_⟩
    simpa only [Algebra.smul_def] using realization_smul c R

def mu (k : ℕ) : MuSpace →ₗ[ℚ] ℚ[X] :=
  (Section2LagrangeFunctional.mu k).comp MuSpace.subtype

theorem mu_eq_existing (k : ℕ) (f : MuSpace) :
    mu k f = muOnDomain k ⟨(f : RatFunc ℚ), f.property⟩ := by
  let R := Classical.choose f.property
  have hR : muRatFunc R = (f : RatFunc ℚ) := Classical.choose_spec f.property
  change Section2LagrangeFunctional.mu k (f : RatFunc ℚ) = muFunctionalPoly k R
  rw [← hR, Section2LagrangeFunctional.mu_eq_existing]

/-- The canonical weighted square substitution as a linear map between the
exact manuscript rational-function domains. -/
def pullback (k : ℕ) : MuSpace →ₗ[ℚ] Section2TauLinear.TauSpace where
  toFun f := weightedPullback k ⟨(f : RatFunc ℚ), f.property⟩
  map_add' f g := by
    apply Subtype.ext
    simp only [weightedPullback_coe, Submodule.coe_add, map_add, mul_add]
  map_smul' c f := by
    apply Subtype.ext
    simp only [weightedPullback_coe, Submodule.coe_smul, Algebra.smul_def,
      map_mul, AlgHom.commutes]
    ring

@[simp] theorem pullback_coe (k : ℕ) (f : MuSpace) :
    (pullback k f : RatFunc ℚ) =
      RatFunc.X^(2*k+1) * substitution (f : RatFunc ℚ) :=
  weightedPullback_coe k _

/-- The exact domain linear map obeys the literal weighted RatFunc pullback. -/
theorem mu_pullback (k : ℕ) (hk : 1 ≤ k) (f : MuSpace) :
    mu k f = Section2TauLinear.tau k
      (pullback k f) := by
  rw [mu_eq_existing]
  exact rational_functional_pullback k hk _

end LeanPaper.Section2MuLinear
