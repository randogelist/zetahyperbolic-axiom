import LeanPaper.Section2RationalDomains
import Mathlib.FieldTheory.RatFunc.AsPolynomial

/-!
The finite simple-pole domain is a genuine rational vector subspace of RatFunc.
The operations are constructed on raw normal-form data. A linear polynomial
action and prescribed pole values descend to a linear map on this subspace by
the proved partial-fraction uniqueness theorem.
-/

noncomputable section
open scoped BigOperators
open Polynomial

namespace LeanPaper.Section2PoleLinearSpace
open Section2RepresentationIndependence

variable {ι : Type*} [DecidableEq ι]

def zeroForm : SimplePoleForm ι := ⟨0, ∅, fun _ => 0⟩

def addForm (F G : SimplePoleForm ι) : SimplePoleForm ι :=
  ⟨F.polynomial + G.polynomial, F.support ∪ G.support,
    fun i => effectiveResidue F i + effectiveResidue G i⟩

def smulForm (c : ℚ) (F : SimplePoleForm ι) : SimplePoleForm ι :=
  ⟨c • F.polynomial, F.support, fun i => c * F.residue i⟩

theorem realization_zero (nodes : ι → ℚ) : realization nodes zeroForm = 0 := by
  simp [realization, zeroForm]

theorem realization_add (nodes : ι → ℚ) (F G : SimplePoleForm ι) :
    realization nodes (addForm F G) = realization nodes F + realization nodes G := by
  rw [realization_extend nodes F (F.support ∪ G.support) Finset.subset_union_left,
    realization_extend nodes G (F.support ∪ G.support) Finset.subset_union_right]
  simp only [realization, addForm, map_add, add_div, Finset.sum_add_distrib]
  abel

theorem realization_smul (nodes : ι → ℚ) (c : ℚ) (F : SimplePoleForm ι) :
    realization nodes (smulForm c F) = (algebraMap ℚ (RatFunc ℚ) c) * realization nodes F := by
  have hc : RatFunc.C c = (algebraMap ℚ (RatFunc ℚ)) c :=
    (map_ratCast RatFunc.C c).trans (map_ratCast (algebraMap ℚ (RatFunc ℚ)) c).symm
  simp only [realization, smulForm, Polynomial.smul_eq_C_mul, map_mul,
    RatFunc.algebraMap_C, hc, mul_add, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem moment_add (polyMoment : ℚ[X] →ₗ[ℚ] ℚ[X]) (poleMoment : ι → ℚ[X])
    (F G : SimplePoleForm ι) :
    moment polyMoment poleMoment (addForm F G) =
      moment polyMoment poleMoment F + moment polyMoment poleMoment G := by
  unfold moment
  simp only [addForm, map_add]
  rw [sum_extend F (F.support ∪ G.support) Finset.subset_union_left
      (fun i c => C c * poleMoment i) (by intro i; simp),
    sum_extend G (F.support ∪ G.support) Finset.subset_union_right
      (fun i c => C c * poleMoment i) (by intro i; simp)]
  simp only [map_add, add_mul, Finset.sum_add_distrib]
  abel

theorem moment_smul (polyMoment : ℚ[X] →ₗ[ℚ] ℚ[X]) (poleMoment : ι → ℚ[X])
    (c : ℚ) (F : SimplePoleForm ι) :
    moment polyMoment poleMoment (smulForm c F) =
      c • moment polyMoment poleMoment F := by
  change polyMoment (c • F.polynomial) +
    ∑ i ∈ F.support, C (c * F.residue i) * poleMoment i = _
  rw [map_smul]
  simp only [moment, smul_add, Finset.smul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Polynomial.smul_eq_C_mul, map_mul]
  ring

def poleSubmodule (nodes : ι → ℚ) : Submodule ℚ (RatFunc ℚ) where
  carrier := Set.range (realization nodes)
  zero_mem' := ⟨zeroForm, realization_zero nodes⟩
  add_mem' := by
    rintro f g ⟨F, rfl⟩ ⟨G, rfl⟩
    exact ⟨addForm F G, realization_add nodes F G⟩
  smul_mem' := by
    rintro c f ⟨F, rfl⟩
    refine ⟨smulForm c F, ?_⟩
    simpa only [Algebra.smul_def] using realization_smul nodes c F

def value (nodes : ι → ℚ) (polyMoment : ℚ[X] →ₗ[ℚ] ℚ[X])
    (poleMoment : ι → ℚ[X]) (f : poleSubmodule nodes) : ℚ[X] :=
  moment polyMoment poleMoment (Classical.choose f.property)

theorem value_eq_of_representation (nodes : ι → ℚ)
    (hnodes : Function.Injective nodes) (polyMoment : ℚ[X] →ₗ[ℚ] ℚ[X])
    (poleMoment : ι → ℚ[X]) (f : poleSubmodule nodes) (F : SimplePoleForm ι)
    (hF : realization nodes F = (f : RatFunc ℚ)) :
    value nodes polyMoment poleMoment f = moment polyMoment poleMoment F := by
  apply moment_representation_independent nodes hnodes polyMoment poleMoment
  exact (Classical.choose_spec f.property).trans hF.symm

def liftMoment (nodes : ι → ℚ) (hnodes : Function.Injective nodes)
    (polyMoment : ℚ[X] →ₗ[ℚ] ℚ[X]) (poleMoment : ι → ℚ[X]) :
    poleSubmodule nodes →ₗ[ℚ] ℚ[X] where
  toFun := value nodes polyMoment poleMoment
  map_add' f g := by
    let F := Classical.choose f.property
    let G := Classical.choose g.property
    have hF : realization nodes F = (f : RatFunc ℚ) := Classical.choose_spec f.property
    have hG : realization nodes G = (g : RatFunc ℚ) := Classical.choose_spec g.property
    have hsum : realization nodes (addForm F G) = ((f + g : poleSubmodule nodes) : RatFunc ℚ) := by
      rw [realization_add, hF, hG]
      rfl
    rw [value_eq_of_representation nodes hnodes polyMoment poleMoment (f + g) _ hsum,
      value_eq_of_representation nodes hnodes polyMoment poleMoment f _ hF,
      value_eq_of_representation nodes hnodes polyMoment poleMoment g _ hG]
    exact moment_add polyMoment poleMoment F G
  map_smul' c f := by
    let F := Classical.choose f.property
    have hF : realization nodes F = (f : RatFunc ℚ) := Classical.choose_spec f.property
    have hsmul : realization nodes (smulForm c F) = ((c • f : poleSubmodule nodes) : RatFunc ℚ) := by
      rw [realization_smul, hF]
      rw [Submodule.coe_smul, Algebra.smul_def]
    rw [value_eq_of_representation nodes hnodes polyMoment poleMoment (c • f) _ hsmul,
      value_eq_of_representation nodes hnodes polyMoment poleMoment f _ hF]
    exact moment_smul polyMoment poleMoment c F

theorem liftMoment_eq (nodes : ι → ℚ) (hnodes : Function.Injective nodes)
    (polyMoment : ℚ[X] →ₗ[ℚ] ℚ[X]) (poleMoment : ι → ℚ[X]) (F : SimplePoleForm ι) :
    liftMoment nodes hnodes polyMoment poleMoment ⟨realization nodes F, ⟨F, rfl⟩⟩ =
      moment polyMoment poleMoment F :=
  value_eq_of_representation nodes hnodes polyMoment poleMoment _ F rfl

end LeanPaper.Section2PoleLinearSpace
