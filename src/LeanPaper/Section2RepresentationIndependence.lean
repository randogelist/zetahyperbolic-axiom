import LeanPaper.Section2LagrangeIdentification
import LeanPaper.PullbackReflection
import Mathlib.Algebra.Polynomial.PartialFractions
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.FieldTheory.RatFunc.Basic

/-!
Representation independence in the actual rational-function field.
Two finite simple-pole expressions may use different finite supports. Equality
in RatFunc ℚ forces equality of their polynomial parts and of their residues
after extension by zero. The manuscript μ therefore descends to its actual
simple negative-square-pole domain, rather than depending on the stored bound.
-/

noncomputable section
open scoped BigOperators
open Polynomial

namespace LeanPaper.Section2RepresentationIndependence

structure SimplePoleForm (ι : Type*) where
  polynomial : ℚ[X]
  support : Finset ι
  residue : ι → ℚ

variable {ι : Type*} [DecidableEq ι]

def effectiveResidue (F : SimplePoleForm ι) (i : ι) : ℚ :=
  if i ∈ F.support then F.residue i else 0

def realization (nodes : ι → ℚ) (F : SimplePoleForm ι) : RatFunc ℚ :=
  algebraMap ℚ[X] (RatFunc ℚ) F.polynomial +
    ∑ i ∈ F.support,
      algebraMap ℚ[X] (RatFunc ℚ) (C (F.residue i)) /
        algebraMap ℚ[X] (RatFunc ℚ) (X - C (nodes i))

theorem sum_extend {A : Type*} [AddCommMonoid A] (F : SimplePoleForm ι)
    (t : Finset ι) (ht : F.support ⊆ t) (f : ι → ℚ → A)
    (hf : ∀ i, f i 0 = 0) :
    (∑ i ∈ F.support, f i (F.residue i)) =
      ∑ i ∈ t, f i (effectiveResidue F i) := by
  calc
    _ = ∑ i ∈ F.support, f i (effectiveResidue F i) := by
      apply Finset.sum_congr rfl
      intro i hi
      simp [effectiveResidue, hi]
    _ = _ := Finset.sum_subset ht (by
      intro i hi hnot
      simp [effectiveResidue, hnot, hf])

theorem realization_extend (nodes : ι → ℚ) (F : SimplePoleForm ι)
    (t : Finset ι) (ht : F.support ⊆ t) :
    realization nodes F = algebraMap ℚ[X] (RatFunc ℚ) F.polynomial +
      ∑ i ∈ t,
        algebraMap ℚ[X] (RatFunc ℚ) (C (effectiveResidue F i)) /
          algebraMap ℚ[X] (RatFunc ℚ) (X - C (nodes i)) := by
  unfold realization
  congr 1
  exact sum_extend F t ht
    (fun i c => algebraMap ℚ[X] (RatFunc ℚ) (C c) /
      algebraMap ℚ[X] (RatFunc ℚ) (X - C (nodes i)))
    (by intro i; simp only [Polynomial.C_0, map_zero, zero_div])

theorem realization_unique (nodes : ι → ℚ) (hnodes : Function.Injective nodes)
    (F G : SimplePoleForm ι) (h : realization nodes F = realization nodes G) :
    F.polynomial = G.polynomial ∧ effectiveResidue F = effectiveResidue G := by
  let t := F.support ∪ G.support
  rw [realization_extend nodes F t Finset.subset_union_left,
    realization_extend nodes G t Finset.subset_union_right] at h
  have hu := Polynomial.quo_add_sum_rem_div_unique (RatFunc ℚ)
    (g := fun i => X - C (nodes i)) (s := t)
    (fun i _ => Polynomial.monic_X_sub_C (nodes i))
    (fun i hi j hj hij => Polynomial.pairwise_coprime_X_sub_C hnodes hij)
    (r₁ := fun i => C (effectiveResidue F i))
    (r₂ := fun i => C (effectiveResidue G i))
    (fun i _ => by simpa only [Polynomial.degree_X_sub_C] using
      (Polynomial.degree_C_lt (a := effectiveResidue F i)))
    (fun i _ => by simpa only [Polynomial.degree_X_sub_C] using
      (Polynomial.degree_C_lt (a := effectiveResidue G i))) h
  refine ⟨hu.1, funext fun i => ?_⟩
  by_cases hi : i ∈ t
  · exact Polynomial.C_injective (hu.2 i hi)
  · have hF : i ∉ F.support := fun hmem => hi (Finset.mem_union_left _ hmem)
    have hG : i ∉ G.support := fun hmem => hi (Finset.mem_union_right _ hmem)
    simp [effectiveResidue, hF, hG]

theorem realization_eq_of_data (nodes : ι → ℚ) (F G : SimplePoleForm ι)
    (hp : F.polynomial = G.polynomial) (hr : effectiveResidue F = effectiveResidue G) :
    realization nodes F = realization nodes G := by
  rw [realization_extend nodes F (F.support ∪ G.support) Finset.subset_union_left,
    realization_extend nodes G (F.support ∪ G.support) Finset.subset_union_right,
    hp, hr]

theorem realization_eq_iff (nodes : ι → ℚ) (hnodes : Function.Injective nodes)
    (F G : SimplePoleForm ι) :
    realization nodes F = realization nodes G ↔
      F.polynomial = G.polynomial ∧ effectiveResidue F = effectiveResidue G :=
  ⟨realization_unique nodes hnodes F G,
    fun h => realization_eq_of_data nodes F G h.1 h.2⟩

def moment (polyMoment : ℚ[X] → ℚ[X]) (poleMoment : ι → ℚ[X])
    (F : SimplePoleForm ι) : ℚ[X] :=
  polyMoment F.polynomial + ∑ i ∈ F.support, C (F.residue i) * poleMoment i

theorem moment_representation_independent (nodes : ι → ℚ)
    (hnodes : Function.Injective nodes) (polyMoment : ℚ[X] → ℚ[X])
    (poleMoment : ι → ℚ[X]) (F G : SimplePoleForm ι)
    (h : realization nodes F = realization nodes G) :
    moment polyMoment poleMoment F = moment polyMoment poleMoment G := by
  obtain ⟨hp, hr⟩ := realization_unique nodes hnodes F G h
  unfold moment
  rw [sum_extend F (F.support ∪ G.support) Finset.subset_union_left
      (fun i c => C c * poleMoment i) (by intro i; simp),
    sum_extend G (F.support ∪ G.support) Finset.subset_union_right
      (fun i c => C c * poleMoment i) (by intro i; simp), hp, hr]

def muForm (R : Zetahyperbolic.RatMomentElem) : SimplePoleForm ℕ :=
  ⟨R.polyPart, Finset.Icc 1 R.maxPole, R.poleRes⟩

def muRatFunc (R : Zetahyperbolic.RatMomentElem) : RatFunc ℚ :=
  realization (fun j : ℕ => -((j : ℚ) ^ 2)) (muForm R)

theorem mu_representation_unique (R S : Zetahyperbolic.RatMomentElem)
    (h : muRatFunc R = muRatFunc S) :
    R.polyPart = S.polyPart ∧
      (fun j => if j ∈ Finset.Icc 1 R.maxPole then R.poleRes j else 0) =
      (fun j => if j ∈ Finset.Icc 1 S.maxPole then S.poleRes j else 0) := by
  exact realization_unique _ Section2LagrangeIdentification.negative_square_injective
    (muForm R) (muForm S) h

theorem muFunctionalPoly_representation_independent (k : ℕ)
    (R S : Zetahyperbolic.RatMomentElem) (h : muRatFunc R = muRatFunc S) :
    Zetahyperbolic.muFunctionalPoly k R = Zetahyperbolic.muFunctionalPoly k S := by
  exact moment_representation_independent _
    Section2LagrangeIdentification.negative_square_injective
    (fun q => ∑ e ∈ Finset.range (q.natDegree + 1),
      C (q.coeff e * Zetahyperbolic.muMonomial k e))
    (Zetahyperbolic.muPolePoly k) (muForm R) (muForm S) h

/-- The actual rational functions representable by the manuscript's specified
polynomial plus finite simple negative-square poles. -/
def MuDomain := Set.range muRatFunc

def muOnDomain (k : ℕ) (f : MuDomain) : ℚ[X] :=
  Zetahyperbolic.muFunctionalPoly k (Classical.choose f.property)

theorem muOnDomain_eq (k : ℕ) (R : Zetahyperbolic.RatMomentElem) :
    muOnDomain k ⟨muRatFunc R, ⟨R, rfl⟩⟩ = Zetahyperbolic.muFunctionalPoly k R := by
  apply muFunctionalPoly_representation_independent
  exact Classical.choose_spec (show muRatFunc R ∈ MuDomain from ⟨R, rfl⟩)

theorem pulledMoment_representation_independent (k : ℕ) (hk : 1 ≤ k)
    (R S : Zetahyperbolic.RatMomentElem) (h : muRatFunc R = muRatFunc S) :
    PullbackReflection.pulledMoment k R = PullbackReflection.pulledMoment k S := by
  rw [← PullbackReflection.muFunctionalPoly_eq_pulledMoment k hk R,
    ← PullbackReflection.muFunctionalPoly_eq_pulledMoment k hk S]
  exact muFunctionalPoly_representation_independent k R S h

end LeanPaper.Section2RepresentationIndependence
