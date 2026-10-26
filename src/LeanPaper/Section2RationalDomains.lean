import LeanPaper.Section2TauRepresentation
import LeanPaper.Rebuild.PartialFractionsQuotient

/-!
Exact algebraic characterization of the manuscript's simple-pole domains.
Membership is equivalent to the reduced RatFunc denominator dividing a finite
product of the prescribed distinct linear pole factors. Partial fractions
construct the representation; no existence of a functional value is assumed.
-/

noncomputable section
open scoped BigOperators
open Polynomial

namespace LeanPaper.Section2RationalDomains
open Section2RepresentationIndependence Section2TauRepresentation

variable {ι : Type*} [DecidableEq ι]

def poleProduct (nodes : ι → ℚ) (s : Finset ι) : ℚ[X] :=
  ∏ i ∈ s, (X - C (nodes i))

theorem poleProduct_ne_zero (nodes : ι → ℚ) (s : Finset ι) :
    poleProduct nodes s ≠ 0 := by
  exact (Polynomial.monic_prod_of_monic s _
    (fun i _ => Polynomial.monic_X_sub_C (nodes i))).ne_zero

def commonNumerator (nodes : ι → ℚ) (F : SimplePoleForm ι) : ℚ[X] :=
  F.polynomial * poleProduct nodes F.support +
    ∑ i ∈ F.support, C (F.residue i) * poleProduct nodes (F.support.erase i)

theorem realization_eq_fraction (nodes : ι → ℚ) (F : SimplePoleForm ι) :
    realization nodes F =
      algebraMap ℚ[X] (RatFunc ℚ) (commonNumerator nodes F) /
        algebraMap ℚ[X] (RatFunc ℚ) (poleProduct nodes F.support) := by
  apply (eq_div_iff (RatFunc.algebraMap_ne_zero (poleProduct_ne_zero nodes F.support))).2
  unfold realization commonNumerator
  rw [add_mul, Finset.sum_mul, map_add, map_mul, map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  have hprod : poleProduct nodes F.support =
      (X - C (nodes i)) * poleProduct nodes (F.support.erase i) :=
    (Finset.mul_prod_erase F.support (fun j => X - C (nodes j)) hi).symm
  rw [hprod, map_mul, map_mul]
  have hd : algebraMap ℚ[X] (RatFunc ℚ) (X - C (nodes i)) ≠ 0 :=
    RatFunc.algebraMap_ne_zero (Polynomial.monic_X_sub_C (nodes i)).ne_zero
  field_simp [hd]

theorem realization_denom_dvd (nodes : ι → ℚ) (F : SimplePoleForm ι) :
    (realization nodes F).denom ∣ poleProduct nodes F.support := by
  rw [realization_eq_fraction]
  exact RatFunc.denom_div_dvd _ _

theorem fraction_representation_exists (nodes : ι → ℚ)
    (hnodes : Function.Injective nodes) (s : Finset ι) (num : ℚ[X]) :
    ∃ (q : ℚ[X]) (c : ι → ℚ),
      realization nodes ⟨q, s, c⟩ =
        algebraMap ℚ[X] (RatFunc ℚ) num /
          algebraMap ℚ[X] (RatFunc ℚ) (poleProduct nodes s) := by
  obtain ⟨q, r, hr, hf⟩ := Polynomial.div_prod_eq_quo_add_sum_rem_div
    (RatFunc ℚ) num (g := fun i => X - C (nodes i)) (s := s)
    (fun i _ => Polynomial.monic_X_sub_C (nodes i))
    (fun i hi j hj hij => Polynomial.pairwise_coprime_X_sub_C hnodes hij)
  have hc (i : ι) (hi : i ∈ s) : r i = C ((r i).coeff 0) :=
    ManuscriptChain.PartialFractions.polynomial_eq_C_of_degree_lt_one
      (by simpa only [Polynomial.degree_X_sub_C] using hr i hi)
  refine ⟨q, fun i => (r i).coeff 0, ?_⟩
  calc
    _ = algebraMap ℚ[X] (RatFunc ℚ) q + ∑ i ∈ s,
        algebraMap ℚ[X] (RatFunc ℚ) (r i) /
          algebraMap ℚ[X] (RatFunc ℚ) (X - C (nodes i)) := by
      unfold realization
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      rw [hc i hi]
    _ = _ := by simpa only [poleProduct, map_prod] using hf.symm

theorem range_realization_iff_denom_dvd (nodes : ι → ℚ)
    (hnodes : Function.Injective nodes) (f : RatFunc ℚ) :
    f ∈ Set.range (realization nodes) ↔
      ∃ s : Finset ι, f.denom ∣ poleProduct nodes s := by
  constructor
  · rintro ⟨F, rfl⟩
    exact ⟨F.support, realization_denom_dvd nodes F⟩
  · rintro ⟨s, hs⟩
    obtain ⟨num, hf⟩ := (RatFunc.denom_dvd (poleProduct_ne_zero nodes s)).mp hs
    obtain ⟨q, c, hc⟩ := fraction_representation_exists nodes hnodes s num
    exact ⟨⟨q, s, c⟩, hc.trans hf.symm⟩

def muPoleProduct (M : ℕ) : ℚ[X] :=
  poleProduct (fun j : ℕ => -((j : ℚ) ^ 2)) (Finset.Icc 1 M)

theorem muPoleProduct_eq (M : ℕ) :
    muPoleProduct M = Zetahyperbolic.denominatorPolynomial M := by
  simp [muPoleProduct, poleProduct, Zetahyperbolic.denominatorPolynomial]

theorem muDomain_iff_denom_dvd (f : RatFunc ℚ) :
    f ∈ MuDomain ↔ ∃ M : ℕ, f.denom ∣ muPoleProduct M := by
  constructor
  · rintro ⟨R, rfl⟩
    exact ⟨R.maxPole, realization_denom_dvd _ (muForm R)⟩
  · rintro ⟨M, hM⟩
    have hprod : muPoleProduct M ≠ 0 := poleProduct_ne_zero _ _
    obtain ⟨num, hf⟩ := (RatFunc.denom_dvd hprod).mp hM
    obtain ⟨q, c, hc⟩ := fraction_representation_exists _
      Section2LagrangeIdentification.negative_square_injective (Finset.Icc 1 M) num
    refine ⟨⟨q, M, c⟩, ?_⟩
    exact hc.trans hf.symm

theorem tauDomain_iff_denom_dvd (f : RatFunc ℚ) :
    f ∈ TauDomain ↔ ∃ s : Finset ℤ,
      f.denom ∣ poleProduct (fun r : ℤ => (r : ℚ)) s :=
  range_realization_iff_denom_dvd _ Int.cast_injective f

/-- Every numerator over the actual manuscript pole product has a μ value,
including numerators whose common factors cancel. -/
theorem fraction_mem_muDomain (M : ℕ) (num : ℚ[X]) :
    algebraMap ℚ[X] (RatFunc ℚ) num /
      algebraMap ℚ[X] (RatFunc ℚ) (muPoleProduct M) ∈ MuDomain := by
  apply (muDomain_iff_denom_dvd _).mpr
  exact ⟨M, RatFunc.denom_div_dvd _ _⟩

end LeanPaper.Section2RationalDomains
