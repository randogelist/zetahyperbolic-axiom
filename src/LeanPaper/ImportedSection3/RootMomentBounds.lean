import LeanPaper.ImportedSection3.PowerSumExtrema
import LeanPaper.ReciprocalRootMoments

/-!
The finite extremal bound is now applied to the existing actual determinant
root vector. An extremal inverse-square gap is constructed from the finite
root family; it is not supplied as an additional witness. The bounds hold for
all nonnegative integral moment orders, with multiplicities retained.

No limit in the moment order, logarithmic-derivative identification, or
uniform quantitative root separation is claimed.
-/

noncomputable section
open scoped BigOperators

namespace LeanPaper.Section3RootMomentBounds

open LeanPaper.ReciprocalRootMoments
open PaperAdvances.Corollary3_6_PowerSumExtrema

/-- Every nonempty finite root family has an attained maximal squared
inverse gap. Equal squared gaps and repeated roots are permitted. -/
theorem reciprocal_atom_maximizer {h : ℕ} (hh : 0 < h)
    (r : Fin h → ℝ) (q : ℝ) :
    ∃ j : Fin h, ∀ i : Fin h, reciprocalAtom r q i ≤ reciprocalAtom r q j := by
  classical
  obtain ⟨j, _, hj⟩ := Finset.exists_max_image
    (Finset.univ : Finset (Fin h)) (reciprocalAtom r q)
    ⟨⟨0, hh⟩, Finset.mem_univ _⟩
  exact ⟨j, fun i => hj i (Finset.mem_univ i)⟩

/-- The exact finite even-moment bound at any maximizing inverse-square gap. -/
theorem reciprocal_even_moment_bounds {h : ℕ}
    (r : Fin h → ℝ) (q : ℝ) (j : Fin h)
    (hj : ∀ i, reciprocalAtom r q i ≤ reciprocalAtom r q j) (m : ℕ) :
    reciprocalAtom r q j ^ m ≤ reciprocalEvenMoment r q m ∧
      reciprocalEvenMoment r q m ≤ (h : ℝ) * reciprocalAtom r q j ^ m := by
  exact positive_atomic_moment_bounds (reciprocalAtom r q)
    (fun i => sq_nonneg ((r i - q)⁻¹)) j hj m

/-- The actual manuscript determinant supplies its root family and an attained
positive extremal atom. Its even power sums obey both sharp finite bounds at
every moment order; only structural admissibility and a rational non-root
shift are required. -/
theorem actual_reciprocal_moment_bounds
    (p : ManuscriptChain.Real.Parameters)
    (hp : ManuscriptChain.Real.Admissible p) (q : ℚ)
    (hq : ManuscriptChain.Real.evalQ (ManuscriptChain.Real.delta p) (q : ℝ) ≠ 0) :
    ∃ j : Fin p.h,
      0 < reciprocalAtom (manuscriptRoots p hp) (q : ℝ) j ∧
      (∀ i, reciprocalAtom (manuscriptRoots p hp) (q : ℝ) i ≤
        reciprocalAtom (manuscriptRoots p hp) (q : ℝ) j) ∧
      ∀ m : ℕ,
        reciprocalAtom (manuscriptRoots p hp) (q : ℝ) j ^ m ≤
          reciprocalEvenMoment (manuscriptRoots p hp) (q : ℝ) m ∧
        reciprocalEvenMoment (manuscriptRoots p hp) (q : ℝ) m ≤
          (p.h : ℝ) * reciprocalAtom (manuscriptRoots p hp) (q : ℝ) j ^ m := by
  have hgap : ∀ i, manuscriptRoots p hp i ≠ (q : ℝ) := by
    intro i heq
    apply hq
    simpa only [heq] using manuscriptRoots_eval p hp i
  obtain ⟨j, hj⟩ := reciprocal_atom_maximizer
    (Nat.sub_pos_of_lt hp.N_lt_K) (manuscriptRoots p hp) (q : ℝ)
  exact ⟨j, reciprocalAtom_pos _ _ hgap j, hj,
    fun m => reciprocal_even_moment_bounds _ _ j hj m⟩

end LeanPaper.Section3RootMomentBounds

#print axioms LeanPaper.Section3RootMomentBounds.actual_reciprocal_moment_bounds
