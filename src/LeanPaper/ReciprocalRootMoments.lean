import ProofAdvances.Corollary_3_6_ExactFiniteRank
import MAIN_CHAIN_ASSEMBLED
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic

/-!
# Corrected Corollary 3.6: coalesced reciprocal-root moments

Repeated inverse-square gaps must be merged, even when the roots themselves
are distinct. We construct the distinct atoms and their positive multiplicity
weights from the finite root vector. The exact determinant threshold is the
number of distinct atoms, without an injectivity hypothesis on the root gaps.

The final results concern the explicit power sums in Corollary 3.6. They do
not identify these sums with logarithmic derivatives, prove their rationality,
or establish the limiting nearest-root estimate. The printed all-orders strict
positivity assertion remains false. Native compilation and audit are pending.
-/

noncomputable section
open scoped BigOperators
open Matrix

namespace LeanPaper.ReciprocalRootMoments

open PaperAdvances.Corollary3_6
open PaperAdvances.Corollary3_6_FullGram
open PaperAdvances.Corollary3_6_WeightedCorrected
open PaperAdvances.Corollary3_6_ExactFiniteRank

/-- The actual distinct values of a finite atomic vector. -/
def atomSupport {h : ℕ} (u : Fin h → ℝ) : Finset ℝ := by
  classical
  exact Finset.univ.image u

/-- A finite enumeration of the distinct values; no distinctness premise. -/
def distinctAtom {h : ℕ} (u : Fin h → ℝ)
    (j : Fin (atomSupport u).card) : ℝ :=
  ((atomSupport u).equivFin.symm j).val

/-- Each original atom is assigned to its canonical support index. -/
def atomIndex {h : ℕ} (u : Fin h → ℝ) (k : Fin h) :
    Fin (atomSupport u).card := by
  classical
  exact (atomSupport u).equivFin ⟨u k, by
    change u k ∈ Finset.univ.image u
    exact Finset.mem_image.mpr ⟨k, Finset.mem_univ k, rfl⟩⟩

theorem distinctAtom_injective {h : ℕ} (u : Fin h → ℝ) :
    Function.Injective (distinctAtom u) := by
  intro i j hij
  apply (atomSupport u).equivFin.symm.injective
  exact Subtype.ext hij

@[simp] theorem distinctAtom_atomIndex {h : ℕ} (u : Fin h → ℝ)
    (k : Fin h) : distinctAtom u (atomIndex u k) = u k := by
  classical
  simp [distinctAtom, atomIndex]

theorem atomIndex_surjective {h : ℕ} (u : Fin h → ℝ) :
    Function.Surjective (atomIndex u) := by
  classical
  intro j
  have hj : distinctAtom u j ∈ atomSupport u :=
    ((atomSupport u).equivFin.symm j).property
  change distinctAtom u j ∈ Finset.univ.image u at hj
  obtain ⟨k, _, hk⟩ := Finset.mem_image.mp hj
  refine ⟨k, distinctAtom_injective u ?_⟩
  simpa only [distinctAtom_atomIndex] using hk

/-- The positive multiplicity of each distinct atom, written as a real sum
of indicators. It is constructed from the data, not supplied as a premise. -/
def coalescedWeight {h : ℕ} (u : Fin h → ℝ)
    (j : Fin (atomSupport u).card) : ℝ :=
  ∑ k : Fin h, if atomIndex u k = j then 1 else 0

theorem coalescedWeight_pos {h : ℕ} (u : Fin h → ℝ)
    (j : Fin (atomSupport u).card) : 0 < coalescedWeight u j := by
  classical
  obtain ⟨k, hk⟩ := atomIndex_surjective u j
  unfold coalescedWeight
  apply Finset.sum_pos'
  · intro i hi
    split_ifs <;> norm_num
  · exact ⟨k, Finset.mem_univ k, by simp [hk]⟩

/-- Finite coalescing preserves every test-function sum, not just moments. -/
theorem sum_coalesced {h : ℕ} (u : Fin h → ℝ) (f : ℝ → ℝ) :
    (∑ j : Fin (atomSupport u).card,
      coalescedWeight u j * f (distinctAtom u j)) =
      ∑ k : Fin h, f (u k) := by
  classical
  unfold coalescedWeight
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  simp [ite_mul]

theorem finiteHankel_eq_coalesced {h : ℕ} (u : Fin h → ℝ) (n : ℕ) :
    finiteHankel u n =
      weightedHankel (distinctAtom u) (coalescedWeight u) n := by
  ext i j
  exact (sum_coalesced u (fun x => x ^ (i.val + j.val))).symm

/-- The sharp determinant threshold for an arbitrary finite atomic vector,
with repeated atoms automatically merged. -/
theorem finiteHankel_det_pos_iff {h : ℕ} (u : Fin h → ℝ) (n : ℕ) :
    0 < (finiteHankel u n).det ↔ n ≤ (atomSupport u).card := by
  rw [finiteHankel_eq_coalesced]
  exact weighted_det_pos_iff_order_le_support
    (distinctAtom u) (coalescedWeight u)
    (distinctAtom_injective u) (coalescedWeight_pos u) n

theorem finiteHankel_posDef_of_le {h : ℕ} (u : Fin h → ℝ) (n : ℕ)
    (hn : n ≤ (atomSupport u).card) : (finiteHankel u n).PosDef := by
  rw [finiteHankel_eq_coalesced]
  exact weighted_posDef_up_to_support
    (distinctAtom u) (coalescedWeight u)
    (distinctAtom_injective u) (coalescedWeight_pos u) n hn

theorem finiteHankel_det_zero_of_support_lt {h : ℕ} (u : Fin h → ℝ)
    (n : ℕ) (hn : (atomSupport u).card < n) :
    (finiteHankel u n).det = 0 := by
  rw [finiteHankel_eq_coalesced]
  exact weighted_hankel_det_zero_above_support
    (distinctAtom u) (coalescedWeight u) n hn

/-- The positive atom attached to the root gap in the manuscript. -/
def reciprocalAtom {h : ℕ} (r : Fin h → ℝ) (q : ℝ) (k : Fin h) : ℝ :=
  ((r k - q)⁻¹) ^ 2

theorem reciprocalAtom_pos {h : ℕ} (r : Fin h → ℝ) (q : ℝ)
    (hr : ∀ k, r k ≠ q) (k : Fin h) : 0 < reciprocalAtom r q k := by
  exact sq_pos_of_ne_zero (inv_ne_zero (sub_ne_zero.mpr (hr k)))

/-- The moment with index m is the reciprocal-root power sum S_(2m).
At m=0 the definition gives the number h of listed roots, with multiplicity. -/
def reciprocalEvenMoment {h : ℕ} (r : Fin h → ℝ) (q : ℝ) (m : ℕ) : ℝ :=
  ∑ k : Fin h, reciprocalAtom r q k ^ m

theorem reciprocalEvenMoment_eq_powerSum {h : ℕ} (r : Fin h → ℝ)
    (q : ℝ) (m : ℕ) :
    reciprocalEvenMoment r q m = ∑ k : Fin h, ((r k - q)⁻¹) ^ (2 * m) := by
  simp only [reciprocalEvenMoment, reciprocalAtom, ← pow_mul]

@[simp] theorem reciprocalEvenMoment_zero {h : ℕ} (r : Fin h → ℝ)
    (q : ℝ) : reciprocalEvenMoment r q 0 = (h : ℝ) := by
  simp [reciprocalEvenMoment]

/-- The Hankel matrix of the actual even reciprocal-root power sums. -/
def reciprocalHankel {h : ℕ} (r : Fin h → ℝ) (q : ℝ) (n : ℕ) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun i j => reciprocalEvenMoment r q (i.val + j.val)

theorem reciprocalHankel_eq {h : ℕ} (r : Fin h → ℝ) (q : ℝ) (n : ℕ) :
    reciprocalHankel r q n = finiteHankel (reciprocalAtom r q) n := rfl

/-- All-order semidefiniteness requires no gap-distinctness assumption. -/
theorem reciprocalHankel_posSemidef {h : ℕ} (r : Fin h → ℝ)
    (q : ℝ) (n : ℕ) : (reciprocalHankel r q n).PosSemidef := by
  exact finite_hankel_posSemidef (reciprocalAtom r q) n

/-- The shifted Hankel condition, alongside ordinary Hankel positivity,
is the finite Stieltjes positivity assertion for the manuscript sequence. -/
theorem reciprocalShiftedHankel_posSemidef {h : ℕ} (r : Fin h → ℝ)
    (q : ℝ) (n : ℕ) :
    Matrix.PosSemidef (fun i j : Fin n =>
      reciprocalEvenMoment r q (i.val + j.val + 1)) := by
  have heq : (fun i j : Fin n =>
      reciprocalEvenMoment r q (i.val + j.val + 1)) =
      weightedHankel (reciprocalAtom r q) (reciprocalAtom r q) n := by
    ext i j
    unfold reciprocalEvenMoment weightedHankel
    apply Finset.sum_congr rfl
    intro k hk
    rw [pow_succ]
    ring
  rw [heq]
  exact weighted_hankel_posSemidef (reciprocalAtom r q)
    (reciprocalAtom r q) n (fun k => sq_nonneg ((r k - q)⁻¹))

/-- Exact corrected replacement for the printed strict-Hankel claim.
The threshold counts distinct squared inverse gaps, not distinct roots. -/
theorem reciprocalHankel_det_pos_iff {h : ℕ} (r : Fin h → ℝ)
    (q : ℝ) (n : ℕ) :
    0 < (reciprocalHankel r q n).det ↔
      n ≤ (atomSupport (reciprocalAtom r q)).card := by
  exact finiteHankel_det_pos_iff (reciprocalAtom r q) n

theorem reciprocalHankel_det_zero_above_distinct_support {h : ℕ}
    (r : Fin h → ℝ) (q : ℝ) (n : ℕ)
    (hn : (atomSupport (reciprocalAtom r q)).card < n) :
    (reciprocalHankel r q n).det = 0 := by
  exact finiteHankel_det_zero_of_support_lt (reciprocalAtom r q) n hn

/-- Opposite gaps yield the same inverse-square atom. Thus distinct real
roots alone cannot justify injectivity of the manuscript's moment atoms. -/
theorem opposite_gaps_same_atom (a : ℝ) : ((-a)⁻¹) ^ 2 = (a⁻¹) ^ 2 := by
  rw [inv_neg]
  ring

/-- The complete real root vector of the actual manuscript determinant,
constructed using the already assembled positive moment realization. -/
def manuscriptRoots (p : ManuscriptChain.Real.Parameters)
    (hp : ManuscriptChain.Real.Admissible p) : Fin p.h → ℝ :=
  (ManuscriptChain.General.factorization p (ManuscriptChain.GRAM_POSITIVE p hp)).root

theorem manuscriptRoots_eval (p : ManuscriptChain.Real.Parameters)
    (hp : ManuscriptChain.Real.Admissible p) (i : Fin p.h) :
    ManuscriptChain.Real.evalQ (ManuscriptChain.Real.delta p)
      (manuscriptRoots p hp i) = 0 := by
  simpa only [ManuscriptChain.Real.manuscriptPencil_detPolynomial,
    ManuscriptChain.Real.evalQ, manuscriptRoots] using
    (ManuscriptChain.General.factorization p
      (ManuscriptChain.GRAM_POSITIVE p hp)).eval_root i

/-- The coalesced Stieltjes matrix conclusions now concern the actual
manuscript roots and its rational shift. Nonvanishing of the determinant at
the shift is the ordinary hypothesis of Corollary 3.6; root-gap positivity is
derived from it. No Gram or root-factorization premise is passed by the caller. -/
theorem manuscript_reciprocal_moments
    (p : ManuscriptChain.Real.Parameters)
    (hp : ManuscriptChain.Real.Admissible p) (q : ℚ)
    (hq : ManuscriptChain.Real.evalQ (ManuscriptChain.Real.delta p) (q : ℝ) ≠ 0)
    (n : ℕ) :
    (∀ i, 0 < reciprocalAtom (manuscriptRoots p hp) (q : ℝ) i) ∧
    (reciprocalHankel (manuscriptRoots p hp) (q : ℝ) n).PosSemidef ∧
    Matrix.PosSemidef (fun i j : Fin n => reciprocalEvenMoment (manuscriptRoots p hp)
      (q : ℝ) (i.val + j.val + 1)) ∧
    (0 < (reciprocalHankel (manuscriptRoots p hp) (q : ℝ) n).det ↔
      n ≤ (atomSupport (reciprocalAtom (manuscriptRoots p hp) (q : ℝ))).card) ∧
    ((atomSupport (reciprocalAtom (manuscriptRoots p hp) (q : ℝ))).card < n →
      (reciprocalHankel (manuscriptRoots p hp) (q : ℝ) n).det = 0) := by
  have hgap : ∀ i, manuscriptRoots p hp i ≠ (q : ℝ) := by
    intro i heq
    apply hq
    simpa only [heq] using manuscriptRoots_eval p hp i
  exact ⟨reciprocalAtom_pos _ _ hgap,
    reciprocalHankel_posSemidef _ _ n,
    reciprocalShiftedHankel_posSemidef _ _ n,
    reciprocalHankel_det_pos_iff _ _ n,
    reciprocalHankel_det_zero_above_distinct_support _ _ n⟩

end LeanPaper.ReciprocalRootMoments

#print axioms LeanPaper.ReciprocalRootMoments.sum_coalesced
#print axioms LeanPaper.ReciprocalRootMoments.finiteHankel_det_pos_iff
#print axioms LeanPaper.ReciprocalRootMoments.reciprocalShiftedHankel_posSemidef
#print axioms LeanPaper.ReciprocalRootMoments.reciprocalHankel_det_pos_iff
#print axioms LeanPaper.ReciprocalRootMoments.reciprocalHankel_det_zero_above_distinct_support
#print axioms LeanPaper.ReciprocalRootMoments.manuscript_reciprocal_moments
