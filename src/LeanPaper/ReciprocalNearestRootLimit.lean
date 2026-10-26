import LeanPaper.ImportedSection3.RootMomentBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Corrected reciprocal-root bounds and nearest-root convergence

For the actual manuscript determinant at a rational non-root shift, the
negative even-moment root converges to the nearest root distance. Multiplicity
and coincident squared gaps are permitted. The finite bounds have the corrected
orientation h^(-1/(2r)) d <= S_(2r)^(-1/(2r)) <= d.

The moment index is r=m+1, so every term has positive order. This result does
not establish the separate logarithmic-derivative or rationality assertions.
-/

noncomputable section
open scoped BigOperators Topology
open Filter

namespace LeanPaper.ReciprocalNearestRootLimit

open LeanPaper.ReciprocalRootMoments
open LeanPaper.Section3RootMomentBounds
open PaperAdvances.Corollary3_6_PowerSumExtrema

theorem finite_power_root_bounds {h : ℕ} (u : Fin h → ℝ)
    (hu : ∀ i, 0 ≤ u i) (j : Fin h) (hj : ∀ i, u i ≤ u j)
    (n : ℕ) (hn : 0 < n) :
    u j ≤ (∑ i, u i ^ n) ^ (1 / (n : ℝ)) ∧
      (∑ i, u i ^ n) ^ (1 / (n : ℝ)) ≤
        (h : ℝ) ^ (1 / (n : ℝ)) * u j := by
  have hbounds := positive_atomic_moment_bounds u hu j hj n
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hsum : 0 ≤ ∑ i, u i ^ n :=
    Finset.sum_nonneg (fun i _ => pow_nonneg (hu i) n)
  have hroot : (u j ^ n) ^ (1 / (n : ℝ)) = u j := by
    simpa only [one_div] using Real.pow_rpow_inv_natCast (hu j) (Nat.ne_of_gt hn)
  constructor
  · rw [← hroot]
    exact Real.rpow_le_rpow (pow_nonneg (hu j) n) hbounds.1 (by positivity)
  · calc
      (∑ i, u i ^ n) ^ (1 / (n : ℝ)) ≤
          ((h : ℝ) * u j ^ n) ^ (1 / (n : ℝ)) :=
        Real.rpow_le_rpow hsum hbounds.2 (by positivity)
      _ = (h : ℝ) ^ (1 / (n : ℝ)) * u j := by
        rw [Real.mul_rpow (Nat.cast_nonneg h) (pow_nonneg (hu j) n), hroot]

theorem finite_power_root_tendsto {h : ℕ} (u : Fin h → ℝ)
    (hu : ∀ i, 0 ≤ u i) (j : Fin h) (hj : ∀ i, u i ≤ u j) :
    Tendsto (fun m : ℕ => (∑ i, u i ^ (m + 1)) ^ (1 / ((m + 1 : ℕ) : ℝ)))
      atTop (𝓝 (u j)) := by
  have hh : 0 < h := Nat.zero_lt_of_lt j.isLt
  have hhR : (h : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hh
  have hexp : Tendsto (fun m : ℕ => 1 / ((m + 1 : ℕ) : ℝ)) atTop (𝓝 0) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hfac : Tendsto (fun m : ℕ =>
      (h : ℝ) ^ (1 / ((m + 1 : ℕ) : ℝ))) atTop (𝓝 1) := by
    simpa only [Real.rpow_zero] using
      (tendsto_const_nhds.rpow hexp (Or.inl hhR))
  have hupper : Tendsto (fun m : ℕ =>
      (h : ℝ) ^ (1 / ((m + 1 : ℕ) : ℝ)) * u j - u j) atTop (𝓝 0) := by
    simpa only [one_mul, sub_self] using (hfac.mul_const (u j)).sub_const (u j)
  have hzero : Tendsto (fun m : ℕ =>
      (∑ i, u i ^ (m + 1)) ^ (1 / ((m + 1 : ℕ) : ℝ)) - u j)
      atTop (𝓝 0) := by
    apply squeeze_zero
    · intro m
      exact sub_nonneg.mpr (finite_power_root_bounds u hu j hj (m + 1) (by omega)).1
    · intro m
      exact sub_le_sub_right
        (finite_power_root_bounds u hu j hj (m + 1) (by omega)).2 (u j)
    · exact hupper
  simpa only [sub_add_cancel, zero_add] using hzero.add_const (u j)

theorem reciprocal_atom_negative_half {h : ℕ} (r : Fin h → ℝ)
    (q : ℝ) (i : Fin h) :
    reciprocalAtom r q i ^ (-1 / 2 : ℝ) = |r i - q| := by
  have heq : reciprocalAtom r q i = (|r i - q|⁻¹) ^ 2 := by
    simp only [reciprocalAtom, ← abs_inv]
    exact (sq_abs _).symm
  rw [heq, ← Real.rpow_natCast_mul (inv_nonneg.mpr (abs_nonneg (r i - q))) 2]
  norm_num [Real.rpow_neg_one]

theorem pow_negative_root (u : ℝ) (hu : 0 ≤ u) (n : ℕ) (hn : 0 < n) :
    (u ^ n) ^ (-1 / (2 * (n : ℝ))) = u ^ (-1 / 2 : ℝ) := by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  rw [← Real.rpow_natCast_mul hu n]
  congr 1
  field_simp

theorem reciprocal_negative_root_bounds {h : ℕ} (r : Fin h → ℝ)
    (q : ℝ) (hr : ∀ i, r i ≠ q) (j : Fin h)
    (hj : ∀ i, reciprocalAtom r q i ≤ reciprocalAtom r q j)
    (n : ℕ) (hn : 0 < n) :
    (h : ℝ) ^ (-1 / (2 * (n : ℝ))) * |r j - q| ≤
        reciprocalEvenMoment r q n ^ (-1 / (2 * (n : ℝ))) ∧
      reciprocalEvenMoment r q n ^ (-1 / (2 * (n : ℝ))) ≤ |r j - q| := by
  have hbounds := reciprocal_even_moment_bounds r q j hj n
  have hu : 0 < reciprocalAtom r q j := reciprocalAtom_pos r q hr j
  have hsum : 0 < reciprocalEvenMoment r q n :=
    lt_of_lt_of_le (pow_pos hu n) hbounds.1
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hpow : (reciprocalAtom r q j ^ n) ^ (-1 / (2 * (n : ℝ))) = |r j - q| := by
    rw [pow_negative_root _ hu.le n hn, reciprocal_atom_negative_half]
  constructor
  · have hb := Real.rpow_le_rpow_of_nonpos hsum hbounds.2
      (show -1 / (2 * (n : ℝ)) ≤ 0 from
        div_nonpos_of_nonpos_of_nonneg (by norm_num) (by positivity))
    rw [Real.mul_rpow (Nat.cast_nonneg h) (pow_nonneg hu.le n), hpow] at hb
    exact hb
  · have hb := Real.rpow_le_rpow_of_nonpos (pow_pos hu n) hbounds.1
      (show -1 / (2 * (n : ℝ)) ≤ 0 from
        div_nonpos_of_nonpos_of_nonneg (by norm_num) (by positivity))
    rwa [hpow] at hb

theorem reciprocal_negative_root_tendsto {h : ℕ} (r : Fin h → ℝ)
    (q : ℝ) (hr : ∀ i, r i ≠ q) (j : Fin h)
    (hj : ∀ i, reciprocalAtom r q i ≤ reciprocalAtom r q j) :
    Tendsto (fun m : ℕ =>
      reciprocalEvenMoment r q (m + 1) ^ (-1 / (2 * ((m + 1 : ℕ) : ℝ))))
      atTop (𝓝 |r j - q|) := by
  have hu : 0 < reciprocalAtom r q j := reciprocalAtom_pos r q hr j
  have ht := (finite_power_root_tendsto (reciprocalAtom r q)
    (fun i => sq_nonneg ((r i - q)⁻¹)) j hj).rpow_const
    (p := (-1 / 2 : ℝ)) (Or.inl (ne_of_gt hu))
  rw [reciprocal_atom_negative_half] at ht
  convert ht using 1
  funext m
  have hnonneg : 0 ≤ reciprocalEvenMoment r q (m + 1) :=
    Finset.sum_nonneg (fun i _ => pow_nonneg (sq_nonneg ((r i - q)⁻¹)) _)
  change reciprocalEvenMoment r q (m + 1) ^ (-1 / (2 * ((m + 1 : ℕ) : ℝ))) =
    (reciprocalEvenMoment r q (m + 1) ^ (1 / ((m + 1 : ℕ) : ℝ))) ^ (-1 / 2 : ℝ)
  rw [← Real.rpow_mul hnonneg]
  congr 1
  ring

/-- The actual determinant yields an attained nearest-root distance, the
correct finite bounds, and convergence, without distinct-root assumptions. -/
theorem actual_nearest_root_limit
    (p : ManuscriptChain.Real.Parameters)
    (hp : ManuscriptChain.Real.Admissible p) (q : ℚ)
    (hq : ManuscriptChain.Real.evalQ (ManuscriptChain.Real.delta p) (q : ℝ) ≠ 0) :
    ∃ j : Fin p.h,
      0 < |manuscriptRoots p hp j - (q : ℝ)| ∧
      (∀ i, |manuscriptRoots p hp j - (q : ℝ)| ≤
        |manuscriptRoots p hp i - (q : ℝ)|) ∧
      (∀ n : ℕ, 0 < n →
        (p.h : ℝ) ^ (-1 / (2 * (n : ℝ))) * |manuscriptRoots p hp j - (q : ℝ)| ≤
          reciprocalEvenMoment (manuscriptRoots p hp) (q : ℝ) n ^ (-1 / (2 * (n : ℝ))) ∧
        reciprocalEvenMoment (manuscriptRoots p hp) (q : ℝ) n ^ (-1 / (2 * (n : ℝ))) ≤
          |manuscriptRoots p hp j - (q : ℝ)|) ∧
      Tendsto (fun m : ℕ =>
        reciprocalEvenMoment (manuscriptRoots p hp) (q : ℝ) (m + 1) ^
          (-1 / (2 * ((m + 1 : ℕ) : ℝ)))) atTop
        (𝓝 |manuscriptRoots p hp j - (q : ℝ)|) := by
  have hgap : ∀ i, manuscriptRoots p hp i ≠ (q : ℝ) := by
    intro i heq
    apply hq
    simpa only [heq] using manuscriptRoots_eval p hp i
  have hh : 0 < p.h := Nat.sub_pos_of_lt hp.N_lt_K
  obtain ⟨j, hj⟩ := reciprocal_atom_maximizer (h := p.h)
    hh (manuscriptRoots p hp) (q : ℝ)
  refine ⟨j, abs_pos.mpr (sub_ne_zero.mpr (hgap j)), ?_, ?_, ?_⟩
  · intro i
    have hb := Real.rpow_le_rpow_of_nonpos
      (reciprocalAtom_pos _ _ hgap i) (hj i) (show (-1 / 2 : ℝ) ≤ 0 by norm_num)
    rw [reciprocal_atom_negative_half, reciprocal_atom_negative_half] at hb
    exact hb
  · exact fun n hn => reciprocal_negative_root_bounds _ _ hgap j hj n hn
  · exact reciprocal_negative_root_tendsto _ _ hgap j hj

end LeanPaper.ReciprocalNearestRootLimit

#print axioms LeanPaper.ReciprocalNearestRootLimit.actual_nearest_root_limit
