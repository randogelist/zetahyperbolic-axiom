import LeanPaper.Section4ConjugateBounds

/-!
# Closest-root existence from the actual center value in Theorem 4.7

A small polynomial value and a nonzero integer leading coefficient force an
actual root into the corresponding degree-normalized exponential disk. The
factorization and multiplicities are constructed from the polynomial itself.
The manuscript specialization also proves that the root obtained is real.
Only the quantitative bound on the actual center value remains a premise.
-/

noncomputable section
open Polynomial

namespace LeanPaper.Section4ClosestRoot
open Section4Resultant

private theorem root_product_lower (s : Multiset ℂ) (z : ℂ) (δ : ℝ)
    (hδ : 0 ≤ δ) (hsep : ∀ r ∈ s, δ ≤ ‖z-r‖) :
    δ ^ s.card ≤ ‖(s.map (fun r => z-r)).prod‖ := by
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons r s ih =>
    have hr := hsep r (by simp)
    have hs : ∀ t ∈ s, δ ≤ ‖z-t‖ := fun t ht => hsep t (by simp [ht])
    have hi := ih hs
    simpa only [Multiset.card_cons, pow_succ, Multiset.map_cons,
      Multiset.prod_cons, norm_mul, mul_comm] using
      mul_le_mul hr hi (pow_nonneg hδ _) (norm_nonneg _)

/-- A small value of a nonconstant polynomial with leading coefficient norm
at least one forces a root into the claimed disk. -/
theorem polynomial_close_root (F : ℂ[X]) (z : ℂ) (t : ℝ)
    (hdegree : 0 < F.natDegree) (hlc : 1 ≤ ‖F.leadingCoeff‖)
    (hvalue : ‖F.eval z‖ ≤ Real.exp (-(F.natDegree : ℝ)*t)) :
    ∃ r ∈ F.roots, ‖z-r‖ ≤ Real.exp (-t) := by
  classical
  by_contra hnone
  push_neg at hnone
  have hs := IsAlgClosed.splits F
  have hcard : 0 < F.roots.card := by
    rw [← hs.natDegree_eq_card_roots]
    exact hdegree
  obtain ⟨r, hr⟩ := Multiset.card_pos_iff_exists_mem.mp hcard
  obtain ⟨s, heq⟩ := Multiset.exists_cons_of_mem hr
  have htail : ∀ q ∈ s, Real.exp (-t) ≤ ‖z-q‖ := by
    intro q hq
    exact (hnone q (by rw [heq]; simp [hq])).le
  have hprod := root_product_lower s z (Real.exp (-t)) (Real.exp_pos _).le htail
  have hstrict : Real.exp (-t)^F.roots.card <
      ‖(F.roots.map (fun q => z-q)).prod‖ := by
    rw [heq, Multiset.card_cons, Multiset.map_cons, Multiset.prod_cons, norm_mul,
      pow_succ]
    calc
      _ < Real.exp (-t)^s.card * ‖z-r‖ :=
        mul_lt_mul_of_pos_left (hnone r hr) (pow_pos (Real.exp_pos _) _)
      _ ≤ ‖(s.map (fun q => z-q)).prod‖ * ‖z-r‖ :=
        mul_le_mul_of_nonneg_right hprod (norm_nonneg _)
      _ = _ := mul_comm _ _
  have hbound : Real.exp (-t)^F.roots.card < ‖F.eval z‖ := by
    calc
      _ < ‖(F.roots.map (fun q => z-q)).prod‖ := hstrict
      _ ≤ ‖F.leadingCoeff‖ * ‖(F.roots.map (fun q => z-q)).prod‖ :=
        le_mul_of_one_le_left (norm_nonneg _) hlc
      _ = _ := by rw [hs.eval_eq_prod_roots z, norm_mul]
  rw [← hs.natDegree_eq_card_roots, ← Real.exp_nat_mul] at hbound
  have hexp : (F.natDegree : ℝ)*(-t) = -(F.natDegree : ℝ)*t := by ring
  rw [hexp] at hbound
  exact not_lt_of_ge hvalue hbound

/-- The integer leading-coefficient lower bound is discharged, rather than
passed to the closest-root estimate as an extra assumption. -/
theorem integer_polynomial_close_root (P : ℤ[X]) (z : ℂ) (t : ℝ)
    (hdegree : 0 < P.natDegree)
    (hvalue : ‖(complexPolynomial P).eval z‖ ≤ Real.exp (-(P.natDegree : ℝ)*t)) :
    ∃ r ∈ (complexPolynomial P).roots, ‖z-r‖ ≤ Real.exp (-t) := by
  have hP : P ≠ 0 := by
    intro hz
    simp [hz] at hdegree
  have hinj : Function.Injective (algebraMap ℤ ℂ) := Int.cast_injective
  have hdeg : (complexPolynomial P).natDegree = P.natDegree :=
    Polynomial.natDegree_map_eq_of_injective hinj P
  have hlc : 1 ≤ ‖(complexPolynomial P).leadingCoeff‖ := by
    rw [complexPolynomial, Polynomial.leadingCoeff_map_of_injective hinj]
    simpa only [eq_intCast, Complex.norm_intCast] using
      PaperOrder.Section4.proposition_4_2_nonzero_integer_abs_bound
        P.leadingCoeff (Polynomial.leadingCoeff_ne_zero.mpr hP)
  exact polynomial_close_root (complexPolynomial P) z t (by simpa [hdeg] using hdegree)
    hlc (by simpa [hdeg] using hvalue)

open ManuscriptChain

/-- The actual primitive manuscript polynomial has a real root in the disk
forced by its actual center value. No root or factorization witness is assumed. -/
theorem manuscript_real_close_root (p : Real.Parameters) (hp : Real.Admissible p)
    (t : ℝ)
    (hvalue : ‖(complexPolynomial (GeneralIrrationality.primitivePolynomial p)).eval
      (Real.zeta p.weight : ℂ)‖ ≤ Real.exp (-(p.h : ℝ)*t)) :
    ∃ r : ℝ,
      (GeneralIrrationality.primitivePolynomial p).eval₂ (algebraMap ℤ ℂ) (r : ℂ) = 0 ∧
      |Real.zeta p.weight-r| ≤ Real.exp (-t) := by
  have hdegree : 0 < (GeneralIrrationality.primitivePolynomial p).natDegree := by
    rw [GeneralIrrationality.primitivePolynomial_natDegree]
    exact Nat.sub_pos_of_lt hp.N_lt_K
  obtain ⟨z, hz, hdist⟩ := integer_polynomial_close_root
    (GeneralIrrationality.primitivePolynomial p) (Real.zeta p.weight : ℂ) t hdegree
    (by simpa only [GeneralIrrationality.primitivePolynomial_natDegree] using hvalue)
  have hroot : (complexPolynomial (GeneralIrrationality.primitivePolynomial p)).eval z = 0 :=
    (Polynomial.mem_roots (Polynomial.ne_zero_of_mem_roots hz)).mp hz
  have heval : (GeneralIrrationality.primitivePolynomial p).eval₂
      (algebraMap ℤ ℂ) z = 0 := by
    simpa only [complexPolynomial, Polynomial.eval_map] using hroot
  have him := General.roots_real p (GRAM_POSITIVE p hp) z
    ((PrimitiveNormDisk.primitive_complex_root_iff p z).mp heval)
  have hreal : (z.re : ℂ) = z := by
    apply Complex.ext <;> simp [him]
  refine ⟨z.re, ?_, ?_⟩
  · simpa only [hreal] using heval
  · have hc : ‖(Real.zeta p.weight : ℂ)-(z.re : ℂ)‖ ≤ Real.exp (-t) := by
      simpa only [hreal] using hdist
    simpa only [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] using hc

end LeanPaper.Section4ClosestRoot

#print axioms LeanPaper.Section4ClosestRoot.polynomial_close_root
#print axioms LeanPaper.Section4ClosestRoot.integer_polynomial_close_root
#print axioms LeanPaper.Section4ClosestRoot.manuscript_real_close_root
