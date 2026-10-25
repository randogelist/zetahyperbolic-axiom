import LeanPaper.ImportedSection3.AllDegreeTuran
import Mathlib.Analysis.Calculus.LocalExtr.Polynomial
import Mathlib.Tactic

/-!
# Direct Theorem 3.7 advancement: strict Turan and Rolle separation

This proves a genuine equality classification for the actual odd-zeta
Hankel determinant in any finite dimension
n > 0 has strictly positive first Laguerre--Turan expression at every
nonzero value of its determinant. Consequently, equality T(P,x)=0 occurs
if and only if x is a MULTIPLE real zero: P(x)=P'(x)=0.

An independent Rolle theorem gives a critical point strictly between every
two real zeros. This is polynomial derivative-root separation, NOT yet the
manuscript Theorem 3.4 interlacing of successive principal minors.

No quantitative arithmetic Witness or extra analytical hypotheses are used.
-/

noncomputable section
open scoped BigOperators
open Polynomial

namespace PaperAdvances.Theorem3_7_StrictRolle

open PaperAdvances.Theorem3_7_AllDegrees

/-- A real affine product has strictly positive Laguerre--Turan expression
at any point where it is nonzero, provided one of its factors has a
nonzero linear coefficient. This is the all-degree strict/equality engine. -/
theorem finite_affine_turan_strict_offroots {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (a b : ι → ℝ) (x : ℝ)
    (i : ι) (hi : i ∈ s) (hai : a i ≠ 0)
    (hx : (s.prod (fun j =>
      Polynomial.C (a j) * (Polynomial.X : ℝ[X]) + Polynomial.C (b j))).eval x ≠ 0) :
    0 < turan (s.prod (fun j =>
      Polynomial.C (a j) * (Polynomial.X : ℝ[X]) + Polynomial.C (b j))) x := by
  classical
  let L : ι → ℝ[X] := fun j =>
    Polynomial.C (a j) * (Polynomial.X : ℝ[X]) + Polynomial.C (b j)
  let Q : ℝ[X] := (s.erase i).prod L
  have hfactor : s.prod L = L i * Q := by
    calc
      s.prod L = (insert i (s.erase i)).prod L := by
        rw [Finset.insert_erase hi]
      _ = L i * Q := by
        rw [Finset.prod_insert (Finset.notMem_erase i s)]
  have hxprod : (s.prod L).eval x ≠ 0 := hx
  rw [hfactor, Polynomial.eval_mul] at hxprod
  have hQ : Q.eval x ≠ 0 := (mul_ne_zero_iff.mp hxprod).2
  have hQnonneg : 0 ≤ turan Q x :=
    finite_affine_turan_nonnegative (s.erase i) a b x
  change 0 < turan (s.prod L) x
  rw [hfactor]
  change 0 < turan
    ((Polynomial.C (a i) * (Polynomial.X : ℝ[X]) + Polynomial.C (b i)) * Q) x
  rw [turan_mul_affine]
  exact add_pos_of_nonneg_of_pos
    (mul_nonneg (sq_nonneg _) hQnonneg)
    (mul_pos (sq_pos_of_ne_zero hai) (sq_pos_of_ne_zero hQ))

/-- Scaling by a nonzero real coefficient retains strict positivity off
real roots of an affine product, in all finite dimensions. -/
theorem scaled_affine_turan_strict_offroots {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (a b : ι → ℝ) (c : ℝ) (P : ℝ[X])
    (i : ι) (hi : i ∈ s) (hai : a i ≠ 0) (hc : c ≠ 0)
    (hP : P = Polynomial.C c *
      s.prod (fun j => Polynomial.C (a j) * (Polynomial.X : ℝ[X]) +
        Polynomial.C (b j)))
    (x : ℝ) (hx : P.eval x ≠ 0) :
    0 < turan P x := by
  rw [hP] at hx ⊢
  have hprod :
      (s.prod (fun j => Polynomial.C (a j) * (Polynomial.X : ℝ[X]) +
        Polynomial.C (b j))).eval x ≠ 0 := by
    have hmul : c *
        (s.prod (fun j => Polynomial.C (a j) * (Polynomial.X : ℝ[X]) +
          Polynomial.C (b j))).eval x ≠ 0 := by
      simpa only [Polynomial.eval_mul, Polynomial.eval_C] using hx
    exact (mul_ne_zero_iff.mp hmul).2
  rw [turan_const_mul]
  exact mul_pos (sq_pos_of_ne_zero hc)
    (finite_affine_turan_strict_offroots s a b x i hi hai hprod)

/-- A general real-rooted symmetric pencil with invertible real slopes has
strict Turan inequality at every real non-root, once n > 0. -/
theorem spectral_turan_strict_offroots {n : ℕ}
    (p : ManuscriptChain.Spectral.SymmetricAffinePencil n)
    (h : ManuscriptChain.Spectral.RootFactorization p)
    (hn : 0 < n) (x : ℝ) (hx : p.detPolynomial.eval x ≠ 0) :
    0 < turan p.detPolynomial x := by
  have hlinear (i : Fin n) :
      ManuscriptChain.Spectral.spectralFactor p.center (h.beta i) =
        Polynomial.C (h.beta i) * (Polynomial.X : ℝ[X]) +
          Polynomial.C (1 - p.center * h.beta i) := by
    simp only [ManuscriptChain.Spectral.spectralFactor, map_sub,
      map_mul, map_one]
    ring
  have hP : p.detPolynomial = Polynomial.C (Matrix.det p.base) *
      (Finset.univ : Finset (Fin n)).prod (fun i =>
        Polynomial.C (h.beta i) * (Polynomial.X : ℝ[X]) +
          Polynomial.C (1 - p.center * h.beta i)) := by
    rw [h.factorization]
    simp_rw [hlinear]
  let i : Fin n := ⟨0, hn⟩
  exact scaled_affine_turan_strict_offroots
    (Finset.univ : Finset (Fin n)) h.beta
    (fun j => 1 - p.center * h.beta j)
    (Matrix.det p.base) p.detPolynomial i (Finset.mem_univ i)
    (h.beta_ne_zero i) h.base_det_ne_zero hP x hx

/-- Positive-definite linear slope gives a strict inequality off roots,
even with an indefinite or singular constant matrix. -/
theorem positive_slope_turan_strict_offroots {n : ℕ}
    (p : ManuscriptChain.Spectral.SymmetricAffinePencil n)
    (hp : p.direction.PosDef) (hn : 0 < n)
    (x : ℝ) (hx : p.detPolynomial.eval x ≠ 0) :
    0 < turan p.detPolynomial x := by
  obtain ⟨beta, hfactor⟩ :=
    PaperAdvances.Theorem5_2_RealRoots.positive_slope_factorization p hp
  have hP : p.detPolynomial = Polynomial.C p.direction.det *
      (Finset.univ : Finset (Fin n)).prod (fun i =>
        Polynomial.C (1 : ℝ) * (Polynomial.X : ℝ[X]) +
          Polynomial.C (beta i - p.center)) := by
    simpa only [map_one, one_mul] using hfactor
  let i : Fin n := ⟨0, hn⟩
  exact scaled_affine_turan_strict_offroots
    (Finset.univ : Finset (Fin n))
    (fun _ : Fin n => (1 : ℝ))
    (fun j => beta j - p.center)
    p.direction.det p.detPolynomial i (Finset.mem_univ i)
    one_ne_zero (ne_of_gt hp.det_pos) hP x hx

/-- The ACTUAL odd-zeta Hankel determinant has strict first-derivative
Turan inequality away from its roots, for all admissible parameters. -/
theorem THEOREM_3_7_ACTUAL_TURAN_STRICT
    (p : ManuscriptChain.Real.Parameters)
    (hp : ManuscriptChain.Real.Admissible p)
    (x : ℝ)
    (hx : (ManuscriptChain.Real.realPolynomial
      (ManuscriptChain.Real.delta p)).eval x ≠ 0) :
    0 < turan (ManuscriptChain.Real.realPolynomial
      (ManuscriptChain.Real.delta p)) x := by
  have hh : 0 < p.h := Nat.sub_pos_of_lt hp.N_lt_K
  have hg : ManuscriptChain.General.GramPositive p :=
    ManuscriptChain.GRAM_POSITIVE p hp
  have hs := spectral_turan_strict_offroots
    (ManuscriptChain.Real.manuscriptPencil p)
    (ManuscriptChain.General.factorization p hg) hh x
    (by simpa only [ManuscriptChain.Real.manuscriptPencil_detPolynomial] using hx)
  simpa only [ManuscriptChain.Real.manuscriptPencil_detPolynomial] using hs

/-- Full equality classification for first-derivative Turan wherever it is
strict off roots: equality is equivalent to a multiple zero. -/
theorem turan_eq_zero_iff_multiple_zero (P : ℝ[X]) (x : ℝ)
    (hstrict : P.eval x ≠ 0 → 0 < turan P x) :
    turan P x = 0 ↔ P.eval x = 0 ∧ (Polynomial.derivative P).eval x = 0 := by
  constructor
  · intro hz
    have hp : P.eval x = 0 := by
      by_contra hne
      exact (ne_of_gt (hstrict hne)) hz
    have hs : ((Polynomial.derivative P).eval x) ^ 2 = 0 := by
      simpa only [turan, hp, zero_mul, sub_zero] using hz
    exact ⟨hp, eq_zero_of_pow_eq_zero hs⟩
  · rintro ⟨hp, hd⟩
    simp [turan, hp, hd]

/-- Actual odd-zeta Turan equality cases, for EVERY admissible Hankel size. -/
theorem THEOREM_3_7_ACTUAL_TURAN_EQUALITY
    (p : ManuscriptChain.Real.Parameters)
    (hp : ManuscriptChain.Real.Admissible p) (x : ℝ) :
    turan (ManuscriptChain.Real.realPolynomial
      (ManuscriptChain.Real.delta p)) x = 0 ↔
      (ManuscriptChain.Real.realPolynomial
        (ManuscriptChain.Real.delta p)).eval x = 0 ∧
      (Polynomial.derivative (ManuscriptChain.Real.realPolynomial
        (ManuscriptChain.Real.delta p))).eval x = 0 := by
  exact turan_eq_zero_iff_multiple_zero _ x
    (THEOREM_3_7_ACTUAL_TURAN_STRICT p hp x)

/-- An exact universal finite-degree Rolle separation theorem. -/
theorem real_polynomial_derivative_root_between (P : ℝ[X])
    (a b : ℝ) (hab : a < b)
    (ha : P.eval a = 0) (hb : P.eval b = 0) :
    ∃ x : ℝ, a < x ∧ x < b ∧ (Polynomial.derivative P).eval x = 0 := by
  obtain ⟨x, hx, hd⟩ :=
    exists_deriv_eq_zero hab P.continuousOn (ha.trans hb.symm)
  exact ⟨x, hx.1, hx.2, by simpa only [Polynomial.deriv] using hd⟩

/-- Critical-point separation for zeros of the ACTUAL odd-zeta polynomial.
This is NOT principal-minor interlacing, which is still open. -/
theorem THEOREM_3_7_ACTUAL_CRITICAL_POINT_SEPARATION
    (p : ManuscriptChain.Real.Parameters)
    (a b : ℝ) (hab : a < b)
    (ha : (ManuscriptChain.Real.realPolynomial
      (ManuscriptChain.Real.delta p)).eval a = 0)
    (hb : (ManuscriptChain.Real.realPolynomial
      (ManuscriptChain.Real.delta p)).eval b = 0) :
    ∃ x : ℝ, a < x ∧ x < b ∧
      (Polynomial.derivative (ManuscriptChain.Real.realPolynomial
        (ManuscriptChain.Real.delta p))).eval x = 0 := by
  exact real_polynomial_derivative_root_between _ a b hab ha hb


end PaperAdvances.Theorem3_7_StrictRolle

#print axioms PaperAdvances.Theorem3_7_StrictRolle.finite_affine_turan_strict_offroots
#print axioms PaperAdvances.Theorem3_7_StrictRolle.THEOREM_3_7_ACTUAL_TURAN_STRICT
#print axioms PaperAdvances.Theorem3_7_StrictRolle.THEOREM_3_7_ACTUAL_TURAN_EQUALITY
#print axioms PaperAdvances.Theorem3_7_StrictRolle.THEOREM_3_7_ACTUAL_CRITICAL_POINT_SEPARATION
