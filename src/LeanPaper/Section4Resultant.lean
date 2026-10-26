import LeanPaper.PrimitiveNormDisk
import LeanPaper.ImportedSection4.Proposition_4_2_Resultant_Product_Barrier
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Polynomial.MahlerMeasure

/-!
# The integer resultant in Proposition 4.2

The integer is the actual Sylvester determinant of the two integer polynomials.
Its complex product formula is proved by mapping the resultant to the complex
numbers and factoring the first polynomial, with root multiplicities retained.
Irreducibility over Q and nonvanishing at one conjugate prove coprimality and
therefore nonvanishing of this integer; neither is encoded in a proof field.

For the manuscript primitive polynomial, nonvanishing at the approximation
point is also derived from the already proved Euclidean operator-norm disk.
The remaining uniform height, decay and asymptotic index-selection estimates
of Proposition 4.2 are not asserted by these finite arithmetic results.

Source: new integration of pinned Mathlib Resultant.Basic and MahlerMeasure,
commit db584cd6d46c92f209a44c0f1c829460d327499d; manuscript pp. 14-15, Proposition 4.2.
-/

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator
open Polynomial

namespace LeanPaper.Section4Resultant

def rationalPolynomial (P : ℤ[X]) : ℚ[X] := P.map (algebraMap ℤ ℚ)

def complexPolynomial (P : ℤ[X]) : ℂ[X] := P.map (algebraMap ℤ ℂ)

theorem complexPolynomial_from_rational (P : ℤ[X]) :
    (rationalPolynomial P).map (algebraMap ℚ ℂ) = complexPolynomial P := by
  rw [rationalPolynomial, complexPolynomial, Polynomial.map_map]
  congr 1

/-- Exact product formula, including all conjugates with algebraic multiplicity.
The orientation is Res(f,Q); swapping the arguments changes only its sign. -/
theorem integer_resultant_product (f Q : ℤ[X]) :
    ((Polynomial.resultant f Q f.natDegree Q.natDegree : ℤ) : ℂ) =
      (f.leadingCoeff : ℂ) ^ Q.natDegree *
        ((complexPolynomial f).roots.map (complexPolynomial Q).eval).prod := by
  have h := Polynomial.resultant_eq_prod_eval
    (complexPolynomial f) (complexPolynomial Q) Q.natDegree
    (by rw [complexPolynomial, Polynomial.natDegree_map_eq_of_injective
      (show Function.Injective (algebraMap ℤ ℂ) from Int.cast_injective)])
    (IsAlgClosed.splits _)
  simpa only [complexPolynomial,
    Polynomial.natDegree_map_eq_of_injective
      (show Function.Injective (algebraMap ℤ ℂ) from Int.cast_injective),
    Polynomial.leadingCoeff_map_of_injective
      (show Function.Injective (algebraMap ℤ ℂ) from Int.cast_injective),
    Polynomial.resultant_map_map, eq_intCast] using h

theorem integer_resultant_abs_product (f Q : ℤ[X]) :
    |((Polynomial.resultant f Q f.natDegree Q.natDegree : ℤ) : ℝ)| =
      |(f.leadingCoeff : ℝ)| ^ Q.natDegree *
        ((complexPolynomial f).roots.map
          (fun a => ‖(complexPolynomial Q).eval a‖)).prod := by
  have h := congrArg (fun z : ℂ => ‖z‖) (integer_resultant_product f Q)
  have hprod (s : Multiset ℂ) : ‖s.prod‖ = (s.map (fun z => ‖z‖)).prod :=
    map_multiset_prod (normHom.toMonoidHom : ℂ →* ℝ) s
  simpa only [norm_mul, norm_pow, Complex.norm_intCast, hprod,
    Multiset.map_map, Function.comp_apply] using h

/-- Coprimality is needed only over Q, not over the non-Bezout ring Z[X]. -/
theorem integer_resultant_ne_zero (f Q : ℤ[X])
    (hcop : IsCoprime (rationalPolynomial f) (rationalPolynomial Q)) :
    Polynomial.resultant f Q f.natDegree Q.natDegree ≠ 0 := by
  have h := Polynomial.resultant_ne_zero _ _ hcop
  intro hz
  apply h
  simpa only [rationalPolynomial,
    Polynomial.natDegree_map_eq_of_injective
      (show Function.Injective (algebraMap ℤ ℚ) from Int.cast_injective),
    Polynomial.resultant_map_map, hz, map_zero]

/-- Nonzero evaluation at one root of an irreducible polynomial rules out
every common factor over Q. This is the exact minimal-polynomial argument. -/
theorem coprime_of_irreducible_of_eval_ne_zero (f Q : ℤ[X])
    (hf : Irreducible (rationalPolynomial f)) (a : ℂ)
    (hfa : (complexPolynomial f).eval a = 0)
    (hQa : (complexPolynomial Q).eval a ≠ 0) :
    IsCoprime (rationalPolynomial f) (rationalPolynomial Q) := by
  apply hf.coprime_iff_not_dvd.mpr
  rintro ⟨D, hD⟩
  have h := congrArg (fun P : ℚ[X] => (P.map (algebraMap ℚ ℂ)).eval a) hD
  rw [complexPolynomial_from_rational, Polynomial.map_mul, Polynomial.eval_mul,
    complexPolynomial_from_rational, hfa, zero_mul] at h
  exact hQa h

/-- The entire conjugate product has magnitude at least one, with the
integer and product identity constructed rather than passed as hypotheses. -/
theorem conjugate_product_one_le (f Q : ℤ[X])
    (hcop : IsCoprime (rationalPolynomial f) (rationalPolynomial Q)) :
    1 ≤ |(f.leadingCoeff : ℝ)| ^ Q.natDegree *
      ((complexPolynomial f).roots.map
        (fun a => ‖(complexPolynomial Q).eval a‖)).prod := by
  rw [← integer_resultant_abs_product]
  exact PaperOrder.Section4.proposition_4_2_nonzero_integer_abs_bound _
    (integer_resultant_ne_zero f Q hcop)

theorem irreducible_conjugate_product_one_le (f Q : ℤ[X])
    (hf : Irreducible (rationalPolynomial f)) (a : ℂ)
    (hfa : (complexPolynomial f).eval a = 0)
    (hQa : (complexPolynomial Q).eval a ≠ 0) :
    1 ≤ |(f.leadingCoeff : ℝ)| ^ Q.natDegree *
      ((complexPolynomial f).roots.map
        (fun z => ‖(complexPolynomial Q).eval z‖)).prod :=
  conjugate_product_one_le f Q (coprime_of_irreducible_of_eval_ne_zero f Q hf a hfa hQa)

/-- The naive coefficient height: the maximum absolute value of the integer
coefficients, viewed in R through the complex coefficient sup norm. -/
def naiveHeight (f : ℤ[X]) : ℝ := (complexPolynomial f).supNorm

/-- The precise Mahler bound used in the manuscript, for actual integer f. -/
theorem integer_mahler_bound (f : ℤ[X]) :
    |(f.leadingCoeff : ℝ)| *
        ((complexPolynomial f).roots.map (fun a => max 1 ‖a‖)).prod ≤
      Real.sqrt ((f.natDegree : ℝ) + 1) * naiveHeight f := by
  have h := (complexPolynomial f).mahlerMeasure_le_sqrt_natDegree_add_one_mul_supNorm
  rw [Polynomial.mahlerMeasure_eq_leadingCoeff_mul_prod_roots] at h
  simpa only [naiveHeight, complexPolynomial,
    Polynomial.natDegree_map_eq_of_injective
      (show Function.Injective (algebraMap ℤ ℂ) from Int.cast_injective),
    Polynomial.leadingCoeff_map_of_injective
      (show Function.Injective (algebraMap ℤ ℂ) from Int.cast_injective),
    eq_intCast, Complex.norm_intCast] using h

open ManuscriptChain

/-- Actual primitive-family specialization, with no assumed resultant identity. -/
theorem primitive_conjugate_product_one_le (p : Real.Parameters)
    (f : ℤ[X]) (hf : Irreducible (rationalPolynomial f)) (a : ℂ)
    (hfa : (complexPolynomial f).eval a = 0)
    (hQa : (complexPolynomial (GeneralIrrationality.primitivePolynomial p)).eval a ≠ 0) :
    1 ≤ |(f.leadingCoeff : ℝ)| ^ p.h *
      ((complexPolynomial f).roots.map
        (fun z => ‖(complexPolynomial (GeneralIrrationality.primitivePolynomial p)).eval z‖)).prod := by
  simpa only [GeneralIrrationality.primitivePolynomial_natDegree] using
    irreducible_conjugate_product_one_le f (GeneralIrrationality.primitivePolynomial p)
      hf a hfa hQa

/-- In the actual zero-free norm disk, nonzero resultant follows from
structural admissibility and irreducibility; nonzero polynomial evaluation
is no longer an independent arithmetic assumption. -/
theorem primitive_conjugate_product_one_le_in_norm_disk
    (p : Real.Parameters) (hp : Real.Admissible p)
    (f : ℤ[X]) (hf : Irreducible (rationalPolynomial f)) (a : ℂ)
    (hfa : (complexPolynomial f).eval a = 0)
    (hclose : ‖a - (Real.zeta p.weight : ℂ)‖ <
      1 / ‖OperatorNormDisk.whitened (Real.manuscriptPencil p)‖) :
    1 ≤ |(f.leadingCoeff : ℝ)| ^ p.h *
      ((complexPolynomial f).roots.map
        (fun z => ‖(complexPolynomial (GeneralIrrationality.primitivePolynomial p)).eval z‖)).prod := by
  apply primitive_conjugate_product_one_le p f hf a hfa
  have h := (PrimitiveNormDisk.primitive_exact_norm_disk p hp).2.1 a hclose
  simpa only [complexPolynomial, Polynomial.eval_map] using h

end LeanPaper.Section4Resultant

#print axioms LeanPaper.Section4Resultant.integer_resultant_product
#print axioms LeanPaper.Section4Resultant.irreducible_conjugate_product_one_le
#print axioms LeanPaper.Section4Resultant.integer_mahler_bound
#print axioms LeanPaper.Section4Resultant.primitive_conjugate_product_one_le_in_norm_disk
