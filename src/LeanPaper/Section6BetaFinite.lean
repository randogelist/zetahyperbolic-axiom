import Mathlib.Tactic

/-! Finite beta sign, tensor-grid and coefficient-energy inputs adapted from supplied archive 23.
These concrete algebraic statements do not identify a continuous Beukers/beta measure.
The raw beta parity retains (-1)^N; only the explicitly normalized model cancels it. -/


-- Source unit: Paper10Section6BetaSign

/-!
## Paper 10 / Block 10: beta character / Vandermonde parity.
With manuscript sign convention (-1)^(j-N) the product is (-1)^N, not
uniformly +1. A positivity claim must account for N parity or any
additional global sign in the residue normalization.
-/

namespace PaperChronology.Paper10

/-- Literal cancellation of the character sign against the derivative
sign: the residual sign depends ONLY on the lower pole index N. -/
theorem PAPER10_BETA_VANDERMONDE_RESIDUAL_SIGN
    (j N : ℕ) (h : N ≤ j) :
    (-1 : ℚ) ^ j * (-1 : ℚ) ^ (j - N) = (-1 : ℚ) ^ N := by
  rw [← pow_add]
  have heq : j + (j - N) = N + 2 * (j - N) := by omega
  rw [heq]
  simp [pow_add, pow_mul]

/-- Even lower pole index: the character and Vandermonde signs cancel. -/
theorem PAPER10_BETA_VANDERMONDE_EVEN_BASE
    (j t : ℕ) (h : 2 * t ≤ j) :
    (-1 : ℚ) ^ j * (-1 : ℚ) ^ (j - 2 * t) = 1 := by
  simpa [pow_mul] using PAPER10_BETA_VANDERMONDE_RESIDUAL_SIGN j (2 * t) h

/-- Odd lower pole index: an overall negative sign remains. -/
theorem PAPER10_BETA_VANDERMONDE_ODD_BASE
    (j t : ℕ) (h : 2 * t + 1 ≤ j) :
    (-1 : ℚ) ^ j * (-1 : ℚ) ^ (j - (2 * t + 1)) = -1 := by
  simpa [pow_add, pow_mul] using
    PAPER10_BETA_VANDERMONDE_RESIDUAL_SIGN j (2 * t + 1) h

end PaperChronology.Paper10

#print axioms PaperChronology.Paper10.PAPER10_BETA_VANDERMONDE_RESIDUAL_SIGN
#print axioms PaperChronology.Paper10.PAPER10_BETA_VANDERMONDE_EVEN_BASE
#print axioms PaperChronology.Paper10.PAPER10_BETA_VANDERMONDE_ODD_BASE


-- Source unit: Paper10Section6BetaNormalizedSign

/-!
Paper 10, Section 6. Corrected complete parity identity. The raw
character times Vandermonde derivative carries residual (-1)^N;
including the global base-index normalization cancels it for all N.
This checks sign bookkeeping only. It does NOT prove positivity or
nonvanishing of the actual Beta pencil's numerical residues.
-/

namespace PaperChronology.Paper10

/-- The compensating global sign cancels the residual Vandermonde parity. -/
theorem PAPER10_BETA_FULL_CHARACTER_VANDERMONDE_CANCELLATION
    (j N : ℕ) (h : N ≤ j) :
    (-1 : ℚ) ^ N * ((-1 : ℚ) ^ j * (-1 : ℚ) ^ (j - N)) = 1 := by
  rw [PAPER10_BETA_VANDERMONDE_RESIDUAL_SIGN j N h]
  rw [← mul_pow]
  norm_num

end PaperChronology.Paper10

#print axioms PaperChronology.Paper10.PAPER10_BETA_FULL_CHARACTER_VANDERMONDE_CANCELLATION


-- Source unit: Paper10Section6PositiveDiagonal

/-!
Section 3 / 6 finite spectral positivity interface. An actually positive
residue diagonal produces a positive weighted quadratic form, and an
injective real analysis map gives strict positive definiteness. This
is independent of any unproved claim that the manuscript's beta weights
or Vandermonde map satisfy these two hypotheses.
-/

namespace PaperChronology.Paper10

/-- A finite positive weighted sum of squares is nonnegative. -/
theorem PAPER10_POSITIVE_DIAGONAL_NONNEG
    {n : ℕ} (gamma v : Fin n → ℝ)
    (hgamma : ∀ i, 0 < gamma i) :
    0 ≤ ∑ i : Fin n, gamma i * (v i) ^ 2 := by
  apply Finset.sum_nonneg
  intro i _
  exact mul_nonneg (hgamma i).le (sq_nonneg _)

/-- Such a form is strictly positive when some analysis coordinate
is nonzero. -/
theorem PAPER10_POSITIVE_DIAGONAL_STRICT
    {n : ℕ} (gamma v : Fin n → ℝ)
    (hgamma : ∀ i, 0 < gamma i)
    (hnonzero : ∃ i, v i ≠ 0) :
    0 < ∑ i : Fin n, gamma i * (v i) ^ 2 := by
  obtain ⟨i, hi⟩ := hnonzero
  have hsquare : 0 < (v i) ^ 2 := sq_pos_of_ne_zero hi
  have hterm : 0 < gamma i * (v i) ^ 2 :=
    mul_pos (hgamma i) hsquare
  calc
    0 < gamma i * (v i) ^ 2 := hterm
    _ ≤ ∑ j : Fin n, gamma j * (v j) ^ 2 := by
      exact Finset.single_le_sum
        (fun j _ => mul_nonneg (hgamma j).le (sq_nonneg _))
        (Finset.mem_univ i)

end PaperChronology.Paper10

#print axioms PaperChronology.Paper10.PAPER10_POSITIVE_DIAGONAL_NONNEG
#print axioms PaperChronology.Paper10.PAPER10_POSITIVE_DIAGONAL_STRICT


-- Source unit: Paper10Section3InjectiveWeightedGram

/-!
Section 3: two-point Vandermonde independence and weighted Gram energy.
Unlike a statement requiring a generic supplied positive definite Gram
matrix, the two-node theorem proves strict positivity directly from
u != v, positive weights and a nonzero coefficient vector.

The all-dimensional transfer states the precise additional hypothesis:
injectivity of the actual finite evaluation / analysis map. That
injectivity is not silently inferred for the manuscript's higher-rank
Cauchy-Vandermonde matrices.
-/

namespace PaperChronology.Paper10

/-- Two distinct nodes give linearly independent affine evaluations. -/
theorem PAPER10_TWO_NODE_VANDERMONDE_ZERO
    (u v a b : ℝ) (huv : u ≠ v)
    (hfirst : a + u * b = 0) (hsecond : a + v * b = 0) :
    a = 0 ∧ b = 0 := by
  have hdiff : (u - v) * b = 0 := by
    calc
      (u - v) * b = (a + u * b) - (a + v * b) := by ring
      _ = 0 := by rw [hfirst, hsecond]; ring
  have hb : b = 0 :=
    (mul_eq_zero.mp hdiff).resolve_left (sub_ne_zero.mpr huv)
  constructor
  · simpa [hb] using hfirst
  · exact hb

/-- An unconditional, strictly positive, concrete two-point Gram form. -/
theorem PAPER10_TWO_NODE_VANDERMONDE_GRAM_STRICT
    (u v w0 w1 a b : ℝ)
    (huv : u ≠ v) (hw0 : 0 < w0) (hw1 : 0 < w1)
    (hcoeff : a ≠ 0 ∨ b ≠ 0) :
    0 < w0 * (a + u * b) ^ 2 + w1 * (a + v * b) ^ 2 := by
  by_cases hfirst : a + u * b = 0
  · have hsecond : a + v * b ≠ 0 := by
      intro heq
      obtain ⟨ha, hb⟩ :=
        PAPER10_TWO_NODE_VANDERMONDE_ZERO u v a b huv hfirst heq
      exact hcoeff.elim (fun h => h ha) (fun h => h hb)
    have hpos : 0 < w1 * (a + v * b) ^ 2 :=
      mul_pos hw1 (sq_pos_of_ne_zero hsecond)
    simpa [hfirst] using hpos
  · have hpos : 0 < w0 * (a + u * b) ^ 2 :=
      mul_pos hw0 (sq_pos_of_ne_zero hfirst)
    have hnonneg : 0 ≤ w1 * (a + v * b) ^ 2 :=
      mul_nonneg hw1.le (sq_nonneg _)
    linarith

/-- For arbitrary finite dimension, a positive diagonal and an
injective (concrete, finite-sum) analysis operator produce a strictly
positive quadratic form. No Gram positivity is assumed as a Prop. -/
theorem PAPER10_FINITE_WEIGHTED_GRAM_STRICT
    {m n : ℕ} (A : Fin m → Fin n → ℝ) (gamma : Fin m → ℝ)
    (v : Fin n → ℝ)
    (hgamma : ∀ i, 0 < gamma i)
    (hinj : Function.Injective
      (fun t : Fin n → ℝ =>
        (fun i : Fin m => ∑ j : Fin n, A i j * t j)))
    (hv : v ≠ 0) :
    0 < ∑ i : Fin m, gamma i * (∑ j : Fin n, A i j * v j) ^ 2 := by
  apply PAPER10_POSITIVE_DIAGONAL_STRICT gamma
    (fun i : Fin m => ∑ j : Fin n, A i j * v j) hgamma
  by_contra hn
  push_neg at hn
  have hEq :
      (fun i : Fin m => ∑ j : Fin n, A i j * v j) =
      (fun i : Fin m => ∑ j : Fin n, A i j * (0 : Fin n → ℝ) j) := by
    funext i
    simpa using hn i
  exact hv (hinj hEq)

end PaperChronology.Paper10

#print axioms PaperChronology.Paper10.PAPER10_TWO_NODE_VANDERMONDE_ZERO
#print axioms PaperChronology.Paper10.PAPER10_TWO_NODE_VANDERMONDE_GRAM_STRICT
#print axioms PaperChronology.Paper10.PAPER10_FINITE_WEIGHTED_GRAM_STRICT


-- Source unit: Paper10Section5TensorGridEnergy

/-!
Section 5, two-variable finite-rank input: a *genuine* 2 by 2 tensor
interpolation grid. Distinct x- and y-nodes prove independence of the
four bilinear monomials 1, x, y, xy. Four strictly positive point masses
then produce a strictly positive definite 4 by 4 weighted Gram pencil.
This is not an identification with the continuous Beukers measure.
-/

namespace PaperChronology.Paper10

/-- The 2 by 2 tensor grid detects every bilinear coefficient vector. -/
theorem PAPER10_BILINEAR_TENSOR_GRID_ZERO
    (u v s t a b c d : ℝ)
    (huv : u ≠ v) (hst : s ≠ t)
    (h00 : a + u * b + s * c + u * s * d = 0)
    (h01 : a + u * b + t * c + u * t * d = 0)
    (h10 : a + v * b + s * c + v * s * d = 0)
    (h11 : a + v * b + t * c + v * t * d = 0) :
    a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0 := by
  have hu0 : (a + u * b) + s * (c + u * d) = 0 := by
    calc
      (a + u * b) + s * (c + u * d) =
          a + u * b + s * c + u * s * d := by ring
      _ = 0 := h00
  have hu1 : (a + u * b) + t * (c + u * d) = 0 := by
    calc
      (a + u * b) + t * (c + u * d) =
          a + u * b + t * c + u * t * d := by ring
      _ = 0 := h01
  have hv0 : (a + v * b) + s * (c + v * d) = 0 := by
    calc
      (a + v * b) + s * (c + v * d) =
          a + v * b + s * c + v * s * d := by ring
      _ = 0 := h10
  have hv1 : (a + v * b) + t * (c + v * d) = 0 := by
    calc
      (a + v * b) + t * (c + v * d) =
          a + v * b + t * c + v * t * d := by ring
      _ = 0 := h11
  obtain ⟨hau, hcu⟩ :=
    PAPER10_TWO_NODE_VANDERMONDE_ZERO s t (a + u * b) (c + u * d)
      hst hu0 hu1
  obtain ⟨hav, hcv⟩ :=
    PAPER10_TWO_NODE_VANDERMONDE_ZERO s t (a + v * b) (c + v * d)
      hst hv0 hv1
  obtain ⟨ha, hb⟩ :=
    PAPER10_TWO_NODE_VANDERMONDE_ZERO u v a b huv hau hav
  obtain ⟨hc, hd⟩ :=
    PAPER10_TWO_NODE_VANDERMONDE_ZERO u v c d huv hcu hcv
  exact ⟨ha, hb, hc, hd⟩

/-- Explicit strictly positive tensor-grid Gram energy on four
bilinear coefficients, without an assumed injective matrix. -/
theorem PAPER10_BILINEAR_TENSOR_GRID_GRAM_STRICT
    (u v s t w00 w01 w10 w11 a b c d : ℝ)
    (huv : u ≠ v) (hst : s ≠ t)
    (hw00 : 0 < w00) (hw01 : 0 < w01)
    (hw10 : 0 < w10) (hw11 : 0 < w11)
    (hcoeff : a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0 ∨ d ≠ 0) :
    0 < w00 * (a + u * b + s * c + u * s * d) ^ 2 +
      w01 * (a + u * b + t * c + u * t * d) ^ 2 +
      w10 * (a + v * b + s * c + v * s * d) ^ 2 +
      w11 * (a + v * b + t * c + v * t * d) ^ 2 := by
  let E00 : ℝ := a + u * b + s * c + u * s * d
  let E01 : ℝ := a + u * b + t * c + u * t * d
  let E10 : ℝ := a + v * b + s * c + v * s * d
  let E11 : ℝ := a + v * b + t * c + v * t * d
  change 0 < w00 * E00 ^ 2 + w01 * E01 ^ 2 +
    w10 * E10 ^ 2 + w11 * E11 ^ 2
  have hnonzero : E00 ≠ 0 ∨ E01 ≠ 0 ∨ E10 ≠ 0 ∨ E11 ≠ 0 := by
    by_contra hbad
    push_neg at hbad
    obtain ⟨z00, z01, z10, z11⟩ := hbad
    obtain ⟨ha, hb, hc, hd⟩ :=
      PAPER10_BILINEAR_TENSOR_GRID_ZERO
        u v s t a b c d huv hst z00 z01 z10 z11
    rcases hcoeff with h | h | h | h
    · exact h ha
    · exact h hb
    · exact h hc
    · exact h hd
  have h0 : 0 ≤ w00 * E00 ^ 2 := mul_nonneg hw00.le (sq_nonneg _)
  have h1 : 0 ≤ w01 * E01 ^ 2 := mul_nonneg hw01.le (sq_nonneg _)
  have h2 : 0 ≤ w10 * E10 ^ 2 := mul_nonneg hw10.le (sq_nonneg _)
  have h3 : 0 ≤ w11 * E11 ^ 2 := mul_nonneg hw11.le (sq_nonneg _)
  rcases hnonzero with hn | hn | hn | hn
  · have hp : 0 < w00 * E00 ^ 2 := mul_pos hw00 (sq_pos_of_ne_zero hn)
    linarith
  · have hp : 0 < w01 * E01 ^ 2 := mul_pos hw01 (sq_pos_of_ne_zero hn)
    linarith
  · have hp : 0 < w10 * E10 ^ 2 := mul_pos hw10 (sq_pos_of_ne_zero hn)
    linarith
  · have hp : 0 < w11 * E11 ^ 2 := mul_pos hw11 (sq_pos_of_ne_zero hn)
    linarith

end PaperChronology.Paper10

#print axioms PaperChronology.Paper10.PAPER10_BILINEAR_TENSOR_GRID_ZERO
#print axioms PaperChronology.Paper10.PAPER10_BILINEAR_TENSOR_GRID_GRAM_STRICT


-- Source unit: Paper10Section6BetaResidueEnergy

/-!
Sections 5/6, character-residue normalization: a real-valued exact
cancellation identity, a concrete normalized residue coefficient, and
positive quadratic energy for all finite injective analysis pencils.
These are true structural results, but they do not identify the paper's
actual unnormalized beta pencil with this normalized model. In
particular, the raw parity product has residual (-1)^N.
-/

namespace PaperChronology.Paper10

/-- Exact character times Vandermonde parity after multiplying by the
base-index normalization, now in the field of real numbers. -/
theorem PAPER10_BETA_REAL_SIGN_NORMALIZATION
    (j N : ℕ) (hj : N ≤ j) :
    (-1 : ℝ) ^ N * ((-1 : ℝ) ^ j * (-1 : ℝ) ^ (j - N)) = 1 := by
  have h : (-1 : ℝ) ^ j * (-1 : ℝ) ^ (j - N) = (-1 : ℝ) ^ N := by
    rw [← pow_add]
    have heq : j + (j - N) = N + 2 * (j - N) := by omega
    rw [heq]
    simp [pow_add, pow_mul]
  rw [h, ← mul_pow]
  norm_num

/-- Actual scalar formula for a normalized beta residue, not an
abstract positivity assumption. -/
noncomputable def PAPER10_BETA_NORMALIZED_RESIDUE
    (N j : ℕ) (q : ℝ) : ℝ :=
  ((-1 : ℝ) ^ N * ((-1 : ℝ) ^ j * (-1 : ℝ) ^ (j - N))) * q

theorem PAPER10_BETA_NORMALIZED_RESIDUE_EQ
    (N j : ℕ) (hNj : N ≤ j) (q : ℝ) :
    PAPER10_BETA_NORMALIZED_RESIDUE N j q = q := by
  unfold PAPER10_BETA_NORMALIZED_RESIDUE
  rw [PAPER10_BETA_REAL_SIGN_NORMALIZATION j N hNj]
  ring

/-- Positive amplitudes yield positive normalized residues at every
finite pole index j=N+i. -/
theorem PAPER10_BETA_NORMALIZED_RESIDUES_POSITIVE
    (N m : ℕ) (q : Fin m → ℝ) (hq : ∀ i, 0 < q i) :
    ∀ i : Fin m,
      0 < PAPER10_BETA_NORMALIZED_RESIDUE N (N + (i : ℕ)) (q i) := by
  intro i
  rw [PAPER10_BETA_NORMALIZED_RESIDUE_EQ
    N (N + (i : ℕ)) (by omega) (q i)]
  exact hq i

/-- Finite beta-type pencil: exact signed normalized residues with
positive amplitudes and injective finite evaluation imply strict
positive definiteness of its quadratic form. -/
theorem PAPER10_BETA_INJECTIVE_PENCIL_STRICT
    {m n : ℕ} (N : ℕ) (A : Fin m → Fin n → ℝ)
    (q : Fin m → ℝ) (v : Fin n → ℝ)
    (hq : ∀ i, 0 < q i)
    (hinj : Function.Injective
      (fun t : Fin n → ℝ =>
        (fun i : Fin m => ∑ j : Fin n, A i j * t j)))
    (hv : v ≠ 0) :
    0 < ∑ i : Fin m,
      PAPER10_BETA_NORMALIZED_RESIDUE N (N + (i : ℕ)) (q i) *
        (∑ j : Fin n, A i j * v j) ^ 2 := by
  exact PAPER10_FINITE_WEIGHTED_GRAM_STRICT A
    (fun i => PAPER10_BETA_NORMALIZED_RESIDUE N (N + (i : ℕ)) (q i))
    v (PAPER10_BETA_NORMALIZED_RESIDUES_POSITIVE N m q hq) hinj hv

/-- At two distinct real nodes the beta-type normalized pencil is
unconditionally positive for every nonzero two-dimensional vector. -/
theorem PAPER10_BETA_TWO_NODE_PENCIL_STRICT
    (N : ℕ) (u v q0 q1 a b : ℝ)
    (huv : u ≠ v) (hq0 : 0 < q0) (hq1 : 0 < q1)
    (hcoeff : a ≠ 0 ∨ b ≠ 0) :
    0 < PAPER10_BETA_NORMALIZED_RESIDUE N N q0 * (a + u * b) ^ 2 +
      PAPER10_BETA_NORMALIZED_RESIDUE N (N + 1) q1 * (a + v * b) ^ 2 := by
  rw [PAPER10_BETA_NORMALIZED_RESIDUE_EQ N N (le_refl N) q0,
      PAPER10_BETA_NORMALIZED_RESIDUE_EQ N (N + 1) (by omega) q1]
  exact PAPER10_TWO_NODE_VANDERMONDE_GRAM_STRICT
    u v q0 q1 a b huv hq0 hq1 hcoeff

end PaperChronology.Paper10

#print axioms PaperChronology.Paper10.PAPER10_BETA_REAL_SIGN_NORMALIZATION
#print axioms PaperChronology.Paper10.PAPER10_BETA_NORMALIZED_RESIDUE_EQ
#print axioms PaperChronology.Paper10.PAPER10_BETA_NORMALIZED_RESIDUES_POSITIVE
#print axioms PaperChronology.Paper10.PAPER10_BETA_INJECTIVE_PENCIL_STRICT
#print axioms PaperChronology.Paper10.PAPER10_BETA_TWO_NODE_PENCIL_STRICT


-- Source unit: Paper10Section6BetaTensorGrid

/-!
Section 6 model: a four-pole beta-normalized residue scheme yields
strict positivity of a genuinely two-variable 2x2 tensor-grid pencil.
The normalized character/Vandermonde signs are handled by the exact
prior parity lemma; this finite discrete model does not establish the
manuscript's continuous two-variable beta pencil.
-/

namespace PaperChronology.Paper10

/-- Four normalized consecutive character residue weights, applied
to bilinear interpolation on two distinct nodes in each direction. -/
theorem PAPER10_BETA_BILINEAR_TENSOR_GRID_STRICT
    (N : ℕ) (u v s t w00 w01 w10 w11 a b c d : ℝ)
    (huv : u ≠ v) (hst : s ≠ t)
    (hw00 : 0 < w00) (hw01 : 0 < w01)
    (hw10 : 0 < w10) (hw11 : 0 < w11)
    (hcoeff : a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0 ∨ d ≠ 0) :
    0 < PAPER10_BETA_NORMALIZED_RESIDUE N N w00 *
      (a + u * b + s * c + u * s * d) ^ 2 +
      PAPER10_BETA_NORMALIZED_RESIDUE N (N + 1) w01 *
      (a + u * b + t * c + u * t * d) ^ 2 +
      PAPER10_BETA_NORMALIZED_RESIDUE N (N + 2) w10 *
      (a + v * b + s * c + v * s * d) ^ 2 +
      PAPER10_BETA_NORMALIZED_RESIDUE N (N + 3) w11 *
      (a + v * b + t * c + v * t * d) ^ 2 := by
  rw [PAPER10_BETA_NORMALIZED_RESIDUE_EQ N N (le_refl N) w00,
      PAPER10_BETA_NORMALIZED_RESIDUE_EQ N (N + 1) (by omega) w01,
      PAPER10_BETA_NORMALIZED_RESIDUE_EQ N (N + 2) (by omega) w10,
      PAPER10_BETA_NORMALIZED_RESIDUE_EQ N (N + 3) (by omega) w11]
  exact PAPER10_BILINEAR_TENSOR_GRID_GRAM_STRICT
    u v s t w00 w01 w10 w11 a b c d huv hst
    hw00 hw01 hw10 hw11 hcoeff

end PaperChronology.Paper10

#print axioms PaperChronology.Paper10.PAPER10_BETA_BILINEAR_TENSOR_GRID_STRICT


-- Source unit: Paper10Section3ThreeNodeGram

/-!
Section 3: concrete two-node Gram determinant, then a three-node
quadratic Vandermonde evaluation and its strictly positive weighted
Gram form. All stated distinct-node and positive-weight hypotheses are
on actual scalars, with no opaque full-rank proof field. This is a
finite special case, not the paper's all-order total positivity theorem.
-/

namespace PaperChronology.Paper10

/-- Exact two-node affine Gram determinant factorization. -/
theorem PAPER10_TWO_NODE_GRAM_DETERMINANT
    (u v q0 q1 : ℝ) :
    (q0 + q1) * (q0 * u ^ 2 + q1 * v ^ 2) -
      (q0 * u + q1 * v) ^ 2 = q0 * q1 * (u - v) ^ 2 := by
  ring

/-- An unconditional strictly positive two-node Gram determinant. -/
theorem PAPER10_TWO_NODE_GRAM_DETERMINANT_POSITIVE
    (u v q0 q1 : ℝ) (huv : u ≠ v)
    (hq0 : 0 < q0) (hq1 : 0 < q1) :
    0 < (q0 + q1) * (q0 * u ^ 2 + q1 * v ^ 2) -
      (q0 * u + q1 * v) ^ 2 := by
  rw [PAPER10_TWO_NODE_GRAM_DETERMINANT]
  exact mul_pos (mul_pos hq0 hq1) (sq_pos_of_ne_zero (sub_ne_zero.mpr huv))

/-- Three pairwise distinct nodes determine a quadratic polynomial
from its values: vanishing at all three forces all coefficients zero. -/
theorem PAPER10_THREE_NODE_VANDERMONDE_ZERO
    (u v w a b c : ℝ)
    (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w)
    (hu : a + u * b + u ^ 2 * c = 0)
    (hv : a + v * b + v ^ 2 * c = 0)
    (hw : a + w * b + w ^ 2 * c = 0) :
    a = 0 ∧ b = 0 ∧ c = 0 := by
  have hvsub : (v - u) * (b + (v + u) * c) = 0 := by
    calc
      (v - u) * (b + (v + u) * c) =
          (a + v * b + v ^ 2 * c) - (a + u * b + u ^ 2 * c) := by ring
      _ = 0 := by rw [hv, hu]; ring
  have hwsub : (w - u) * (b + (w + u) * c) = 0 := by
    calc
      (w - u) * (b + (w + u) * c) =
          (a + w * b + w ^ 2 * c) - (a + u * b + u ^ 2 * c) := by ring
      _ = 0 := by rw [hw, hu]; ring
  have hbv : b + (v + u) * c = 0 :=
    (mul_eq_zero.mp hvsub).resolve_left (sub_ne_zero.mpr huv.symm)
  have hbw : b + (w + u) * c = 0 :=
    (mul_eq_zero.mp hwsub).resolve_left (sub_ne_zero.mpr huw.symm)
  have hcsub : (v - w) * c = 0 := by
    calc
      (v - w) * c = (b + (v + u) * c) - (b + (w + u) * c) := by ring
      _ = 0 := by rw [hbv, hbw]; ring
  have hc : c = 0 :=
    (mul_eq_zero.mp hcsub).resolve_left (sub_ne_zero.mpr hvw)
  have hb : b = 0 := by simpa [hc] using hbv
  have ha : a = 0 := by simpa [hb, hc] using hu
  exact ⟨ha, hb, hc⟩

/-- Concrete three-node quadratic Gram positivity for all nonzero
coefficient triples and arbitrary strictly positive node weights. -/
theorem PAPER10_THREE_NODE_WEIGHTED_GRAM_STRICT
    (u v w q0 q1 q2 a b c : ℝ)
    (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w)
    (hq0 : 0 < q0) (hq1 : 0 < q1) (hq2 : 0 < q2)
    (hcoeff : a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0) :
    0 < q0 * (a + u * b + u ^ 2 * c) ^ 2 +
      q1 * (a + v * b + v ^ 2 * c) ^ 2 +
      q2 * (a + w * b + w ^ 2 * c) ^ 2 := by
  by_cases h0 : a + u * b + u ^ 2 * c = 0
  · by_cases h1 : a + v * b + v ^ 2 * c = 0
    · have h2 : a + w * b + w ^ 2 * c ≠ 0 := by
        intro h2
        obtain ⟨ha, hb, hc⟩ :=
          PAPER10_THREE_NODE_VANDERMONDE_ZERO
            u v w a b c huv huw hvw h0 h1 h2
        exact hcoeff.elim (fun h => h ha)
          (fun h => h.elim (fun h' => h' hb) (fun h' => h' hc))
      have hp : 0 < q2 * (a + w * b + w ^ 2 * c) ^ 2 :=
        mul_pos hq2 (sq_pos_of_ne_zero h2)
      simpa [h0, h1] using hp
    · have hp : 0 < q1 * (a + v * b + v ^ 2 * c) ^ 2 :=
        mul_pos hq1 (sq_pos_of_ne_zero h1)
      have hnn : 0 ≤ q2 * (a + w * b + w ^ 2 * c) ^ 2 :=
        mul_nonneg hq2.le (sq_nonneg _)
      simpa [h0] using (add_pos_of_pos_of_nonneg hp hnn)
  · have hp : 0 < q0 * (a + u * b + u ^ 2 * c) ^ 2 :=
      mul_pos hq0 (sq_pos_of_ne_zero h0)
    have hnn1 : 0 ≤ q1 * (a + v * b + v ^ 2 * c) ^ 2 :=
      mul_nonneg hq1.le (sq_nonneg _)
    have hnn2 : 0 ≤ q2 * (a + w * b + w ^ 2 * c) ^ 2 :=
      mul_nonneg hq2.le (sq_nonneg _)
    linarith

end PaperChronology.Paper10

#print axioms PaperChronology.Paper10.PAPER10_TWO_NODE_GRAM_DETERMINANT
#print axioms PaperChronology.Paper10.PAPER10_TWO_NODE_GRAM_DETERMINANT_POSITIVE
#print axioms PaperChronology.Paper10.PAPER10_THREE_NODE_VANDERMONDE_ZERO
#print axioms PaperChronology.Paper10.PAPER10_THREE_NODE_WEIGHTED_GRAM_STRICT


-- Source unit: Paper10Section6BetaThreeNode

/-!
Section 6: higher-rank concrete normalized beta pencil.
Three distinct real nodes and positive amplitudes yield a strictly
positive quadratic Gram form; the precise normalized character parity
is inherited from the verified residue formula. The paper's own beta
pencil identification is not assumed or claimed.
-/

namespace PaperChronology.Paper10

/-- Positive-definite quadratic three-node beta-type model, using the
actual previously proved real character/Vandermonde normalization. -/
theorem PAPER10_BETA_THREE_NODE_PENCIL_STRICT
    (N : ℕ) (u v w q0 q1 q2 a b c : ℝ)
    (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w)
    (hq0 : 0 < q0) (hq1 : 0 < q1) (hq2 : 0 < q2)
    (hcoeff : a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0) :
    0 < PAPER10_BETA_NORMALIZED_RESIDUE N N q0 *
        (a + u * b + u ^ 2 * c) ^ 2 +
      PAPER10_BETA_NORMALIZED_RESIDUE N (N + 1) q1 *
        (a + v * b + v ^ 2 * c) ^ 2 +
      PAPER10_BETA_NORMALIZED_RESIDUE N (N + 2) q2 *
        (a + w * b + w ^ 2 * c) ^ 2 := by
  rw [PAPER10_BETA_NORMALIZED_RESIDUE_EQ N N (le_refl N) q0,
      PAPER10_BETA_NORMALIZED_RESIDUE_EQ N (N + 1) (by omega) q1,
      PAPER10_BETA_NORMALIZED_RESIDUE_EQ N (N + 2) (by omega) q2]
  exact PAPER10_THREE_NODE_WEIGHTED_GRAM_STRICT
    u v w q0 q1 q2 a b c huv huw hvw hq0 hq1 hq2 hcoeff

end PaperChronology.Paper10

#print axioms PaperChronology.Paper10.PAPER10_BETA_THREE_NODE_PENCIL_STRICT


-- Source unit: Paper10Section6ShiftPoleAlignment

/-!
Section 4.5 / 6.6: exact pole-order alignment in the differential-shift
coupling. At each pole t = -j^2, the factor (-t)^(k-m) times j^(2m)
is j^(2k), uniformly for 1 <= m <= k. Therefore all scalar variables
X_m combine into a single Z=sum a_m X_m. This is the algebraic part;
functional and matrix-derivative identification remains a separate task.
-/

namespace PaperChronology.Paper10

/-- Every summand has the identical j^(2k) pole factor. -/
theorem PAPER10_DIFFERENTIAL_SHIFT_POLE_ALIGNMENT
    (j k m : ℕ) (hm : m ≤ k) :
    (j : ℚ) ^ (2 * (k - m)) * (j : ℚ) ^ (2 * m) = (j : ℚ) ^ (2 * k) := by
  rw [← pow_add]
  congr 1
  omega

/-- Arbitrary rational linear combinations of odd weights align to
one scalar Z and the same highest-order pole power. -/
theorem PAPER10_DIFFERENTIAL_SHIFT_FINITE_COUPLING
    (j k : ℕ) (a X : ℕ → ℚ) :
    (∑ m ∈ Finset.Icc 1 k,
      a m * ((j : ℚ) ^ (2 * (k - m)) * (j : ℚ) ^ (2 * m)) * X m) =
      (j : ℚ) ^ (2 * k) * ∑ m ∈ Finset.Icc 1 k, a m * X m := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  have hmk : m ≤ k := (Finset.mem_Icc.mp hm).2
  rw [PAPER10_DIFFERENTIAL_SHIFT_POLE_ALIGNMENT j k m hmk]
  ring

end PaperChronology.Paper10

#print axioms PaperChronology.Paper10.PAPER10_DIFFERENTIAL_SHIFT_POLE_ALIGNMENT
#print axioms PaperChronology.Paper10.PAPER10_DIFFERENTIAL_SHIFT_FINITE_COUPLING
