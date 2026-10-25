import Theorem_4_1_Content_Gram_Cancellation
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Genuine one-step contraction criterion for the original primitive pencil

The original affine family has K_n = 30(n+1), so its K^2 increment is
900(2n+3). This file proves that a UNIFORM strictly negative adjacent
content-plus-Gram logarithmic drift of order (2n+3) forces eventual
quadratic decay of the actual integer primitive determinant. The initial
value is arbitrary: a finite additive constant is absorbed by the quadratic
growth. This is an analytic reduction, NOT a proof of its open drift input.

All arithmetic and determinant data here are the actual manuscript inputs;
no custom/assumed zeta value or artificial polynomial is substituted.
-/

noncomputable section

namespace ManuscriptChain.AdjacentLogIncrement

open GeneralIrrationality FiniteEnergy ContentGramCancellation

/-- Exact logarithmic potential for the original fixed-weight affine family. -/
def affineEnergy (k n : ℕ) : ℝ :=
  contentLog (affineFamily k n) + gramLog (affineFamily k n)

/-- The actual positive primitive integer polynomial evaluated at zeta(2k+1). -/
def primitiveValue (k n : ℕ) : ℝ :=
  RealTransfer.evalReal (primitivePolynomial (affineFamily k n))
    (Real.zeta (affineFamily k n).weight)

/-- Strict positivity is unconditional, not an input to the drift criterion. -/
theorem primitiveValue_pos (k n : ℕ) (hk : 0 < k) :
    0 < primitiveValue k n := by
  exact primitivePolynomial_eval_pos (affineFamily k n)
    (affineFamily_admissible k hk n)

/-- The exact content/Gram cancellation from the previously proved stage. -/
theorem log_primitiveValue_eq_affineEnergy (k n : ℕ) (hk : 0 < k) :
    _root_.Real.log (primitiveValue k n) = affineEnergy k n := by
  exact primitive_eval_log_eq_content_add_gram (affineFamily k n)
    (affineFamily_admissible k hk n)

/-- Unconditional exact relation between consecutive primitive values. -/
theorem affineEnergy_increment_eq_log_ratio (k n : ℕ) (hk : 0 < k) :
    affineEnergy k (n + 1) - affineEnergy k n =
      _root_.Real.log (primitiveValue k (n + 1) / primitiveValue k n) := by
  rw [_root_.Real.log_div (primitiveValue_pos k (n + 1) hk).ne'
    (primitiveValue_pos k n hk).ne']
  rw [log_primitiveValue_eq_affineEnergy k (n + 1) hk,
    log_primitiveValue_eq_affineEnergy k n hk]

/-- Elementary telescoping with the EXACT increments of (n+1)^2.
A finite initial value does not prevent eventual negative quadratic drift. -/
theorem eventual_quadratic_bound_of_adjacent_drift
    (F : ℕ → ℝ) (c : ℝ) (hc : 0 < c)
    (hstep : ∀ n : ℕ,
      F (n + 1) ≤ F n - c * (2 * (n : ℝ) + 3)) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      F n ≤ -(c / 2) * ((n : ℝ) + 1) ^ 2 := by
  have hglobal : ∀ n : ℕ,
      F n ≤ F 0 + c - c * ((n : ℝ) + 1) ^ 2 := by
    intro n
    induction n with
    | zero =>
        simp
    | succ n ih =>
        calc
          F (n + 1) ≤ F n - c * (2 * (n : ℝ) + 3) := hstep n
          _ ≤ (F 0 + c - c * ((n : ℝ) + 1) ^ 2) -
              c * (2 * (n : ℝ) + 3) := sub_le_sub_right ih _
          _ = F 0 + c - c * (((n + 1 : ℕ) : ℝ) + 1) ^ 2 := by
                push_cast
                ring
  obtain ⟨n₀, hchoose⟩ := exists_nat_gt (2 * (F 0 + c) / c)
  refine ⟨n₀, ?_⟩
  intro n hn
  have hnreal : (n₀ : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hchoice : 2 * (F 0 + c) < c * (n₀ : ℝ) := by
    have h := (div_lt_iff₀ hc).mp hchoose
    nlinarith
  have hnnonneg : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hsquare : (n : ℝ) ≤ ((n : ℝ) + 1) ^ 2 := by
    nlinarith [sq_nonneg (n : ℝ)]
  have hmono : c * (n₀ : ℝ) ≤ c * (n : ℝ) :=
    mul_le_mul_of_nonneg_left hnreal hc.le
  have hpower : c * (n : ℝ) ≤ c * ((n : ℝ) + 1) ^ 2 :=
    mul_le_mul_of_nonneg_left hsquare hc.le
  have hinitial : F 0 + c ≤ (c / 2) * ((n : ℝ) + 1) ^ 2 := by
    nlinarith
  have hbound := hglobal n
  nlinarith

/-- Exact affine-family indexing constant, not an asymptotic approximation. -/
theorem affine_K (k n : ℕ) :
    (((affineFamily k n).K : ℕ) : ℝ) = 30 * ((n : ℝ) + 1) := by
  simp [affineFamily, Nat.cast_mul, Nat.cast_add]

/-- ONE conditional increment estimate implies the original strong
normalized quadratic decay required by the integer-polynomial argument.
The increment bound itself is the outstanding analytic premise. -/
theorem normalizedQuadraticDecay_of_adjacent_energy_drift
    (k : ℕ) (hk : 0 < k) (c : ℝ) (hc : 0 < c)
    (hstep : ∀ n : ℕ,
      affineEnergy k (n + 1) ≤ affineEnergy k n -
        c * (2 * (n : ℝ) + 3)) :
    NormalizedQuadraticDecay (affineFamily k) := by
  obtain ⟨n₀, hbound⟩ :=
    eventual_quadratic_bound_of_adjacent_drift (affineEnergy k) c hc hstep
  apply (normalizedQuadraticDecay_iff_content_gram_quadratic
    (affineFamily k) (fun n => affineFamily_admissible k hk n)).mpr
  refine ⟨c / 1800, by positivity, n₀, ?_⟩
  intro n hn
  calc
    contentLog (affineFamily k n) + gramLog (affineFamily k n) =
        affineEnergy k n := rfl
    _ ≤ -(c / 2) * ((n : ℝ) + 1) ^ 2 := hbound n hn
    _ = -(c / 1800) * (((affineFamily k n).K : ℝ) ^ 2) := by
      rw [affine_K]
      ring

/-- Two *adjacent*, rather than absolute K^2, finite-data log estimates
with a strictly negative combined slope imply the original decay premise.
Neither of these adjacent estimates is proved by this theorem. -/
theorem normalizedQuadraticDecay_of_two_adjacent_log_rates
    (k : ℕ) (hk : 0 < k) (A B : ℝ) (hAB : A + B < 0)
    (hcontent : ∀ n : ℕ,
      contentLog (affineFamily k (n + 1)) -
        contentLog (affineFamily k n) ≤ A * (2 * (n : ℝ) + 3))
    (hgram : ∀ n : ℕ,
      gramLog (affineFamily k (n + 1)) -
        gramLog (affineFamily k n) ≤ B * (2 * (n : ℝ) + 3)) :
    NormalizedQuadraticDecay (affineFamily k) := by
  apply normalizedQuadraticDecay_of_adjacent_energy_drift
    k hk (-(A + B)) (neg_pos.mpr hAB)
  intro n
  have h := add_le_add (hcontent n) (hgram n)
  dsimp [affineEnergy]
  nlinarith

/-- Direct adjacent RATIO criterion for the actual positive primitive value.
Unlike a hypothetical zero-free polynomial, each primitive is constructed.
A uniform strict ratio contraction remains an explicit OPEN input. -/
theorem normalizedQuadraticDecay_of_adjacent_primitive_ratio
    (k : ℕ) (hk : 0 < k) (c : ℝ) (hc : 0 < c)
    (hratio : ∀ n : ℕ,
      primitiveValue k (n + 1) ≤
        _root_.Real.exp (-c * (2 * (n : ℝ) + 3)) * primitiveValue k n) :
    NormalizedQuadraticDecay (affineFamily k) := by
  apply normalizedQuadraticDecay_of_adjacent_energy_drift k hk c hc
  intro n
  have hlog := _root_.Real.log_le_log (primitiveValue_pos k (n + 1) hk)
    (hratio n)
  rw [_root_.Real.log_mul (_root_.Real.exp_pos _).ne'
    (primitiveValue_pos k n hk).ne', _root_.Real.log_exp] at hlog
  rw [log_primitiveValue_eq_affineEnergy k (n + 1) hk,
    log_primitiveValue_eq_affineEnergy k n hk] at hlog
  linarith

end ManuscriptChain.AdjacentLogIncrement
