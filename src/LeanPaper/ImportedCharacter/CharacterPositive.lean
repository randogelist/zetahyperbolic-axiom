import LeanPaper.ImportedCharacter.ShiftedPole
import Mathlib.Tactic

/-!
# Theorem 3.9 / Section 6.4 -- character numerator positivity

The five explicit real-character numerator polynomials displayed in the
manuscript on page 13 have positive values on 0 < z < 1.

The statements here are **unconditional** polynomial inequalities.  No
assumption about a Dirichlet L-value or unformalized Mellin integral enters.
The infinite geometric-series identity connecting the positive numerators
to the Dirichlet weights is a *different* analytic theorem and is not
asserted here.

The final lemma isolates the exact algebraic character--Vandermonde sign
cancellation, but does not claim that a not-yet-constructed beta integral
has been evaluated.
-/

noncomputable section
namespace PaperAdvances.Theorem3_9_CharacterPositive

/-- The conductor-three odd character numerator. -/
def f3 (z : ℝ) : ℝ := z - z ^ 2
/-- The conductor-four odd character numerator. -/
def f4 (z : ℝ) : ℝ := z - z ^ 3
/-- The conductor-five quadratic character numerator. -/
def f5 (z : ℝ) : ℝ := z - z ^ 2 - z ^ 3 + z ^ 4
/-- The positive-character conductor-eight numerator. -/
def f8pos (z : ℝ) : ℝ := z - z ^ 3 - z ^ 5 + z ^ 7
/-- The negative-character conductor-eight numerator. -/
def f8neg (z : ℝ) : ℝ := z + z ^ 3 - z ^ 5 - z ^ 7

theorem f3_factor (z : ℝ) : f3 z = z * (1 - z) := by
  unfold f3
  ring

theorem f4_factor (z : ℝ) : f4 z = z * (1 - z ^ 2) := by
  unfold f4
  ring

theorem f5_factor (z : ℝ) : f5 z = z * (1 - z) ^ 2 * (1 + z) := by
  unfold f5
  ring

theorem f8pos_factor (z : ℝ) :
    f8pos z = z * (1 - z ^ 2) * (1 - z ^ 4) := by
  unfold f8pos
  ring

theorem f8neg_factor (z : ℝ) :
    f8neg z = z * (1 + z ^ 2) * (1 - z ^ 4) := by
  unfold f8neg
  ring

/-- The order-two gap remains strictly positive on the open unit interval. -/
theorem square_gap_pos (z : ℝ) (hz : 0 < z) (h1 : z < 1) :
    0 < 1 - z ^ 2 := by
  calc
    0 < (1 - z) * (1 + z) := mul_pos (sub_pos.mpr h1) (by linarith)
    _ = 1 - z ^ 2 := by ring

/-- The order-four gap remains strictly positive on the open unit interval. -/
theorem fourth_gap_pos (z : ℝ) (hz : 0 < z) (h1 : z < 1) :
    0 < 1 - z ^ 4 := by
  have hsq : 0 < 1 - z ^ 2 := square_gap_pos z hz h1
  have hs : 0 < 1 + z ^ 2 := by positivity
  calc
    0 < (1 - z ^ 2) * (1 + z ^ 2) := mul_pos hsq hs
    _ = 1 - z ^ 4 := by ring

theorem f3_pos (z : ℝ) (hz : 0 < z) (h1 : z < 1) : 0 < f3 z := by
  rw [f3_factor]
  exact mul_pos hz (sub_pos.mpr h1)

theorem f4_pos (z : ℝ) (hz : 0 < z) (h1 : z < 1) : 0 < f4 z := by
  rw [f4_factor]
  exact mul_pos hz (square_gap_pos z hz h1)

theorem f5_pos (z : ℝ) (hz : 0 < z) (h1 : z < 1) : 0 < f5 z := by
  rw [f5_factor]
  have hgap : 0 < 1 - z := sub_pos.mpr h1
  have hplus : 0 < 1 + z := by linarith
  exact mul_pos (mul_pos hz (sq_pos_of_pos hgap)) hplus

theorem f8pos_pos (z : ℝ) (hz : 0 < z) (h1 : z < 1) : 0 < f8pos z := by
  rw [f8pos_factor]
  exact mul_pos (mul_pos hz (square_gap_pos z hz h1)) (fourth_gap_pos z hz h1)

theorem f8neg_pos (z : ℝ) (hz : 0 < z) (h1 : z < 1) : 0 < f8neg z := by
  rw [f8neg_factor]
  have hplus : 0 < 1 + z ^ 2 := by positivity
  exact mul_pos (mul_pos hz hplus) (fourth_gap_pos z hz h1)

/-- All five Fekete numerators have strictly positive values simultaneously. -/
theorem all_fekete_numerators_pos (z : ℝ) (hz : 0 < z) (h1 : z < 1) :
    0 < f3 z ∧ 0 < f4 z ∧ 0 < f5 z ∧ 0 < f8pos z ∧ 0 < f8neg z := by
  exact ⟨f3_pos z hz h1, f4_pos z hz h1, f5_pos z hz h1,
    f8pos_pos z hz h1, f8neg_pos z hz h1⟩

/-- The alternating character phase cancels an alternating derivative phase. -/
theorem alternating_character_vandermonde_cancellation
    (j : ℕ) (u v : ℝ) (hu : 0 < u) (hv : 0 < v) :
    0 < (((-1 : ℝ) ^ j) * u) * (((-1 : ℝ) ^ j) * v) := by
  have hsign : ((-1 : ℝ) ^ j) * ((-1 : ℝ) ^ j) = 1 := by
    rw [← mul_pow]
    norm_num
  have heq : (((-1 : ℝ) ^ j) * u) * (((-1 : ℝ) ^ j) * v) = u * v := by
    calc
      (((-1 : ℝ) ^ j) * u) * (((-1 : ℝ) ^ j) * v) =
          (((-1 : ℝ) ^ j) * ((-1 : ℝ) ^ j)) * (u * v) := by ring
      _ = u * v := by rw [hsign, one_mul]
  rw [heq]
  exact mul_pos hu hv

/-- The geometric parameter of a real-character Dirichlet kernel. -/
def qParameter (q y : ℝ) : ℝ := Real.exp (-(2 * Real.pi * y / q))

/-- For every positive conductor and positive Laplace variable, 0 < z < 1. -/
theorem qParameter_mem_unit_interval
    (q y : ℝ) (hq : 0 < q) (hy : 0 < y) :
    0 < qParameter q y ∧ qParameter q y < 1 := by
  constructor
  · unfold qParameter
    exact Real.exp_pos _
  · unfold qParameter
    apply Real.exp_lt_one_iff.mpr
    have hnum : 0 < (2 : ℝ) * Real.pi * y := by
      exact mul_pos (mul_pos (by norm_num) Real.pi_pos) hy
    exact neg_lt_zero.mpr (div_pos hnum hq)

/-- All five character numerators are strictly positive at every positive
    Laplace parameter, without assuming any zeta/L-function identity. -/
theorem all_fekete_laplace_numerators_pos
    (q y : ℝ) (hq : 0 < q) (hy : 0 < y) :
    0 < f3 (qParameter q y) ∧
    0 < f4 (qParameter q y) ∧
    0 < f5 (qParameter q y) ∧
    0 < f8pos (qParameter q y) ∧
    0 < f8neg (qParameter q y) := by
  obtain ⟨hz, h1⟩ := qParameter_mem_unit_interval q y hq hy
  exact all_fekete_numerators_pos (qParameter q y) hz h1

/-- The denominator for a conductor-three character is positive. -/
theorem cubic_gap_pos (z : ℝ) (hz : 0 < z) (h1 : z < 1) :
    0 < 1 - z ^ 3 := by
  have hs : 0 < 1 + z + z ^ 2 := by positivity
  calc
    0 < (1 - z) * (1 + z + z ^ 2) := mul_pos (sub_pos.mpr h1) hs
    _ = 1 - z ^ 3 := by ring

/-- The denominator for a conductor-five character is positive. -/
theorem fifth_gap_pos (z : ℝ) (hz : 0 < z) (h1 : z < 1) :
    0 < 1 - z ^ 5 := by
  have hs : 0 < 1 + z + z ^ 2 + z ^ 3 + z ^ 4 := by positivity
  calc
    0 < (1 - z) * (1 + z + z ^ 2 + z ^ 3 + z ^ 4) :=
      mul_pos (sub_pos.mpr h1) hs
    _ = 1 - z ^ 5 := by ring

/-- The denominator for either conductor-eight real character is positive. -/
theorem eighth_gap_pos (z : ℝ) (hz : 0 < z) (h1 : z < 1) :
    0 < 1 - z ^ 8 := by
  have hfour : 0 < 1 - z ^ 4 := fourth_gap_pos z hz h1
  have hs : 0 < 1 + z ^ 4 := by positivity
  calc
    0 < (1 - z ^ 4) * (1 + z ^ 4) := mul_pos hfour hs
    _ = 1 - z ^ 8 := by ring

/-- The grouped rational generating kernel is strictly positive for q=3. -/
theorem rational_kernel_3_pos (z : ℝ) (hz : 0 < z) (h1 : z < 1) :
    0 < f3 z / (1 - z ^ 3) :=
  div_pos (f3_pos z hz h1) (cubic_gap_pos z hz h1)

/-- The grouped rational generating kernel is strictly positive for q=4. -/
theorem rational_kernel_4_pos (z : ℝ) (hz : 0 < z) (h1 : z < 1) :
    0 < f4 z / (1 - z ^ 4) :=
  div_pos (f4_pos z hz h1) (fourth_gap_pos z hz h1)

/-- The grouped rational generating kernel is strictly positive for q=5. -/
theorem rational_kernel_5_pos (z : ℝ) (hz : 0 < z) (h1 : z < 1) :
    0 < f5 z / (1 - z ^ 5) :=
  div_pos (f5_pos z hz h1) (fifth_gap_pos z hz h1)

/-- The grouped rational generating kernels are positive for both q=8 characters. -/
theorem rational_kernel_8_pos (z : ℝ) (hz : 0 < z) (h1 : z < 1) :
    0 < f8pos z / (1 - z ^ 8) ∧ 0 < f8neg z / (1 - z ^ 8) := by
  exact ⟨div_pos (f8pos_pos z hz h1) (eighth_gap_pos z hz h1),
    div_pos (f8neg_pos z hz h1) (eighth_gap_pos z hz h1)⟩

/-- All character quotients in the paper's Theorem 3.9 are positive. -/
theorem all_rational_character_kernels_pos
    (z : ℝ) (hz : 0 < z) (h1 : z < 1) :
    0 < f3 z / (1 - z ^ 3) ∧
    0 < f4 z / (1 - z ^ 4) ∧
    0 < f5 z / (1 - z ^ 5) ∧
    0 < f8pos z / (1 - z ^ 8) ∧
    0 < f8neg z / (1 - z ^ 8) := by
  obtain ⟨hp, hm⟩ := rational_kernel_8_pos z hz h1
  exact ⟨rational_kernel_3_pos z hz h1,
    rational_kernel_4_pos z hz h1,
    rational_kernel_5_pos z hz h1, hp, hm⟩

end PaperAdvances.Theorem3_9_CharacterPositive

#print axioms PaperAdvances.Theorem3_9_CharacterPositive.all_fekete_numerators_pos
#print axioms PaperAdvances.Theorem3_9_CharacterPositive.alternating_character_vandermonde_cancellation

#print axioms PaperAdvances.Theorem3_9_CharacterPositive.all_fekete_laplace_numerators_pos

#print axioms PaperAdvances.Theorem3_9_CharacterPositive.all_rational_character_kernels_pos
