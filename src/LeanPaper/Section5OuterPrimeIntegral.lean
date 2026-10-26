import Mathlib

/-!
# The actual outer prime-sum integral in Theorem 5.6(1)

The floor-defined integrand is used literally, including its exceptional
endpoint values. The eleven affine identities are proved on open intervals;
Lebesgue integration ignores their finitely many boundary points. Thus the
integral does not require the false printed endpoint-continuity assertion.
This file makes no claim about the separate inner-tail or residue-gain parts.
-/

noncomputable section
open MeasureTheory Set
open scoped BigOperators Topology

namespace LeanPaper.Section5OuterPrimeIntegral

def alpha : ℝ := 3/40
def lambda : ℝ := 37/40

def v (y : ℝ) : ℝ := 1-y*(⌊1/y⌋ : ℝ)
def u (y : ℝ) : ℝ := max 0 (alpha+v y-y)
def t (y : ℝ) : ℝ := min alpha (v y)+u y
def r (y : ℝ) : ℝ := max 0 (29/20-3*y)

/-- The manuscript's piecewise function, extended outside its stated interval.
Only its restriction to `[1/3,37/20]` is used. -/
def outerR (y : ℝ) : ℝ :=
  if y < 1/2 then 9*(1-y)-16*alpha-7*t y+min (r y) (y+u y)
  else if y < 1 then 9*(1-y)-8*t y+min (r y) (y-alpha+u y)
  else 0

def outerT (y : ℝ) : ℝ :=
  outerR y-2*lambda*(⌊1/y⌋ : ℝ)+
    ∑ j : Fin 7, max 0 (2*lambda-((j.val+1 : ℕ) : ℝ)*y)

private theorem floor_reciprocal_eq (n : ℤ) {y : ℝ} (hy : 0 < y)
    (hlo : (n : ℝ)*y ≤ 1) (hhi : 1 < ((n : ℝ)+1)*y) :
    ⌊1/y⌋ = n := by
  apply Int.floor_eq_iff.mpr
  constructor
  · exact (le_div_iff₀ hy).mpr hlo
  · exact (div_lt_iff₀ hy).mpr hhi

theorem outerT_piece_1 {y : ℝ} (ha : 1/3 < y) (hb : y < 43/120) :
    outerT y = 51/8+(-5)*y := by
  have hf : ⌊1/y⌋ = (2 : ℤ) :=
    floor_reciprocal_eq 2 (by linarith) (by norm_num <;> linarith) (by norm_num <;> linarith)
  have hh : y < 1/2 := by linarith
  have h1 : y < 1 := by linarith
  norm_num [outerT, outerR, alpha, lambda, v, u, t, r, hf, hh, h1,
    Fin.sum_univ_succ]
  try simp only [max_def, min_def]
  all_goals
    repeat' (split <;> try linarith)
  all_goals linarith

theorem outerT_piece_2 {y : ℝ} (ha : 43/120 < y) (hb : y < 29/80) :
    outerT y = 513/40+(-23)*y := by
  have hf : ⌊1/y⌋ = (2 : ℤ) :=
    floor_reciprocal_eq 2 (by linarith) (by norm_num <;> linarith) (by norm_num <;> linarith)
  have hh : y < 1/2 := by linarith
  have h1 : y < 1 := by linarith
  norm_num [outerT, outerR, alpha, lambda, v, u, t, r, hf, hh, h1,
    Fin.sum_univ_succ]
  try simp only [max_def, min_def]
  all_goals
    repeat' (split <;> try linarith)
  all_goals linarith

theorem outerT_piece_3 {y : ℝ} (ha : 29/80 < y) (hb : y < 37/100) :
    outerT y = 571/40+(-27)*y := by
  have hf : ⌊1/y⌋ = (2 : ℤ) :=
    floor_reciprocal_eq 2 (by linarith) (by norm_num <;> linarith) (by norm_num <;> linarith)
  have hh : y < 1/2 := by linarith
  have h1 : y < 1 := by linarith
  norm_num [outerT, outerR, alpha, lambda, v, u, t, r, hf, hh, h1,
    Fin.sum_univ_succ]
  try simp only [max_def, min_def]
  all_goals
    repeat' (split <;> try linarith)
  all_goals linarith

theorem outerT_piece_4 {y : ℝ} (ha : 37/100 < y) (hb : y < 37/80) :
    outerT y = 497/40+(-22)*y := by
  have hf : ⌊1/y⌋ = (2 : ℤ) :=
    floor_reciprocal_eq 2 (by linarith) (by norm_num <;> linarith) (by norm_num <;> linarith)
  have hh : y < 1/2 := by linarith
  have h1 : y < 1 := by linarith
  norm_num [outerT, outerR, alpha, lambda, v, u, t, r, hf, hh, h1,
    Fin.sum_univ_succ]
  try simp only [max_def, min_def]
  all_goals
    repeat' (split <;> try linarith)
  all_goals linarith

theorem outerT_piece_5 {y : ℝ} (ha : 37/80 < y) (hb : y < 29/60) :
    outerT y = 41/10+(-4)*y := by
  have hf : ⌊1/y⌋ = (2 : ℤ) :=
    floor_reciprocal_eq 2 (by linarith) (by norm_num <;> linarith) (by norm_num <;> linarith)
  have hh : y < 1/2 := by linarith
  have h1 : y < 1 := by linarith
  norm_num [outerT, outerR, alpha, lambda, v, u, t, r, hf, hh, h1,
    Fin.sum_univ_succ]
  try simp only [max_def, min_def]
  all_goals
    repeat' (split <;> try linarith)
  all_goals linarith

theorem outerT_piece_6 {y : ℝ} (ha : 29/60 < y) (hb : y < 1/2) :
    outerT y = 53/20+(-1)*y := by
  have hf : ⌊1/y⌋ = (2 : ℤ) :=
    floor_reciprocal_eq 2 (by linarith) (by norm_num <;> linarith) (by norm_num <;> linarith)
  have hh : y < 1/2 := by linarith
  have h1 : y < 1 := by linarith
  norm_num [outerT, outerR, alpha, lambda, v, u, t, r, hf, hh, h1,
    Fin.sum_univ_succ]
  try simp only [max_def, min_def]
  all_goals
    repeat' (split <;> try linarith)
  all_goals linarith

theorem outerT_piece_7 {y : ℝ} (ha : 1/2 < y) (hb : y < 43/80) :
    outerT y = 7/2+(1)*y := by
  have hf : ⌊1/y⌋ = (1 : ℤ) :=
    floor_reciprocal_eq 1 (by linarith) (by norm_num <;> linarith) (by norm_num <;> linarith)
  have hh : ¬y < 1/2 := by linarith
  have h1 : y < 1 := by linarith
  norm_num [outerT, outerR, alpha, lambda, v, u, t, r, hf, hh, h1,
    Fin.sum_univ_succ]
  try simp only [max_def, min_def]
  all_goals
    repeat' (split <;> try linarith)
  all_goals linarith

theorem outerT_piece_8 {y : ℝ} (ha : 43/80 < y) (hb : y < 37/60) :
    outerT y = 121/10+(-15)*y := by
  have hf : ⌊1/y⌋ = (1 : ℤ) :=
    floor_reciprocal_eq 1 (by linarith) (by norm_num <;> linarith) (by norm_num <;> linarith)
  have hh : ¬y < 1/2 := by linarith
  have h1 : y < 1 := by linarith
  norm_num [outerT, outerR, alpha, lambda, v, u, t, r, hf, hh, h1,
    Fin.sum_univ_succ]
  try simp only [max_def, min_def]
  all_goals
    repeat' (split <;> try linarith)
  all_goals linarith

theorem outerT_piece_9 {y : ℝ} (ha : 37/60 < y) (hb : y < 37/40) :
    outerT y = 41/4+(-12)*y := by
  have hf : ⌊1/y⌋ = (1 : ℤ) :=
    floor_reciprocal_eq 1 (by linarith) (by norm_num <;> linarith) (by norm_num <;> linarith)
  have hh : ¬y < 1/2 := by linarith
  have h1 : y < 1 := by linarith
  norm_num [outerT, outerR, alpha, lambda, v, u, t, r, hf, hh, h1,
    Fin.sum_univ_succ]
  try simp only [max_def, min_def]
  all_goals
    repeat' (split <;> try linarith)
  all_goals linarith

theorem outerT_piece_10 {y : ℝ} (ha : 37/40 < y) (hb : y < 1) :
    outerT y = 1+(-2)*y := by
  have hf : ⌊1/y⌋ = (1 : ℤ) :=
    floor_reciprocal_eq 1 (by linarith) (by norm_num <;> linarith) (by norm_num <;> linarith)
  have hh : ¬y < 1/2 := by linarith
  have h1 : y < 1 := by linarith
  norm_num [outerT, outerR, alpha, lambda, v, u, t, r, hf, hh, h1,
    Fin.sum_univ_succ]
  try simp only [max_def, min_def]
  all_goals
    repeat' (split <;> try linarith)
  all_goals linarith

theorem outerT_piece_11 {y : ℝ} (ha : 1 < y) (hb : y < 37/20) :
    outerT y = 37/20+(-1)*y := by
  have hf : ⌊1/y⌋ = (0 : ℤ) :=
    floor_reciprocal_eq 0 (by linarith) (by norm_num <;> linarith) (by norm_num <;> linarith)
  have hh : ¬y < 1/2 := by linarith
  have h1 : ¬y < 1 := by linarith
  norm_num [outerT, outerR, alpha, lambda, v, u, t, r, hf, hh, h1,
    Fin.sum_univ_succ]
  try simp only [max_def, min_def]
  all_goals
    repeat' (split <;> try linarith)
  all_goals linarith

/-- Open-interval equality is enough for both integrability and evaluation. -/
private theorem integral_of_affine_piece {a b B C : ℝ} (hab : a ≤ b)
    (hp : ∀ y ∈ Ioo a b, outerT y = B+C*y) :
    IntervalIntegrable outerT volume a b ∧
    (∫ y in a..b, outerT y) = B*(b-a)+C*(b^2-a^2)/2 := by
  have he : EqOn outerT (fun y => B+C*y) (uIoo a b) := by
    intro y hy
    exact hp y (by simpa only [uIoo_of_le hab] using hy)
  have hB : IntervalIntegrable (fun _ : ℝ => B) volume a b :=
    continuous_const.intervalIntegrable a b
  have hCy : IntervalIntegrable (fun y : ℝ => C*y) volume a b :=
    (continuous_const.mul continuous_id).intervalIntegrable a b
  have hi : IntervalIntegrable (fun y => B+C*y) volume a b :=
    hB.add hCy
  refine ⟨(intervalIntegrable_congr_uIoo he).mpr hi, ?_⟩
  rw [intervalIntegral.integral_congr_uIoo he,
    intervalIntegral.integral_add hB hCy,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const,
    intervalIntegral.integral_id]
  simp only [smul_eq_mul]
  ring

theorem outerT_integral_1 :
    IntervalIntegrable outerT volume (1/3) (43/120) ∧
    (∫ y in (1/3)..(43/120), outerT y) = (223/1920 : ℝ) := by
  have h := integral_of_affine_piece (a := 1/3) (b := 43/120)
    (B := 51/8) (C := -5) (by norm_num)
    (fun y hy => outerT_piece_1 hy.1 hy.2)
  norm_num at h ⊢
  exact h

theorem outerT_integral_2 :
    IntervalIntegrable outerT volume (43/120) (29/80) ∧
    (∫ y in (43/120)..(29/80), outerT y) = (2177/115200 : ℝ) := by
  have h := integral_of_affine_piece (a := 43/120) (b := 29/80)
    (B := 513/40) (C := -23) (by norm_num)
    (fun y hy => outerT_piece_2 hy.1 hy.2)
  norm_num at h ⊢
  exact h

theorem outerT_integral_3 :
    IntervalIntegrable outerT volume (29/80) (37/100) ∧
    (∫ y in (29/80)..(37/100), outerT y) = (10527/320000 : ℝ) := by
  have h := integral_of_affine_piece (a := 29/80) (b := 37/100)
    (B := 571/40) (C := -27) (by norm_num)
    (fun y hy => outerT_piece_3 hy.1 hy.2)
  norm_num at h ⊢
  exact h

theorem outerT_integral_4 :
    IntervalIntegrable outerT volume (37/100) (37/80) ∧
    (∫ y in (37/100)..(37/80), outerT y) = (48359/160000 : ℝ) := by
  have h := integral_of_affine_piece (a := 37/100) (b := 37/80)
    (B := 497/40) (C := -22) (by norm_num)
    (fun y hy => outerT_piece_4 hy.1 hy.2)
  norm_num at h ⊢
  exact h

theorem outerT_integral_5 :
    IntervalIntegrable outerT volume (37/80) (29/60) ∧
    (∫ y in (37/80)..(29/60), outerT y) = (53/1152 : ℝ) := by
  have h := integral_of_affine_piece (a := 37/80) (b := 29/60)
    (B := 41/10) (C := -4) (by norm_num)
    (fun y hy => outerT_piece_5 hy.1 hy.2)
  norm_num at h ⊢
  exact h

theorem outerT_integral_6 :
    IntervalIntegrable outerT volume (29/60) (1/2) ∧
    (∫ y in (29/60)..(1/2), outerT y) = (259/7200 : ℝ) := by
  have h := integral_of_affine_piece (a := 29/60) (b := 1/2)
    (B := 53/20) (C := -1) (by norm_num)
    (fun y hy => outerT_piece_6 hy.1 hy.2)
  norm_num at h ⊢
  exact h

theorem outerT_integral_7 :
    IntervalIntegrable outerT volume (1/2) (43/80) ∧
    (∫ y in (1/2)..(43/80), outerT y) = (1929/12800 : ℝ) := by
  have h := integral_of_affine_piece (a := 1/2) (b := 43/80)
    (B := 7/2) (C := 1) (by norm_num)
    (fun y hy => outerT_piece_7 hy.1 hy.2)
  norm_num at h ⊢
  exact h

theorem outerT_integral_8 :
    IntervalIntegrable outerT volume (43/80) (37/60) ∧
    (∫ y in (43/80)..(37/60), outerT y) = (10469/38400 : ℝ) := by
  have h := integral_of_affine_piece (a := 43/80) (b := 37/60)
    (B := 121/10) (C := -15) (by norm_num)
    (fun y hy => outerT_piece_8 hy.1 hy.2)
  norm_num at h ⊢
  exact h

theorem outerT_integral_9 :
    IntervalIntegrable outerT volume (37/60) (37/40) ∧
    (∫ y in (37/60)..(37/40), outerT y) = (37/120 : ℝ) := by
  have h := integral_of_affine_piece (a := 37/60) (b := 37/40)
    (B := 41/4) (C := -12) (by norm_num)
    (fun y hy => outerT_piece_9 hy.1 hy.2)
  norm_num at h ⊢
  exact h

theorem outerT_integral_10 :
    IntervalIntegrable outerT volume (37/40) (1) ∧
    (∫ y in (37/40)..(1), outerT y) = (-111/1600 : ℝ) := by
  have h := integral_of_affine_piece (a := 37/40) (b := 1)
    (B := 1) (C := -2) (by norm_num)
    (fun y hy => outerT_piece_10 hy.1 hy.2)
  norm_num at h ⊢
  exact h

theorem outerT_integral_11 :
    IntervalIntegrable outerT volume (1) (37/20) ∧
    (∫ y in (1)..(37/20), outerT y) = (289/800 : ℝ) := by
  have h := integral_of_affine_piece (a := 1) (b := 37/20)
    (B := 37/20) (C := -1) (by norm_num)
    (fun y hy => outerT_piece_11 hy.1 hy.2)
  norm_num at h ⊢
  exact h

/-- Exact integral of the actual floor function in Theorem 5.6(1). -/
theorem theorem_5_6_outer_integral :
    IntervalIntegrable outerT volume (1/3) (37/20) ∧
    (∫ y in (1/3)..(37/20), outerT y) = (453803/288000 : ℝ) := by
  obtain ⟨h1, e1⟩ := outerT_integral_1
  obtain ⟨h2, e2⟩ := outerT_integral_2
  obtain ⟨h3, e3⟩ := outerT_integral_3
  obtain ⟨h4, e4⟩ := outerT_integral_4
  obtain ⟨h5, e5⟩ := outerT_integral_5
  obtain ⟨h6, e6⟩ := outerT_integral_6
  obtain ⟨h7, e7⟩ := outerT_integral_7
  obtain ⟨h8, e8⟩ := outerT_integral_8
  obtain ⟨h9, e9⟩ := outerT_integral_9
  obtain ⟨h10, e10⟩ := outerT_integral_10
  obtain ⟨h11, e11⟩ := outerT_integral_11
  have hi := (((((((((h1.trans h2).trans h3).trans h4).trans h5).trans h6).trans h7).trans h8).trans h9).trans h10).trans h11
  refine ⟨hi, ?_⟩
  have eadd2 := intervalIntegral.integral_add_adjacent_intervals h1 h2
  have eadd3 := intervalIntegral.integral_add_adjacent_intervals (h1.trans h2) h3
  have eadd4 := intervalIntegral.integral_add_adjacent_intervals ((h1.trans h2).trans h3) h4
  have eadd5 := intervalIntegral.integral_add_adjacent_intervals (((h1.trans h2).trans h3).trans h4) h5
  have eadd6 := intervalIntegral.integral_add_adjacent_intervals ((((h1.trans h2).trans h3).trans h4).trans h5) h6
  have eadd7 := intervalIntegral.integral_add_adjacent_intervals (((((h1.trans h2).trans h3).trans h4).trans h5).trans h6) h7
  have eadd8 := intervalIntegral.integral_add_adjacent_intervals ((((((h1.trans h2).trans h3).trans h4).trans h5).trans h6).trans h7) h8
  have eadd9 := intervalIntegral.integral_add_adjacent_intervals (((((((h1.trans h2).trans h3).trans h4).trans h5).trans h6).trans h7).trans h8) h9
  have eadd10 := intervalIntegral.integral_add_adjacent_intervals ((((((((h1.trans h2).trans h3).trans h4).trans h5).trans h6).trans h7).trans h8).trans h9) h10
  have eadd11 := intervalIntegral.integral_add_adjacent_intervals (((((((((h1.trans h2).trans h3).trans h4).trans h5).trans h6).trans h7).trans h8).trans h9).trans h10) h11
  linarith

/-- The three printed table endpoint entries are right-hand affine limits,
not the actual values of the floor-defined function. -/
theorem outerT_endpoint_values :
    outerT (1/3) = (23/6 : ℝ) ∧
    outerT (1/2) = (67/20 : ℝ) ∧
    outerT 1 = (-1 : ℝ) := by
  norm_num [outerT, outerR, alpha, lambda, v, u, t, r, Fin.sum_univ_succ]

private theorem not_continuousOn_of_boundary_mismatch {a b B C : ℝ}
    (hab : a < b) (hp : ∀ y ∈ Ioo a b, outerT y = B+C*y)
    (hne : outerT a ≠ B+C*a) : ¬ContinuousOn outerT (Ico a b) := by
  intro hc
  have hright : Filter.Tendsto outerT (𝓝[>] a) (𝓝 (B+C*a)) := by
    have hlin : Filter.Tendsto (fun y : ℝ => B+C*y) (𝓝 a) (𝓝 (B+C*a)) :=
      (continuous_const.add (continuous_const.mul continuous_id) :
        Continuous (fun y : ℝ => B+C*y)).continuousAt.tendsto
    apply (hlin.mono_left inf_le_left).congr'
    filter_upwards [Ioo_mem_nhdsGT hab] with y hy
    exact (hp y hy).symm
  have hcont : Filter.Tendsto outerT (𝓝[>] a) (𝓝 (outerT a)) :=
    (hc a ⟨le_rfl, hab⟩).mono_of_mem_nhdsWithin
      (Filter.mem_of_superset (Ioo_mem_nhdsGT hab) (fun _ hy => ⟨hy.1.le, hy.2⟩))
  exact hne (tendsto_nhds_unique hcont hright)

/-- The literal first printed continuity clause is false at 1/3. -/
theorem not_continuousOn_first_printed_interval :
    ¬ContinuousOn outerT (Ico (1/3) (1/2)) := by
  intro hc
  apply not_continuousOn_of_boundary_mismatch
    (a := 1/3) (b := 43/120) (B := 51/8) (C := -5)
    (by norm_num) (fun y hy => outerT_piece_1 hy.1 hy.2)
  · rw [outerT_endpoint_values.1]
    norm_num
  · exact hc.mono (fun y hy => ⟨hy.1, by linarith [hy.2]⟩)

/-- The literal second printed continuity clause is false at 1/2. -/
theorem not_continuousOn_second_printed_interval :
    ¬ContinuousOn outerT (Ico (1/2) 1) := by
  intro hc
  apply not_continuousOn_of_boundary_mismatch
    (a := 1/2) (b := 43/80) (B := 7/2) (C := 1)
    (by norm_num) (fun y hy => outerT_piece_7 hy.1 hy.2)
  · rw [outerT_endpoint_values.2.1]
    norm_num
  · exact hc.mono (fun y hy => ⟨hy.1, by linarith [hy.2]⟩)

end LeanPaper.Section5OuterPrimeIntegral

#print axioms LeanPaper.Section5OuterPrimeIntegral.theorem_5_6_outer_integral
#print axioms LeanPaper.Section5OuterPrimeIntegral.outerT_endpoint_values
#print axioms LeanPaper.Section5OuterPrimeIntegral.not_continuousOn_first_printed_interval
#print axioms LeanPaper.Section5OuterPrimeIntegral.not_continuousOn_second_printed_interval
