import USPDCore

/-!
# MO271 weight-five seed to weight-seven jumper

A-Tier candidate only. This branch file has not yet received a matching native
Lean 4.33.0 compile and theorem-level axiom audit.
-/

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 4096

open Polynomial

namespace ZetaBetaHankel.MO271Jumper57

open ZetaBetaHankel.USPD

def ray5 : Ray := pureHigherRay 1 (by omega)
def ray7 : Ray := pureHigherRay 2 (by omega)
def baseScale (n : ℕ) : ℕ := 40 * (n + 1)

def DegreeAtBase (ray : Ray) : Prop :=
  ∀ n : ℕ, (canonicalPolynomial ray n).natDegree + 1 ≤ baseScale n

def SubquadraticTransfer57 : Prop :=
  ∀ η : ℝ, 0 < η →
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      0 < |evaluatedValue ray7 n| ∧
      |evaluatedValue ray7 n| ≤
        Real.exp (η * ((baseScale n : ℝ) ^ 2)) *
          |evaluatedValue ray5 n|

structure MO271Seed5 : Prop where
  degree_at_base : DegreeAtBase ray5
  decay : DecaysAt ray5

structure Transfer57 : Prop where
  degree_at_base : DegreeAtBase ray7
  subquadratic : SubquadraticTransfer57

theorem cutoffScale_eq_base (ray : Ray) (hdeg : DegreeAtBase ray) (n : ℕ) :
    cutoffScale ray n = baseScale n := by
  unfold cutoffScale
  apply max_eq_left
  exact hdeg n

theorem decay7_of_mo271_seed_and_transfer
    (h5 : MO271Seed5) (h57 : Transfer57) :
    DecaysAt ray7 := by
  obtain ⟨ε, hε, n5, h5decay⟩ := h5.decay
  have hη : 0 < ε / 2 := half_pos hε
  obtain ⟨n57, htransfer⟩ := h57.subquadratic (ε / 2) hη
  refine ⟨ε / 2, hη, max n5 n57, ?_⟩
  intro n hn
  have hn5 : n5 ≤ n := le_trans (le_max_left n5 n57) hn
  have hn57 : n57 ≤ n := le_trans (le_max_right n5 n57) hn
  have h5n := h5decay n hn5
  have h57n := htransfer n hn57
  have hs5 : cutoffScale ray5 n = baseScale n :=
    cutoffScale_eq_base ray5 h5.degree_at_base n
  have hs7 : cutoffScale ray7 n = baseScale n :=
    cutoffScale_eq_base ray7 h57.degree_at_base n
  constructor
  · exact h57n.1
  · rw [hs7]
    calc
      |evaluatedValue ray7 n| ≤
          Real.exp ((ε / 2) * ((baseScale n : ℝ) ^ 2)) *
            |evaluatedValue ray5 n| := h57n.2
      _ ≤ Real.exp ((ε / 2) * ((baseScale n : ℝ) ^ 2)) *
            Real.exp (-ε * ((cutoffScale ray5 n : ℝ) ^ 2)) :=
          mul_le_mul_of_nonneg_left h5n.2 (Real.exp_pos _).le
      _ = Real.exp (-(ε / 2) * ((baseScale n : ℝ) ^ 2)) := by
          rw [hs5, ← Real.exp_add]
          congr 1
          ring

theorem irrational_actualValue_ray7
    (h5 : MO271Seed5) (h57 : Transfer57) :
    Irrational (actualValue ray7) :=
  irrational_of_decay ray7 (decay7_of_mo271_seed_and_transfer h5 h57)

@[simp] theorem actualValue_ray5_eq :
    actualValue ray5 = ZetaBetaHankel.Repaired.riemannZetaReal 5 := by
  simp [ray5, actualValue, pureHigherRay,
    ZetaBetaHankel.Repaired.xiCoupled]

@[simp] theorem actualValue_ray7_eq :
    actualValue ray7 = ZetaBetaHankel.Repaired.riemannZetaReal 7 := by
  simp [ray7, actualValue, pureHigherRay,
    ZetaBetaHankel.Repaired.xiCoupled]

theorem irrational_zeta5_of_mo271_seed (h5 : MO271Seed5) :
    Irrational (ZetaBetaHankel.Repaired.riemannZetaReal 5) := by
  rw [← actualValue_ray5_eq]
  exact irrational_of_decay ray5 h5.decay

theorem irrational_zeta7_of_mo271_jumper
    (h5 : MO271Seed5) (h57 : Transfer57) :
    Irrational (ZetaBetaHankel.Repaired.riemannZetaReal 7) := by
  rw [← actualValue_ray7_eq]
  exact irrational_actualValue_ray7 h5 h57

theorem irrational_zeta5_and_zeta7_of_mo271_jumper
    (h5 : MO271Seed5) (h57 : Transfer57) :
    Irrational (ZetaBetaHankel.Repaired.riemannZetaReal 5) ∧
    Irrational (ZetaBetaHankel.Repaired.riemannZetaReal 7) :=
  ⟨irrational_zeta5_of_mo271_seed h5,
    irrational_zeta7_of_mo271_jumper h5 h57⟩

end ZetaBetaHankel.MO271Jumper57
