import Theorem_2_5_Lagrange_Pole_Diagonalization
import Theorem_3_1_Universal_Hyperbolicity_And_Zero_Free_Disk
import Mathlib.Tactic

/-!
# Proposition 3.2: real-exponent finite spectral algebra

This is an unconditional **finite-algebra component** of Proposition 3.2,
not a proof of its analytic integral identity.  The exponent s is any real
number.  The slope weights agree with the manuscript's odd-weight weights
when s = 2*k+1 and are nonzero for every real s.

The positive-definite base of the paper's *continuous integral pencil* is
NOT constructed here.  The last two theorems universally quantify over a
positive-definite base and therefore do not assert that the unconstructed
paper integral has been evaluated or is integrable.
-/

noncomputable section
open scoped BigOperators
open Matrix

namespace PaperAdvances.Proposition3_2

open ManuscriptChain

private def node (p : ManuscriptChain.Real.Parameters) (a : Fin p.h) : ℝ :=
  (PoleDiagonalization.poleIndex p a : ℝ)

private theorem node_pos (p : ManuscriptChain.Real.Parameters) (a : Fin p.h) :
    0 < node p a := by
  change (0 : ℝ) < (PoleDiagonalization.poleIndex p a : ℝ)
  exact_mod_cast (PoleDiagonalization.poleIndex_pos p a)

/-- Strictly positive multiplier changing the pole exponent 2*k to real s-1. -/
def exponentScale (p : ManuscriptChain.Real.Parameters) (s : ℝ) (a : Fin p.h) : ℝ :=
  (node p a) ^ (s - 1) / (node p a) ^ (2 * p.k)

theorem exponentScale_pos (p : ManuscriptChain.Real.Parameters) (s : ℝ) (a : Fin p.h) :
    0 < exponentScale p s a := by
  unfold exponentScale
  have ha := node_pos p a
  positivity

/-- The gamma coefficient from equation (2.11), extended to real s. -/
def gamma (p : ManuscriptChain.Real.Parameters) (s : ℝ) (a : Fin p.h) : ℝ :=
  (PoleDiagonalization.poleWeight p a : ℝ) * exponentScale p s a

theorem gamma_ne_zero (p : ManuscriptChain.Real.Parameters) (s : ℝ) (a : Fin p.h) :
    gamma p s a ≠ 0 := by
  unfold gamma
  apply mul_ne_zero
  · exact_mod_cast PoleDiagonalization.poleWeight_ne_zero p a
  · exact ne_of_gt (exponentScale_pos p s a)

theorem gamma_pos_iff (p : ManuscriptChain.Real.Parameters) (s : ℝ) (a : Fin p.h) :
    0 < gamma p s a ↔ 0 < (PoleDiagonalization.poleWeight p a : ℝ) := by
  unfold gamma
  have ht := exponentScale_pos p s a
  constructor
  · intro h
    by_contra hn
    have hw : (PoleDiagonalization.poleWeight p a : ℝ) ≤ 0 := le_of_not_gt hn
    exact (not_lt_of_ge (mul_nonpos_of_nonpos_of_nonneg hw ht.le)) h
  · intro hw
    exact mul_pos hw ht

theorem gamma_neg_iff (p : ManuscriptChain.Real.Parameters) (s : ℝ) (a : Fin p.h) :
    gamma p s a < 0 ↔ (PoleDiagonalization.poleWeight p a : ℝ) < 0 := by
  unfold gamma
  have ht := exponentScale_pos p s a
  constructor
  · intro h
    by_contra hn
    have hw : (0 : ℝ) ≤ (PoleDiagonalization.poleWeight p a : ℝ) := le_of_not_gt hn
    exact (not_lt_of_ge (mul_nonneg hw ht.le)) h
  · intro hw
    exact mul_neg_of_neg_of_pos hw ht

/-- The original odd-weight slope is exactly recovered at s=2*k+1. -/
theorem exponentScale_odd (p : ManuscriptChain.Real.Parameters) (a : Fin p.h) :
    exponentScale p (p.weight : ℝ) a = 1 := by
  have ha : node p a ≠ 0 := ne_of_gt (node_pos p a)
  have hexp : ((p.weight : ℕ) : ℝ) - 1 = ((2 * p.k : ℕ) : ℝ) := by
    simp only [ManuscriptChain.Real.Parameters.weight, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
    ring
  unfold exponentScale
  rw [hexp, Real.rpow_natCast]
  exact div_self (pow_ne_zero _ ha)

@[simp] theorem gamma_odd (p : ManuscriptChain.Real.Parameters) (a : Fin p.h) :
    gamma p (p.weight : ℝ) a = (PoleDiagonalization.poleWeight p a : ℝ) := by
  simp [gamma, exponentScale_odd]

/-- The exact Vandermonde formula of equation (3.2) at real pole exponent s. -/
def vandermonde (p : ManuscriptChain.Real.Parameters) : Matrix (Fin p.h) (Fin p.h) ℝ :=
  (PoleDiagonalization.poleVandermonde p).map (Rat.castHom ℝ)

def slope (p : ManuscriptChain.Real.Parameters) (s : ℝ) : Matrix (Fin p.h) (Fin p.h) ℝ :=
  vandermonde p * Matrix.diagonal (gamma p s) * (vandermonde p).transpose

theorem vandermonde_det_ne_zero (p : ManuscriptChain.Real.Parameters) :
    (vandermonde p).det ≠ 0 := by
  have h : ((PoleDiagonalization.poleVandermonde p).det : ℝ) ≠ 0 := by
    exact_mod_cast (PoleDiagonalization.poleVandermonde_det_ne_zero p)
  rw [Rat.cast_det] at h
  exact h

theorem slope_det_formula (p : ManuscriptChain.Real.Parameters) (s : ℝ) :
    (slope p s).det = (vandermonde p).det ^ 2 * ∏ a : Fin p.h, gamma p s a := by
  unfold slope
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, Matrix.det_diagonal]
  ring

theorem slope_det_ne_zero (p : ManuscriptChain.Real.Parameters) (s : ℝ) :
    (slope p s).det ≠ 0 := by
  rw [slope_det_formula]
  apply mul_ne_zero
  · exact pow_ne_zero _ (vandermonde_det_ne_zero p)
  · exact Finset.prod_ne_zero_iff.mpr (fun a _ => gamma_ne_zero p s a)

theorem slope_entry (p : ManuscriptChain.Real.Parameters) (s : ℝ) (i j : Fin p.h) :
    slope p s i j =
      ∑ a : Fin p.h, vandermonde p i a * gamma p s a * vandermonde p j a := by
  unfold slope
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply]

theorem slope_isSymm (p : ManuscriptChain.Real.Parameters) (s : ℝ) : (slope p s).IsSymm := by
  ext i j
  simp only [Matrix.transpose_apply, slope_entry]
  apply Finset.sum_congr rfl
  intro a _
  ring

/-- Generic continuous-exponent symmetric pencil, with the exact pole slope. -/
def pencil (p : ManuscriptChain.Real.Parameters) (s center : ℝ)
    (A : Matrix (Fin p.h) (Fin p.h) ℝ) (hA : A.IsSymm) :
    Spectral.SymmetricAffinePencil p.h where
  center := center
  base := A
  direction := slope p s
  base_symmetric := hA
  direction_symmetric := slope_isSymm p s

/-- The real-exponent slope never degenerates.  This is NOT conditional. -/
theorem pencil_direction_nonsingular (p : ManuscriptChain.Real.Parameters) (s center : ℝ)
    (A : Matrix (Fin p.h) (Fin p.h) ℝ) (hA : A.IsSymm) :
    (pencil p s center A hA).direction.det ≠ 0 :=
  slope_det_ne_zero p s

/-- Universal spectral theorem conditional only on positivity of the supplied
matrix A; the paper's A(s) integral is not asserted to have been constructed. -/
noncomputable def factorization (p : ManuscriptChain.Real.Parameters) (s center : ℝ)
    (A : Matrix (Fin p.h) (Fin p.h) ℝ)
    (hA : A.IsSymm) (hpos : A.PosDef) :
    Spectral.RootFactorization (pencil p s center A hA) :=
  Spectral.rootFactorizationOfPosDef _ hpos
    (pencil_direction_nonsingular p s center A hA)

theorem all_complex_roots_real (p : ManuscriptChain.Real.Parameters) (s center : ℝ)
    (A : Matrix (Fin p.h) (Fin p.h) ℝ)
    (hA : A.IsSymm) (hpos : A.PosDef) (z : ℂ)
    (hz : Polynomial.eval₂ (algebraMap ℝ ℂ) z
      (pencil p s center A hA).detPolynomial = 0) :
    z.im = 0 :=
  (factorization p s center A hA hpos).complex_root_im_zero z hz

end PaperAdvances.Proposition3_2

#print axioms PaperAdvances.Proposition3_2.slope_det_ne_zero
#print axioms PaperAdvances.Proposition3_2.all_complex_roots_real
