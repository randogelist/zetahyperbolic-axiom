import MAIN_CHAIN_ASSEMBLED
import Mathlib.Tactic

/-!
# Original-paper principal minors at the true odd-zeta center

New source candidate; native Windows Lean 4.33 compilation and axiom audit
are pending. Theorem 3.3(1), principal-minor portion only, and the center
nonvanishing needed by Theorem 3.4. No claim of arbitrary mixed minors,
strict total positivity, interlacing, or the exact minor-degree law.

This imports the actual original-pencil analytic realization from source20.
The only mathematical hypotheses are the manuscript parameter conditions
and injectivity of the selected row/column indices.
-/

noncomputable section
open Polynomial

namespace ManuscriptChain.PrincipalMinors

/-- A genuine principal subpencil of the manuscript's rational pencil. -/
def pencil (p : Real.Parameters) {r : ℕ}
    (index : Fin r ↪ Fin p.h) : Matrix (Fin r) (Fin r) ℚ[X] :=
  (Real.pencil p).submatrix index index

/-- Its rational determinant polynomial; no degree or root data is supplied. -/
def determinant (p : Real.Parameters) {r : ℕ}
    (index : Fin r ↪ Fin p.h) : ℚ[X] :=
  Matrix.det (pencil p index)

/-- Its real matrix at a specified real center. -/
def gram (p : Real.Parameters) {r : ℕ}
    (index : Fin r ↪ Fin p.h) (x : ℝ) : Matrix (Fin r) (Fin r) ℝ :=
  (Real.gram p x).submatrix index index

/-- Evaluation commutes with the selected determinant, so the polynomial
is tied to the original rational moment entries. -/
theorem eval_determinant (p : Real.Parameters) {r : ℕ}
    (index : Fin r ↪ Fin p.h) (x : ℝ) :
    Real.evalQ (determinant p index) x = (gram p index x).det := by
  let evaluation : ℚ[X] →+* ℝ :=
    (Polynomial.evalRingHom x).comp (Polynomial.mapRingHom (Rat.castHom ℝ))
  have hmap := evaluation.map_det (pencil p index)
  change evaluation (Matrix.det (pencil p index)) =
    Matrix.det ((pencil p index).map evaluation) at hmap
  exact hmap

/-- Every principal submatrix is strictly positive definite, including
nonconsecutive selected indices. Positivity is derived from the actual
Bose-density realization, not assumed as a matrix hypothesis. -/
theorem gram_posDef (p : Real.Parameters) (hp : Real.Admissible p)
    {r : ℕ} (index : Fin r ↪ Fin p.h) :
    (gram p index (Real.zeta p.weight)).PosDef := by
  exact (GRAM_POSITIVE p hp).submatrix index.injective

/-- The principal-minor part of manuscript Theorem 3.3(1). -/
theorem determinant_center_pos (p : Real.Parameters) (hp : Real.Admissible p)
    {r : ℕ} (index : Fin r ↪ Fin p.h) :
    0 < Real.evalQ (determinant p index) (Real.zeta p.weight) := by
  rw [eval_determinant]
  exact (gram_posDef p hp index).det_pos

/-- A genuine principal determinant polynomial cannot vanish identically. -/
theorem determinant_ne_zero (p : Real.Parameters) (hp : Real.Admissible p)
    {r : ℕ} (index : Fin r ↪ Fin p.h) :
    determinant p index ≠ 0 := by
  intro hzero
  have hpos := determinant_center_pos p hp index
  rw [hzero] at hpos
  simpa [Real.evalQ, Real.realPolynomial] using hpos

/-- The explicit initial-segment embedding for a leading principal minor. -/
def leadingIndex (p : Real.Parameters) (r : ℕ) (hr : r ≤ p.h) :
    Fin r ↪ Fin p.h where
  toFun i := ⟨i.val, lt_of_lt_of_le i.isLt hr⟩
  inj' := by
    intro i j hij
    apply Fin.ext
    exact congrArg Fin.val hij

/-- Every leading principal determinant is positive at the actual zeta
center. This gives the required nonzero starting point for the minor chain. -/
theorem leading_determinant_center_pos (p : Real.Parameters)
    (hp : Real.Admissible p) (r : ℕ) (hr : r ≤ p.h) :
    0 < Real.evalQ (determinant p (leadingIndex p r hr)) (Real.zeta p.weight) :=
  determinant_center_pos p hp (leadingIndex p r hr)

/-- Strict two-index minor inequality for the original Gram entries.
This is a genuine rank-two strictness result for every pair of distinct
indices, not an assumed generic Gram or supplied numerical witness. -/
theorem two_index_strict (p : Real.Parameters) (hp : Real.Admissible p)
    (i j : Fin p.h) (hij : i ≠ j) :
    Real.gram p (Real.zeta p.weight) i j *
        Real.gram p (Real.zeta p.weight) j i <
      Real.gram p (Real.zeta p.weight) i i *
        Real.gram p (Real.zeta p.weight) j j := by
  have hinj : Function.Injective (![i, j] : Fin 2 → Fin p.h) := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all
  have hpos := ((GRAM_POSITIVE p hp).submatrix hinj).det_pos
  have hdet : 0 <
      Real.gram p (Real.zeta p.weight) i i *
          Real.gram p (Real.zeta p.weight) j j -
        Real.gram p (Real.zeta p.weight) i j *
          Real.gram p (Real.zeta p.weight) j i := by
    simpa [Matrix.det_fin_two, Matrix.submatrix] using hpos
  exact sub_pos.mp hdet

end ManuscriptChain.PrincipalMinors

#print axioms ManuscriptChain.PrincipalMinors.eval_determinant
#print axioms ManuscriptChain.PrincipalMinors.gram_posDef
#print axioms ManuscriptChain.PrincipalMinors.determinant_center_pos
#print axioms ManuscriptChain.PrincipalMinors.determinant_ne_zero
#print axioms ManuscriptChain.PrincipalMinors.leading_determinant_center_pos
#print axioms ManuscriptChain.PrincipalMinors.two_index_strict
