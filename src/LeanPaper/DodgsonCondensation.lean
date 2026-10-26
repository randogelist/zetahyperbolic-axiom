import LeanPaper.PrincipalMinorRealRoots
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.Tactic

/-! All-rank Desnanot--Jacobi identity for symmetric polynomial pencils.
The central principal determinant is only required to be a nonzero polynomial;
it is allowed to vanish at the evaluation point. This is the hypothesis
supplied by the manuscript's positive Gram center. -/
noncomputable section
open scoped BigOperators
open Matrix Polynomial
namespace LeanPaper.DodgsonCondensation
set_option backward.isDefEq.respectTransparency false

/-- The border using the i-th additional row and j-th additional column. -/
def border {R n : Type*} (A : Matrix n n R) (U : Matrix n (Fin 2) R)
    (V : Matrix (Fin 2) n R) (D : Matrix (Fin 2) (Fin 2) R) (i j : Fin 2) :
    Matrix (n ⊕ Unit) (n ⊕ Unit) R :=
  fromBlocks A (fun a _ => U a j) (fun _ b => V i b) (fun _ _ => D i j)

lemma det_border {R n : Type*} [CommRing R] [Fintype n] [DecidableEq n]
    (A : Matrix n n R) (U : Matrix n (Fin 2) R) (V : Matrix (Fin 2) n R)
    (D : Matrix (Fin 2) (Fin 2) R) [Invertible A] (i j : Fin 2) :
    (border A U V D i j).det = A.det * (D - V * ⅟A * U) i j := by
  rw [border, det_fromBlocks₁₁]
  congr 1
  rw [Matrix.det_unique]
  simp [Matrix.mul_apply]

/-- Schur-complement derivation with an invertible central block. -/
theorem block_condensation {R n : Type*} [CommRing R] [Fintype n] [DecidableEq n]
    (A : Matrix n n R) (U : Matrix n (Fin 2) R) (V : Matrix (Fin 2) n R)
    (D : Matrix (Fin 2) (Fin 2) R) [Invertible A] :
    (fromBlocks A U V D).det * A.det =
      (border A U V D 0 0).det * (border A U V D 1 1).det -
        (border A U V D 0 1).det * (border A U V D 1 0).det := by
  simp only [det_border, det_fromBlocks₁₁, Matrix.det_fin_two]
  ring

lemma border_map {R S n : Type*} [Semiring R] [Semiring S]
    (f : R →+* S) (A : Matrix n n R) (U : Matrix n (Fin 2) R)
    (V : Matrix (Fin 2) n R) (D : Matrix (Fin 2) (Fin 2) R) (i j : Fin 2) :
    (border A U V D i j).map f = border (A.map f) (U.map f) (V.map f) (D.map f) i j := by
  apply Matrix.ext
  intro a b
  cases a <;> cases b <;> rfl

lemma map_det' {R S n : Type*} [CommRing R] [CommRing S]
    [Fintype n] [DecidableEq n] (f : R →+* S) (M : Matrix n n R) :
    f M.det = (M.map f).det := f.map_det M

/-- Polynomial identity valid even where the central block becomes singular. -/
theorem polynomial_block_condensation {K n : Type*} [Field K] [Fintype n] [DecidableEq n]
    (A : Matrix n n K[X]) (U : Matrix n (Fin 2) K[X])
    (V : Matrix (Fin 2) n K[X]) (D : Matrix (Fin 2) (Fin 2) K[X])
    (hA : A.det ≠ 0) :
    (fromBlocks A U V D).det * A.det =
      (border A U V D 0 0).det * (border A U V D 1 1).det -
        (border A U V D 0 1).det * (border A U V D 1 0).det := by
  let f := algebraMap K[X] (RatFunc K)
  have hf : Function.Injective f := RatFunc.algebraMap_injective K
  have hd : (A.map f).det ≠ 0 := by
    rw [← map_det' f A]
    exact map_ne_zero_iff f hf |>.mpr hA
  letI : Invertible (A.map f).det := invertibleOfNonzero hd
  letI : Invertible (A.map f) := Matrix.invertibleOfDetInvertible _
  apply hf
  simp only [map_mul, map_sub, map_det', border_map]
  have h := block_condensation (A.map f) (U.map f) (V.map f) (D.map f)
  convert h using 1
  congr 2
  apply Matrix.ext
  intro a b
  cases a <;> cases b <;> rfl

lemma border_transpose {R n : Type*} (A : Matrix n n R) (U : Matrix n (Fin 2) R)
    (D : Matrix (Fin 2) (Fin 2) R) (hA : A.IsSymm) (hD : D.IsSymm) (i j : Fin 2) :
    (border A U Uᵀ D i j)ᵀ = border A U Uᵀ D j i := by
  apply Matrix.ext
  intro a b
  cases a <;> cases b
  · rename_i a b
    exact congrArg (fun M => M a b) hA
  · rfl
  · rfl
  · exact congrArg (fun M => M j i) hD

/-- Symmetric polynomial pencils satisfy the square form of condensation. -/
theorem symmetric_polynomial_condensation {K n : Type*} [Field K]
    [Fintype n] [DecidableEq n]
    (A : Matrix n n K[X]) (U : Matrix n (Fin 2) K[X])
    (D : Matrix (Fin 2) (Fin 2) K[X]) (hA : A.IsSymm) (hD : D.IsSymm)
    (hne : A.det ≠ 0) :
    (fromBlocks A U Uᵀ D).det * A.det =
      (border A U Uᵀ D 0 0).det * (border A U Uᵀ D 1 1).det -
        (border A U Uᵀ D 0 1).det ^ 2 := by
  rw [polynomial_block_condensation A U Uᵀ D hne]
  have hb : (border A U Uᵀ D 1 0).det = (border A U Uᵀ D 0 1).det := by
    rw [← border_transpose A U D hA hD 0 1, det_transpose]
  rw [hb, pow_two]

/-- At every zero of the penultimate minor the Dodgson product is nonpositive.
No nonvanishing assumption at x is imposed on the smaller central minor. -/
theorem at_minor_root {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ[X]) (U : Matrix n (Fin 2) ℝ[X])
    (D : Matrix (Fin 2) (Fin 2) ℝ[X]) (hA : A.IsSymm) (hD : D.IsSymm)
    (hne : A.det ≠ 0) (x : ℝ) (hx : ((border A U Uᵀ D 0 0).det).eval x = 0) :
    ((fromBlocks A U Uᵀ D).det).eval x * (A.det).eval x =
        -(((border A U Uᵀ D 0 1).det).eval x)^2 ∧
      ((fromBlocks A U Uᵀ D).det).eval x * (A.det).eval x ≤ 0 := by
  have h := congrArg (Polynomial.eval x) (symmetric_polynomial_condensation A U D hA hD hne)
  simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_pow, hx, zero_mul,
    zero_sub] at h
  exact ⟨h, h.trans_le (neg_nonpos.mpr (sq_nonneg _))⟩

/-- Select one of the two final rows/columns together with the central block. -/
def keepOne {n : Type*} (i : Fin 2) : n ⊕ Unit → n ⊕ Fin 2 :=
  Sum.elim Sum.inl (fun _ => Sum.inr i)

/-- All-rank condensation directly in terms of selected submatrices. -/
theorem submatrix_condensation {K n : Type*} [Field K] [Fintype n] [DecidableEq n]
    (M : Matrix (n ⊕ Fin 2) (n ⊕ Fin 2) K[X]) (hs : M.IsSymm)
    (hne : (M.submatrix Sum.inl Sum.inl).det ≠ 0) :
    M.det * (M.submatrix Sum.inl Sum.inl).det =
      (M.submatrix (keepOne 0) (keepOne 0)).det *
        (M.submatrix (keepOne 1) (keepOne 1)).det -
          (M.submatrix (keepOne 0) (keepOne 1)).det ^ 2 := by
  let A := M.submatrix Sum.inl Sum.inl
  let U := M.submatrix Sum.inl Sum.inr
  let D := M.submatrix Sum.inr Sum.inr
  have hA : A.IsSymm := by
    apply Matrix.ext
    intro i j
    exact congrArg (fun B => B (Sum.inl i) (Sum.inl j)) hs
  have hD : D.IsSymm := by
    apply Matrix.ext
    intro i j
    exact congrArg (fun B => B (Sum.inr i) (Sum.inr j)) hs
  have hM : fromBlocks A U Uᵀ D = M := by
    apply Matrix.ext
    intro i j
    cases i <;> cases j
    · rfl
    · rfl
    · rename_i i j
      exact congrArg (fun B => B (Sum.inr i) (Sum.inl j)) hs
    · rfl
  have hb (i j : Fin 2) : border A U Uᵀ D i j =
      M.submatrix (keepOne i) (keepOne j) := by
    apply Matrix.ext
    intro a b
    cases a <;> cases b
    · rfl
    · rfl
    · rename_i a b
      exact congrArg (fun B => B (Sum.inr i) (Sum.inl b)) hs
    · rfl
  simpa only [hM, hb] using symmetric_polynomial_condensation A U D hA hD hne

/-- The actual rational pencil is symmetric as a polynomial matrix. -/
theorem manuscript_pencil_symmetric (p : ManuscriptChain.Real.Parameters) :
    (ManuscriptChain.Real.pencil p).IsSymm := by
  apply Matrix.ext
  intro i j
  simp only [Matrix.transpose_apply, ManuscriptChain.Real.pencil,
    ManuscriptChain.Real.entryA_symmetric p j.val i.val,
    ManuscriptChain.Real.entryM_symmetric p j.val i.val]

/-- The exact all-rank identity for the manuscript pencil. The selected indices
may be arbitrary; in particular initial segments give Theorem 3.4(2). -/
theorem manuscript_condensation (p : ManuscriptChain.Real.Parameters)
    (hp : ManuscriptChain.Real.Admissible p) {n : ℕ}
    (index : (Fin n ⊕ Fin 2) ↪ Fin p.h) :
    let M := (ManuscriptChain.Real.pencil p).submatrix index index
    M.det * (M.submatrix Sum.inl Sum.inl).det =
      (M.submatrix (keepOne 0) (keepOne 0)).det *
        (M.submatrix (keepOne 1) (keepOne 1)).det -
          (M.submatrix (keepOne 0) (keepOne 1)).det ^ 2 := by
  intro M
  apply submatrix_condensation M
  · apply Matrix.ext
    intro i j
    exact congrArg (fun B => B (index i) (index j)) (manuscript_pencil_symmetric p)
  · let core : Fin n ↪ Fin p.h :=
      ⟨fun i => index (Sum.inl i), index.injective.comp Sum.inl_injective⟩
    exact ManuscriptChain.PrincipalMinors.determinant_ne_zero p hp core

/-- The printed root-evaluation identity and its nonpositive sign, for all
orders of the actual pencil. No singular-slope hypothesis is required. -/
theorem manuscript_at_minor_root (p : ManuscriptChain.Real.Parameters)
    (hp : ManuscriptChain.Real.Admissible p) {n : ℕ}
    (index : (Fin n ⊕ Fin 2) ↪ Fin p.h) (x : ℝ)
    (hx : ManuscriptChain.Real.evalQ
      (((ManuscriptChain.Real.pencil p).submatrix index index).submatrix
        (keepOne 0) (keepOne 0)).det x = 0) :
    let M := (ManuscriptChain.Real.pencil p).submatrix index index
    ManuscriptChain.Real.evalQ M.det x *
      ManuscriptChain.Real.evalQ (M.submatrix Sum.inl Sum.inl).det x =
        -(ManuscriptChain.Real.evalQ (M.submatrix (keepOne 0) (keepOne 1)).det x)^2 ∧
    ManuscriptChain.Real.evalQ M.det x *
      ManuscriptChain.Real.evalQ (M.submatrix Sum.inl Sum.inl).det x ≤ 0 := by
  intro M
  let e : ℚ[X] →+* ℝ :=
    (Polynomial.evalRingHom x).comp (Polynomial.mapRingHom (Rat.castHom ℝ))
  have h := congrArg e (manuscript_condensation p hp index)
  simp only [map_mul, map_sub, map_pow] at h
  change e M.det * e (M.submatrix Sum.inl Sum.inl).det =
    e (M.submatrix (keepOne 0) (keepOne 0)).det *
      e (M.submatrix (keepOne 1) (keepOne 1)).det -
        (e (M.submatrix (keepOne 0) (keepOne 1)).det)^2 at h
  have hz : e (M.submatrix (keepOne 0) (keepOne 0)).det = 0 := hx
  rw [hz, zero_mul, zero_sub] at h
  exact ⟨h, h.trans_le (neg_nonpos.mpr (sq_nonneg _))⟩

end LeanPaper.DodgsonCondensation
#print axioms LeanPaper.DodgsonCondensation.at_minor_root
