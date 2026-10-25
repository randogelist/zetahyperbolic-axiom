import Theorem_3_1_Universal_Hyperbolicity_And_Zero_Free_Disk
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.Tactic

/-!
# Theorem 3.9 — arbitrary shifted-pole finite spectral theorem

This is a NEW proof of the finite algebraic transfer used in the manuscript's
Hurwitz and character Hankel constructions. Every finite size n is allowed.

For any injective real pole lattice `nodes`, any nonzero real residues `gamma`,
any positive-definite real symmetric base matrix G, and any real center, the
finite Hankel-style affine pencil has exact degree n, no zero at the center,
and only real complex roots. For a positive shift theta we also construct the
negative-square pole lattice `- (N+a+theta)^2` and prove it is injective; the
real-exponent rescaling of any nonzero base residue remains nonzero.

The paper's Hermite / Hurwitz and Dirichlet integral *evaluations* and their
positive-measure identities are NOT proved by these finite-algebra lemmas.
In particular the matrix parameter `G` is assumed PosDef as a domain condition,
not asserted to equal an as-yet-unconstructed shifted analytic Gram integral.
No new Witness field, axiom, sorry, or opaque declaration is used.
-/

noncomputable section
open scoped BigOperators
open Matrix Polynomial
namespace PaperAdvances.Theorem3_9_ShiftedPole

/-- Columns evaluate monomials at n distinct negative (or arbitrary) nodes. -/
def poleV {n : ℕ} (nodes : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  (Matrix.vandermonde nodes).transpose

/-- The exact pole-residue derivative matrix. -/
def poleM {n : ℕ} (nodes gamma : Fin n → ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  poleV nodes * Matrix.diagonal gamma * (poleV nodes).transpose

/-- Noncollision of pole nodes gives an invertible interpolation matrix. -/
theorem poleV_det_ne_zero {n : ℕ} (nodes : Fin n → ℝ)
    (hn : Function.Injective nodes) : (poleV nodes).det ≠ 0 := by
  unfold poleV
  rw [Matrix.det_transpose]
  exact Matrix.det_vandermonde_ne_zero_iff.mpr hn

/-- Exact finite determinant, with no analytic assumptions. -/
theorem poleM_det_formula {n : ℕ} (nodes gamma : Fin n → ℝ) :
    (poleM nodes gamma).det = (poleV nodes).det ^ 2 * ∏ a : Fin n, gamma a := by
  unfold poleM
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, Matrix.det_diagonal]
  ring

/-- Noncolliding nodes and nonzero residues force a nonsingular slope. -/
theorem poleM_det_ne_zero {n : ℕ} (nodes gamma : Fin n → ℝ)
    (hn : Function.Injective nodes) (hgamma : ∀ a, gamma a ≠ 0) :
    (poleM nodes gamma).det ≠ 0 := by
  rw [poleM_det_formula]
  apply mul_ne_zero
  · exact pow_ne_zero _ (poleV_det_ne_zero nodes hn)
  · exact Finset.prod_ne_zero_iff.mpr (fun a _ => hgamma a)

/-- Moment-index entry formula for the pole derivative. -/
theorem poleM_entry {n : ℕ} (nodes gamma : Fin n → ℝ) (i j : Fin n) :
    poleM nodes gamma i j =
      ∑ a : Fin n, poleV nodes i a * gamma a * poleV nodes j a := by
  unfold poleM
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply]

/-- Pole derivative symmetry, independent of any sign condition. -/
theorem poleM_isSymm {n : ℕ} (nodes gamma : Fin n → ℝ) :
    (poleM nodes gamma).IsSymm := by
  ext i j
  simp only [Matrix.transpose_apply, poleM_entry]
  apply Finset.sum_congr rfl
  intro a _
  ring

/-- Generic shifted-pole symmetric matrix pencil. -/
def polePencil {n : ℕ} (nodes gamma : Fin n → ℝ)
    (center : ℝ) (G : Matrix (Fin n) (Fin n) ℝ) (hG : G.IsSymm) :
    ManuscriptChain.Spectral.SymmetricAffinePencil n where
  center := center
  base := G
  direction := poleM nodes gamma
  base_symmetric := hG
  direction_symmetric := poleM_isSymm nodes gamma

/-- The exact degree of the pole Hankel determinant for a positive base. -/
theorem polePencil_degree {n : ℕ} (nodes gamma : Fin n → ℝ)
    (hn : Function.Injective nodes) (hgamma : ∀ a, gamma a ≠ 0)
    (center : ℝ) (G : Matrix (Fin n) (Fin n) ℝ)
    (hG : G.IsSymm) (hpos : G.PosDef) :
    (polePencil nodes gamma center G hG).detPolynomial.natDegree = n :=
  ManuscriptChain.Spectral.theorem_3_1_degree_of_posDef
    (polePencil nodes gamma center G hG) hpos
    (poleM_det_ne_zero nodes gamma hn hgamma)

/-- No root of the determinant occurs at the distinguished center. -/
theorem polePencil_center_ne_zero {n : ℕ} (nodes gamma : Fin n → ℝ)
    (center : ℝ) (G : Matrix (Fin n) (Fin n) ℝ)
    (hG : G.IsSymm) (hpos : G.PosDef) :
    (polePencil nodes gamma center G hG).detPolynomial.eval center ≠ 0 :=
  (polePencil nodes gamma center G hG).center_nonvanishing_of_positive hpos

/-- Entire complex zero set is real, for every matrix size. -/
theorem polePencil_complex_roots_real {n : ℕ} (nodes gamma : Fin n → ℝ)
    (hn : Function.Injective nodes) (hgamma : ∀ a, gamma a ≠ 0)
    (center : ℝ) (G : Matrix (Fin n) (Fin n) ℝ)
    (hG : G.IsSymm) (hpos : G.PosDef) (z : ℂ)
    (hz : Polynomial.eval₂ (algebraMap ℝ ℂ) z
      (polePencil nodes gamma center G hG).detPolynomial = 0) :
    z.im = 0 :=
  ManuscriptChain.Spectral.theorem_3_1_hyperbolicity_of_posDef
    (polePencil nodes gamma center G hG) hpos
    (poleM_det_ne_zero nodes gamma hn hgamma) z hz

/-- The positive physical coordinate of an arbitrary positive shifted pole. -/
def shiftedPositiveNode {n : ℕ} (N : ℕ) (theta : ℝ) (a : Fin n) : ℝ :=
  (N : ℝ) + (a.val : ℝ) + theta

/-- The negative-square shifted Hurwitz pole lattice. -/
def shiftedSquareNode {n : ℕ} (N : ℕ) (theta : ℝ) (a : Fin n) : ℝ :=
  - (shiftedPositiveNode N theta a) ^ 2

theorem shiftedPositiveNode_pos {n : ℕ} (N : ℕ) (theta : ℝ)
    (htheta : 0 < theta) (a : Fin n) :
    0 < shiftedPositiveNode N theta a := by
  unfold shiftedPositiveNode
  positivity

/-- Negative squares at the shifted integers are pairwise distinct. -/
theorem shiftedSquareNode_injective {n : ℕ} (N : ℕ) (theta : ℝ)
    (htheta : 0 < theta) :
    Function.Injective (shiftedSquareNode (n := n) N theta) := by
  intro a b hab
  have ha : 0 < shiftedPositiveNode N theta a :=
    shiftedPositiveNode_pos N theta htheta a
  have hb : 0 < shiftedPositiveNode N theta b :=
    shiftedPositiveNode_pos N theta htheta b
  have hs : (shiftedPositiveNode N theta a) ^ 2 =
      (shiftedPositiveNode N theta b) ^ 2 := by
    dsimp [shiftedSquareNode] at hab
    linarith
  have hmul :
      (shiftedPositiveNode N theta a - shiftedPositiveNode N theta b) *
        (shiftedPositiveNode N theta a + shiftedPositiveNode N theta b) = 0 := by
    nlinarith [hs]
  have hsum : shiftedPositiveNode N theta a + shiftedPositiveNode N theta b ≠ 0 :=
    ne_of_gt (add_pos ha hb)
  have heq : shiftedPositiveNode N theta a = shiftedPositiveNode N theta b :=
    sub_eq_zero.mp ((mul_eq_zero.mp hmul).resolve_right hsum)
  have hv : (a.val : ℝ) = (b.val : ℝ) := by
    dsimp [shiftedPositiveNode] at heq
    linarith
  apply Fin.ext
  exact_mod_cast hv

/-- All real-exponent pole scales preserve nonzero base residues. -/
def shiftedGamma {n : ℕ} (N : ℕ) (theta s : ℝ)
    (residue : Fin n → ℝ) (a : Fin n) : ℝ :=
  residue a * (shiftedPositiveNode N theta a) ^ (s - 1)

theorem shiftedGamma_ne_zero {n : ℕ} (N : ℕ) (theta s : ℝ)
    (htheta : 0 < theta) (residue : Fin n → ℝ)
    (hres : ∀ a, residue a ≠ 0) (a : Fin n) :
    shiftedGamma N theta s residue a ≠ 0 := by
  unfold shiftedGamma
  exact mul_ne_zero (hres a)
    (ne_of_gt (Real.rpow_pos_of_pos (shiftedPositiveNode_pos N theta htheta a) _))

/-- The exact shifted-Hurwitz pole derivative is nonsingular in every size. -/
theorem hurwitz_slope_nonsingular {n : ℕ} (N : ℕ) (theta s : ℝ)
    (htheta : 0 < theta) (residue : Fin n → ℝ)
    (hres : ∀ a, residue a ≠ 0) :
    (poleM (shiftedSquareNode (n := n) N theta)
      (shiftedGamma N theta s residue)).det ≠ 0 :=
  poleM_det_ne_zero _ _
    (shiftedSquareNode_injective N theta htheta)
    (shiftedGamma_ne_zero N theta s htheta residue hres)

/-- General Hurwitz/Dirichlet finite matrix-pencil transfer. This is not yet
    the paper's analytic Gram integral because positive definiteness is a
    domain condition on the supplied real symmetric base matrix. -/
theorem hurwitz_complex_roots_real {n : ℕ} (N : ℕ) (theta s center : ℝ)
    (htheta : 0 < theta) (residue : Fin n → ℝ)
    (hres : ∀ a, residue a ≠ 0)
    (G : Matrix (Fin n) (Fin n) ℝ) (hG : G.IsSymm) (hpos : G.PosDef)
    (z : ℂ)
    (hz : Polynomial.eval₂ (algebraMap ℝ ℂ) z
      (polePencil (shiftedSquareNode (n := n) N theta)
        (shiftedGamma N theta s residue) center G hG).detPolynomial = 0) :
    z.im = 0 :=
  polePencil_complex_roots_real _ _
    (shiftedSquareNode_injective N theta htheta)
    (shiftedGamma_ne_zero N theta s htheta residue hres)
    center G hG hpos z hz

end PaperAdvances.Theorem3_9_ShiftedPole

#print axioms PaperAdvances.Theorem3_9_ShiftedPole.poleM_det_ne_zero
#print axioms PaperAdvances.Theorem3_9_ShiftedPole.polePencil_complex_roots_real
#print axioms PaperAdvances.Theorem3_9_ShiftedPole.hurwitz_slope_nonsingular
#print axioms PaperAdvances.Theorem3_9_ShiftedPole.hurwitz_complex_roots_real
