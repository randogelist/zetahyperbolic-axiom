import PaperChain.Stage02
import Theorem_3_1_Universal_Hyperbolicity_And_Zero_Free_Disk

/-!
Stage 3: explicit positive-definite input -> Hermitian spectral
factorization, real roots and zero-free disk. The *actual integral Gram
positivity* is a separate already-proved manuscript endpoint only if the
corresponding external anchor source and axiom audit are present. This
file does not invent that input.
-/

namespace PaperChain
open ManuscriptChain.Spectral

/-- Exact spectral-root factorization conditional only on matrix positivity and
nonsingular derivative; this is a finite-dimensional theorem, not a zeta claim. -/
theorem stage03_spectral_factorization {n : ℕ}
    (p : SymmetricAffinePencil n)
    (hpos : p.base.PosDef) (hderiv : Matrix.det p.direction ≠ 0) :
    Nonempty (RootFactorization p) :=
  rootFactorization_nonempty_of_posDef p hpos hderiv

/-- Every complex zero of the determinant pencil is real. -/
theorem stage03_all_roots_real {n : ℕ}
    (p : SymmetricAffinePencil n)
    (hpos : p.base.PosDef) (hderiv : Matrix.det p.direction ≠ 0)
    (z : ℂ) (hz : Polynomial.eval₂ (algebraMap ℝ ℂ) z p.detPolynomial = 0) :
    z.im = 0 :=
  theorem_3_1_hyperbolicity_of_posDef p hpos hderiv z hz

/-- A finite spectral bound produces an explicit root-free disk. -/
theorem stage03_zero_free_disk {n : ℕ} {p : SymmetricAffinePencil n}
    (c : RootFactorization p) (L x : ℝ)
    (hbound : ∀ i : Fin n, |c.beta i| ≤ L)
    (hx : |x - p.center| < 1 / L) :
    p.detPolynomial.eval x ≠ 0 :=
  c.eval_ne_zero_of_distance_lt L x hbound hx

end PaperChain
