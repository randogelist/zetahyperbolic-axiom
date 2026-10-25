import Definition_2_1_Order_s_Rational_Moment_Functional

/-!
# Theorem 5.1 (Two-variable Beukers measure for ζ(7))

PDF pp. 22-23. Supporting constructions only: rational dual moments, pencil
entries, determinant, and integer-normalization interfaces. The two-variable
integral identity in the printed theorem is not proved in this package.
The supplied normalization interface is not imported in this selection.
-/

noncomputable section
open scoped BigOperators
open Polynomial

namespace ManuscriptChain.Real

def dualConstant (s r t : ℕ) : ℚ :=
  if r = t then -harmonic s r
  else (harmonic (s - 1) r - harmonic (s - 1) t) /
    ((s - 1 : ℕ) * ((r : ℚ) - (t : ℚ)))

def dualEntry {h K : ℕ} (s : ℕ) (c : Fin h → Fin (K + 1) → ℚ)
    (i j : Fin h) : ℚ[X] :=
  C (∑ r, ∑ t, c i r * c j t * dualConstant s r.val t.val) +
    C (∑ r, c i r * c j r) * X

def dualDelta {h K : ℕ} (s : ℕ) (c : Fin h → Fin (K + 1) → ℚ) : ℚ[X] :=
  Matrix.det (fun i j => dualEntry s c i j)

end ManuscriptChain.Real

