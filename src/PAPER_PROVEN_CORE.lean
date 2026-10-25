import MAIN_CHAIN_ASSEMBLED
import Theorem_2_4_Primitive_Normalization_Minimality
import Theorem_2_5_Weight_Change
import Theorem_4_1_Leading_Coefficient_Gap

/-!
# Proven paper core, without project-owned axioms or omitted hypotheses

This is the *unconditional general odd-weight spectral endpoint* and the
exact finite algebra/normalization identities. Domain admissibility is an
ordinary parameter restriction, not an unproved analytic premise.

It is NOT a formalization of all 52 manuscript pages. In particular, it
makes no claim about the manuscript's unverified measure 25687, all-odd
irrationality, or statements identified as false in the paper audit.
-/

noncomputable section

namespace ZetaPaperNoGaps

/-- Canonical admissible parameters: arbitrary indices, no external hypothesis. -/
def canonicalParameters (k m N h : ℕ) : ManuscriptChain.Real.Parameters :=
  ⟨k + 1, m + 1, N + 1, N + 1 + (h + 1)⟩

private theorem canonicalAdmissible (k m N h : ℕ) :
    ManuscriptChain.Real.Admissible (canonicalParameters k m N h) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> dsimp [canonicalParameters] <;> omega

/-- Fully unconditional all-odd-weight spectral theorem; the positivity
    conditions are satisfied by construction, not imposed on the caller. -/
theorem ALL_ODD_WEIGHT_SPECTRAL_NO_PREMISES (k m N h : ℕ) :
    ManuscriptChain.General.GeneralStatement (canonicalParameters k m N h) :=
  ManuscriptChain.MAIN_CHAIN_UNCONDITIONAL _ (canonicalAdmissible k m N h)

theorem ODD_WEIGHT_SPECTRAL
    (p : ManuscriptChain.Real.Parameters)
    (hp : ManuscriptChain.Real.Admissible p) :
    ManuscriptChain.General.GeneralStatement p :=
  ManuscriptChain.MAIN_CHAIN_UNCONDITIONAL p hp

theorem ODD_WEIGHT_EXACT_ZERO_FREE_DISK
    (p : ManuscriptChain.Real.Parameters)
    (hp : ManuscriptChain.Real.Admissible p) :
    ∃ radius : ℝ, 0 < radius ∧
      (∀ z : ℂ, ‖z - (ManuscriptChain.Real.zeta p.weight : ℂ)‖ < radius →
        ¬ ManuscriptChain.General.ComplexRoot p z) ∧
      (∃ z : ℂ, ManuscriptChain.General.ComplexRoot p z ∧
        ‖z - (ManuscriptChain.Real.zeta p.weight : ℂ)‖ = radius) :=
  ManuscriptChain.EXACT_ZERO_FREE_DISK p hp

theorem ORIGINAL_PENCIL_SPECTRAL
    (p : Zetahyperbolic.HankelParams) (k : ℕ) (hk : 1 ≤ k) :
    ManuscriptChain.General.GeneralStatement
      (Zetahyperbolic.ManuscriptCompatibility.toParameters p k) :=
  Zetahyperbolic.MAIN_CHAIN_UNCONDITIONAL p k hk

end ZetaPaperNoGaps

-- Real theorem declarations already checked in the supplied baseline:
#check ManuscriptChain.BasisInvariance.theorem_2_4_canonical_basis_invariance
#check ManuscriptChain.PoleDiagonalization.derivativeMatrix_det_ne_zero
#check ManuscriptChain.LeadingCoefficientGap.primitivePolynomial_eval_eq
#check ManuscriptChain.PoleDiagonalization.delta_leadingCoeff_reweight_add

-- For these endpoints only standard logical axioms are expected.
#print axioms ZetaPaperNoGaps.ALL_ODD_WEIGHT_SPECTRAL_NO_PREMISES
#print axioms ZetaPaperNoGaps.ODD_WEIGHT_SPECTRAL
#print axioms ZetaPaperNoGaps.ODD_WEIGHT_EXACT_ZERO_FREE_DISK
#print axioms ZetaPaperNoGaps.ORIGINAL_PENCIL_SPECTRAL
#print axioms ManuscriptChain.LeadingCoefficientGap.primitivePolynomial_eval_eq
