import PAPER_PROVEN_CORE

/-!
# Paper chapters 2–3: proved native Lean chain

The rational Hankel determinant is the actual manuscript determinant.
Derivative invertibility, exact degree, positive Gram realization,
real-rootedness and an exact nonzero zero-free disk are theorems, not
hypotheses of the eventual Diophantine witness.
-/

noncomputable section

namespace ZetaHyperbolicPaper

/-- Chapter 2: full exact determinant degree (finite arithmetic). -/
theorem CHAPTER_2_DEGREE (p : ManuscriptChain.Real.Parameters) :
    (ManuscriptChain.Real.delta p).natDegree = p.h :=
  ManuscriptChain.General.delta_degree p

/-- Chapter 2: nondegenerate Vandermonde derivative matrix. -/
theorem CHAPTER_2_DERIVATIVE (p : ManuscriptChain.Real.Parameters) :
    (ManuscriptChain.Real.derivativeMatrix p).det ≠ 0 :=
  ManuscriptChain.General.derivative_nonsingular p

/-- Chapter 3: unconditional hyperbolicity for every admissible odd weight. -/
theorem CHAPTER_3_SPECTRAL
    (p : ManuscriptChain.Real.Parameters)
    (hp : ManuscriptChain.Real.Admissible p) :
    ManuscriptChain.General.GeneralStatement p :=
  ManuscriptChain.MAIN_CHAIN_UNCONDITIONAL p hp

/-- Chapter 3: the actual determinant has an exact positive root-free radius. -/
theorem CHAPTER_3_EXACT_DISK
    (p : ManuscriptChain.Real.Parameters)
    (hp : ManuscriptChain.Real.Admissible p) :
    ∃ radius : ℝ, 0 < radius ∧
      (∀ z : ℂ, ‖z - (ManuscriptChain.Real.zeta p.weight : ℂ)‖ < radius →
        ¬ ManuscriptChain.General.ComplexRoot p z) ∧
      (∃ z : ℂ, ManuscriptChain.General.ComplexRoot p z ∧
        ‖z - (ManuscriptChain.Real.zeta p.weight : ℂ)‖ = radius) :=
  ManuscriptChain.EXACT_ZERO_FREE_DISK p hp

end ZetaHyperbolicPaper

#print axioms ZetaHyperbolicPaper.CHAPTER_2_DEGREE
#print axioms ZetaHyperbolicPaper.CHAPTER_2_DERIVATIVE
#print axioms ZetaHyperbolicPaper.CHAPTER_3_SPECTRAL
#print axioms ZetaHyperbolicPaper.CHAPTER_3_EXACT_DISK
