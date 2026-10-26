import PaperChain.Stage05

/-!
Stage 6: theorem 4.4 conditional spectral growth target. The numerical
constants are represented exactly as rationals in ℝ. No alleged proof of
the paper's Legendre/Stirling maximum is contained here.
-/

namespace PaperChain

/-- The missing, genuine spectral estimate for the actual zeta(5) family.
`normB K` must subsequently be identified with the operator norm of the
actual B_K; leaving it an argument makes that bridge visible. -/
def HasZeta5StandardSpectralEstimate
    (normB : ℕ → ℝ) (K₀ : ℕ) : Prop :=
  ∀ K, K₀ ≤ K →
    normB K ≤ Real.exp ((11407 / 1000 : ℝ) * (K : ℝ))

def HasZeta5SharpenedSpectralEstimate
    (normB : ℕ → ℝ) (K₀ : ℕ) : Prop :=
  ∀ K, K₀ ≤ K →
    normB K ≤ Real.exp ((10954 / 1000 : ℝ) * (K : ℝ))

/-- Unconditional comparison of the paper's two numerical upper envelopes. -/
theorem stage06_sharpened_implies_standard
    (normB : ℕ → ℝ) (K₀ : ℕ)
    (h : HasZeta5SharpenedSpectralEstimate normB K₀) :
    HasZeta5StandardSpectralEstimate normB K₀ := by
  intro K hK
  have hk : (0 : ℝ) ≤ (K : ℝ) := Nat.cast_nonneg K
  exact (h K hK).trans (Real.exp_le_exp.mpr (by nlinarith))

end PaperChain
