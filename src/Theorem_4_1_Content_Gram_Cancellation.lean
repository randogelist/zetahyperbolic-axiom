import Theorem_4_1_Determinant_Log_Energy
import Mathlib.Tactic.Linarith

/-!
# Section 4/8: exact primitive-content cancellation on the real pencil

For the ACTUAL canonical integer primitive normalization of the manuscript
pencil, the Vandermonde/pole determinant enters the leading coefficient and
the determinant ratio with opposite signs. It cancels EXACTLY at finite K:

  P_p(zeta(2k+1)) = scale(delta_p) * det G_p(zeta(2k+1)).

Consequently the one genuine quadratic-decay condition is EQUIVALENT to a
uniform negative quadratic upper bound for two logarithms: the positive
rational primitive scale and the actual positive-definite Gram determinant.
No claimed asymptotic (nor irrationality of zeta(5)) is proved here.
-/

noncomputable section

namespace ManuscriptChain.ContentGramCancellation

open GeneralIrrationality LeadingCoefficientGap FiniteEnergy

/-- The exact rational primitive-normalization multiplier on the log scale. -/
def contentLog (p : Real.Parameters) : ℝ :=
  _root_.Real.log ((normalization p).scale : ℝ)

/-- No slope determinant survives in the actual primitive zeta evaluation. -/
theorem primitive_eval_eq_scale_mul_gram (p : Real.Parameters) :
    RealTransfer.evalReal (primitivePolynomial p) (Real.zeta p.weight) =
      ((normalization p).scale : ℝ) *
        (Real.gram p (Real.zeta p.weight)).det := by
  rw [primitivePolynomial_eval, Real.delta_eval_eq_det_gram]

/-- Exact log identity on the actual admissible analytic moment pencil. -/
theorem primitive_eval_log_eq_content_add_gram
    (p : Real.Parameters) (hp : Real.Admissible p) :
    _root_.Real.log
        (RealTransfer.evalReal (primitivePolynomial p) (Real.zeta p.weight)) =
      contentLog p + gramLog p := by
  rw [primitive_eval_eq_scale_mul_gram]
  unfold contentLog gramLog
  have hscale : 0 < ((normalization p).scale : ℝ) := by
    exact_mod_cast (normalization p).scale_pos
  have hgram : 0 < (Real.gram p (Real.zeta p.weight)).det :=
    (GRAM_POSITIVE p hp).det_pos
  exact _root_.Real.log_mul hscale.ne' hgram.ne'

/-- The original finite-K primitive value-decay log has only TWO inputs. -/
theorem valueDecayLog_eq_neg_content_sub_gram
    (p : Real.Parameters) (hp : Real.Admissible p) :
    valueDecayLog p = -(contentLog p + gramLog p) := by
  unfold valueDecayLog
  rw [primitive_eval_log_eq_content_add_gram p hp]

/-- Exact cancellation of pole-slope energy against primitive height. -/
theorem content_add_gram_eq_height_sub_energy
    (p : Real.Parameters) (hp : Real.Admissible p) :
    contentLog p + gramLog p =
      leadingLog p - determinantEnergy p := by
  have hcons := finite_potential_conservation p hp
  have hvalue := valueDecayLog_eq_neg_content_sub_gram p hp
  linarith

/-- Exact IFF for the genuine normalized quadratic-decay premise.
The right side does NOT assert existence of rates: it is the open estimate. -/
theorem normalizedQuadraticDecay_iff_content_gram_quadratic
    (p : ℕ → Real.Parameters) (hp : ∀ n, Real.Admissible (p n)) :
    NormalizedQuadraticDecay p ↔
      ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ, ∀ n, n₀ ≤ n →
        contentLog (p n) + gramLog (p n) ≤
          -c * ((p n).K : ℝ) ^ 2 := by
  constructor
  · intro hd
    obtain ⟨c, hc, n₀, hgap⟩ :=
      (normalizedQuadraticDecay_iff_energy_gap p hp).mp hd
    refine ⟨c, hc, n₀, ?_⟩
    intro n hn
    rw [content_add_gram_eq_height_sub_energy (p n) (hp n)]
    exact hgap n hn
  · rintro ⟨c, hc, n₀, hgap⟩
    apply (normalizedQuadraticDecay_iff_energy_gap p hp).mpr
    refine ⟨c, hc, n₀, ?_⟩
    intro n hn
    rw [← content_add_gram_eq_height_sub_energy (p n) (hp n)]
    exact hgap n hn

/-- TWO explicit actual-data upper rates with a negative sum suffice.
The sign gap and both rate bounds remain independently OPEN premises. -/
theorem normalizedQuadraticDecay_of_content_gram_rates
    (p : ℕ → Real.Parameters) (hp : ∀ n, Real.Admissible (p n))
    (A B : ℝ) (hAB : A + B < 0) (n₀ : ℕ)
    (hcontent : ∀ n, n₀ ≤ n →
      contentLog (p n) ≤ A * ((p n).K : ℝ) ^ 2)
    (hgram : ∀ n, n₀ ≤ n →
      gramLog (p n) ≤ B * ((p n).K : ℝ) ^ 2) :
    NormalizedQuadraticDecay p := by
  apply (normalizedQuadraticDecay_iff_content_gram_quadratic p hp).mpr
  refine ⟨-(A + B), neg_pos.mpr hAB, n₀, ?_⟩
  intro n hn
  calc
    contentLog (p n) + gramLog (p n) ≤
        A * ((p n).K : ℝ) ^ 2 + B * ((p n).K : ℝ) ^ 2 :=
      add_le_add (hcontent n hn) (hgram n hn)
    _ = -(-(A + B)) * ((p n).K : ℝ) ^ 2 := by ring

end ManuscriptChain.ContentGramCancellation
