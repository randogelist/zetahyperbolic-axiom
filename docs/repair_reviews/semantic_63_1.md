# Theorem 6.3(1): actual prime matrix and local determinant

Verification status: source-complete candidate, pending receiving-branch GitHub CI and transitive axiom audit. The previously accepted 260-module main receipt remains authoritative until this follow-up passes. No local Lean/compiler execution was used.

The endpoint `ManuscriptChain.Beukers.PrimeMatrix.theorem_6_3_1` preserves the original hypotheses: q is any prime with q≥5, K=2q−1, h=q, and the coefficient rows are exactly `A_r(x)=x^r+x^(r+q)` for 0≤r<q. Its first conclusion is the exact valuation `v_q(Δ_Aq(0))=−7q`; it also proves nonvanishing at zero and, for every pair of integers a,b with q∤b, nonvanishing and the same valuation at a/b. There is no assumed matrix valuation, determinant nonvanishing, local congruence or spectral input.

`BeukersPrimeMatrix.lean` constructs the literal coefficient rows, proves that they equal the coefficients of the stated polynomials and that their coefficient map is injective. `matrix_entry` expands the original `Real.dualEntry` into all four actual rational moments and proves the slope is `2 I`. `matrix_diagonal` identifies its actual harmonic expression. `determinant_eq_dualDelta` proves that the determinant used by the local arithmetic argument is exactly evaluation of the existing original dual determinant polynomial. Thus the endpoint concerns the manuscript family, not an arbitrary matrix satisfying unproved local hypotheses. The already accepted actual Beukers integral-to-dual-entry bridge supplies the corresponding continuous-family identification.

`BeukersHarmonicRemainders.lean` isolates the actual q-pole in the finite harmonic sums. Its lower harmonic and high-index remainder bounds show that q⁷ times each actual diagonal differs from −2/3 by q-adic norm strictly less than one. Distinct-residue off-diagonal moments have normalized norm less than one. `BeukersPrimeMatrix` proves the same bounds for all four moments of each basis pair and for every rational X of norm at most one; the literal a/b endpoint derives this norm condition from q∤b.

`PadicDominantDeterminant.lean` proves the needed finite determinant result: the identity-permutation term has norm one and all other permutation terms have norm strictly below one. Its determinant conclusion and scalar-rescaling theorem give the exact valuation after multiplication by q⁷. Zero off-diagonal entries are allowed and do not require ad hoc exceptions to the valuation proof.

## Correction to the intermediate printed congruence

The printed proof states its unscaled diagonal congruence modulo Z_q. This is stronger than needed and false at the permitted q=7,r=0. The new module contains exact rational certificates:

`G_A7(0)_(0,0) + 2/(3·7⁷) = −18809799306101/19595520000000`.

The reduced denominator is divisible by 7 and the numerator is not. The candidate Lean theorems `seven_diagonal_remainder_exact` and `seven_diagonal_remainder_not_integral` prove these finite arithmetic facts. The corrected proof only requires the normalized remainder to have norm less than one (equivalently, the unscaled error has valuation greater than −7). The stronger integral-remainder assertion is neither assumed nor needed, and the original determinant statement is unchanged.

## Separate status of part (2)

This proof does not use or repair the positive-cone assertion in 6.3(2). Its actual h=4,K=28 counterexample and the missing quantitative negative-tail control remain independent obstacles. Completing 6.3(1) therefore does not mark the whole two-part Theorem 6.3 complete.
