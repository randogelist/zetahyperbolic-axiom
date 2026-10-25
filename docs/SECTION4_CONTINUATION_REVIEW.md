# Section 4 continuation review

This review concerns the literal 52-page manuscript supplied with the project.
Its mathematical classifications are separate from compiler acceptance.

## 4.1: transfer criterion

The baseline proved the integer squeeze and a conditional transfer but left
`IndexBudget` as an input. `LeanPaper.Section4IndexSelection` constructs the
index `d0 * floor(c * log(b) / d0)`, proves its lattice bounds and divergence,
and derives the radius and denominator budgets from explicit strict rate gaps.
`LeanPaper.Section4ComplexComparison` targets the comparison for arbitrary
complex-root polynomials, removing the special symmetric-pencil restriction.
`LeanPaper.Section4TransferComplete` assembles the result for every real exponent above lambda*rho/epsilon and the actual lattice-indexed family. `LeanPaper.Section4EffectiveBudget` separately defines a natural-number threshold using only rational ceilings, maxima and powers of 3; its theorem requires certified rational rate data and an explicit onset. Compilation and global-audit statuses are recorded by the runner, not this note.

The printed word “effectively computable” needs effective input data: an
unspecified “for all sufficiently large K” hypothesis does not provide a
computable onset. An existential approximation threshold can be proved from
those hypotheses; an algorithm for that threshold requires certified moduli
for both hypotheses (1) and (2). This distinction must remain explicit.

## 4.2: actual resultant

`LeanPaper.Section4Resultant` constructs the Sylvester resultant in Z and proves
its complex conjugate product with multiplicities. Coprimality over Q implies
nonvanishing. Irreducibility of the approximation polynomial plus nonvanishing
at one conjugate implies coprimality. For the actual primitive manuscript
polynomial that nonvanishing follows inside the certified operator-norm disk.
The exact Mahler bound is instantiated from pinned Mathlib.

`LeanPaper.Section4ConjugateBounds` proves the coefficient-height evaluation bound, isolates one conjugate, uses the Mahler product to bound all remaining conjugates, and combines the result with the nonzero integer lower bound. The complete printed asymptotic algebraic-approximation measure still needs the real exponent threshold and index-selection assembly, including the uniform interpretation of its limsup height hypothesis. No hypothesis asserting the resultant identity was introduced.

## 4.4–4.8: arithmetic source and a reversed inequality

On p. 16, the supplied manuscript states `A_M <= -2.32425` for its
`K=30n, N=3n, h=27n, M=100000` family. On p. 21 the proof of Theorem 4.6(2)
uses `A_M + 2.557199 >= -2.32425 + 2.55690`. This lower bound does not follow
from the preceding upper bound. The precise repair is to establish an
independent lower estimate, for example `A_M >= -2.32425`, or to replace the
height lower constant by one supported by a certified two-sided interval for
`A_M`. The arithmetic multiplier and family identity must be the same on both
sides. For example A=-3 satisfies the displayed upper bound but A+2.557199=-0.442801<0.23, so that implication fails even over rational numbers. This is a proof gap, not by itself a counterexample to the theorem.


A second direction error occurs on p. 21 in Proposition 4.8(1). Its proof
applies the cluster estimate `|r-zeta(5)| <= exp(-tau*K)` with `tau=11.411`
to every root, citing Theorem 4.4. The cited spectral-norm estimate instead
gives `|r-zeta(5)| >= exp(-11.411*K)`. The conditional conclusion for a root
already known to lie in a cluster remains valid, but the blanket exclusion
of all rational roots with denominator at most `exp(K/2251)` does not follow.
A correction must either add the upper-closeness premise to that exclusion,
or supply an independent arithmetic argument ruling out rational roots far
from zeta(5). This is an invalid inference in the supplied proof, not a
constructed counterexample to the particular polynomial family's conclusion.

Theorem 4.5 additionally needs the coupled-family arithmetic multiplier,
valuation loss and density comparison to preserve those rates. The finite
coupled-shift algebra in the baseline does not supply these estimates.

## External source retrieval (2026-10-25)

The requested investigation did locate the cited external source; it is not
classified as unavailable:

- Aabir Fauzan, *zeta(5) is irrational*, Zenodo record
  <https://zenodo.org/records/22826419>, v1, published 2026-09-17.
- <https://github.com/mo271/Zeta5/tree/7fe736760f4b96bfdb4334b68e3b3124ecbe10b0>
  has 253 Lean sources (about 30 MB), Apache-2.0. The inspected source pins
  Lean 4.34.0-rc1, Mathlib `f385f9fd18abed332ebcd3df239cb357e264aceb`, and
  PrimeNumberTheoremAnd `04d81b2a68ea3548b9990813fdc463c78511f412`.
  `Apery/MainEstimate.lean` uses the constructed family `K=40n`, `h=37n` and
  its own normalization. The `main_estimate` theorem states an existential
  positive decay rate, not the manuscript's `K=30n` constant `0.0004`.
- <https://github.com/domino14/zeta5/tree/3da8eb1b91f9a90a1c0b7959e845c060dbd16256>
  has 59 project Lean files (about 1.3 MB including a vendored PNT port).
  Its inspected toolchain is Lean 4.35.0-rc2 with matching Mathlib.
  `NOTES.md` records four off-main-line placeholders and a claimed audited
  main theorem; these claims have not been certified in this project's
  Lean 4.33 environment. Its parameters likewise differ from the manuscript.

README or printed axiom claims from those repositories are not kernel evidence
for this project. A legitimate import requires a pinned dependency closure,
local compilation and transitive auditing, followed by a proved identification
of any reused object. Their existence rules out calling the irrationality
conclusion an unavailable mathematical fact. It does not identify their
normalization, parameter family or numerical estimates with the manuscript.

The actual 476,337-byte Zenodo PDF was retrieved and text-extracted in this
session. Its equation (2.1), printed page 3, fixes `K=40n, N=3n, h=37n`,
`alpha=3/40, lambda=37/40`. Searches of the full extracted text found neither
`2.32425` nor `2.32380` nor the family `K=30n`. Thus the manuscript's p. 16
constants cannot be imported by citing the source alone: their dependence on
the changed parameter ratio must be proved. The original source's quantitative
conclusions for its own family remain distinct from the manuscript's family.

## Independent review of the Section 6.3(2) counterexample

The Section 4 agent independently inspected manuscript equation (5.3), the
precise subspace and normalization in Theorem 6.3(2), the certificate JSON,
and `tools/check_beukers_h4_counterexample.py`, and executed that checker
successfully. The negative combination has actual degree 25 (hence at most
27), vanishing order 8 at zero, and nonzero free Q-coordinates `(-t,1,0,0)`.
The four Q-vectors' final coordinates are the identity, proving independence;
multiplication by `x^8(1-x)^4` preserves it. Their twelve exact constraints
coincide with the printed Mellin moment conditions.

If `s_i` is the positive coefficient l1 norm of Q_i, the normalized basis
consists of `P_i/s_i`. The same negative vector P has coordinates
`(-t*s_0,s_1,0,0)` in this basis, so normalization does not remove the negative
quadratic direction. The diagonal and off-diagonal coefficients in the
checker agree with equation (5.3), including its positive difference quotient
and factor `1/6`.

The finite geometric identity for `1/(1+x)` gives exactly the displayed Euler
eta partial sum after integration against `(-log x)^6/720`. Its positive
remainder is bounded by `2^(-240)` because that logarithmic weight has total
mass one. Absolute summability justifies the eta/zeta relation
`eta(7)=(63/64)*zeta(7)`. Thus the exact rational enclosure and final negative
interval establish the counterexample without floating-point sign decisions.
This independent review agrees with the explicit scope label: rational
arithmetic plus an elementary analytic derivation, not a Lean kernel proof.
