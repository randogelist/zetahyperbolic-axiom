> **Final receiving verification:** All registered Lean sources discussed here are included in the 263-module [GitHub CI PASS](https://github.com/randogelist/zetahyperbolic-axiom/actions/runs/40339809027) at proof commit `cdcb1935aa73a7c7e65006c1c198d114e9dcc6db`, with a fresh all-project transitive axiom audit and negative regressions. See the [matching receipt](../../validation/github/20261026-prime/acceptance.json) and [current whole-result status](../FORMALIZATION_STATUS.md). References below to candidates, pending CI or failed runs describe historical investigation checkpoints; compilation does not extend the exact mathematical scope recorded here.

# Chapter 4 autonomous repair notes — 2026-10-26

Execution target: GitHub CI only. No local Lean, Lake, installation, compilation,
or axiom execution was performed. All new declarations below remain candidates
until the receiving commit compiles and passes the independent transitive audit.

## Implemented changes

### Actual polynomial factor degree bounds (4.8(2))

- File: `src/LeanPaper/Section4FactorDegreeBounds.lean`.
- Dependency: `LeanPaper.Section4Resultant` (and its retained exact norm disk).
- Original gap: the retained 4.8 source proved only inequalities for a caller's
  finite list of root distances. It did not derive the logarithmic degree
  inequalities for a genuine polynomial/divisor.
- Correction: construct the actual complex root factorization using algebraic
  closedness; retain root multiplicities; derive nonvanishing from positive
  root separation; prove logarithmic lower and upper degree bounds. Then
  transfer the exact inverse-operator-norm disk to every actual root of a
  genuine integer-polynomial divisor of the manuscript primitive polynomial.
- Public endpoints:
  `polynomial_log_degree_lower`, `polynomial_log_degree_upper`,
  `manuscript_divisor_root_separation`,
  `manuscript_divisor_log_degree_lower`,
  `manuscript_divisor_log_degree_upper`.
- Exact scope: the numerical norm estimate remains an explicit quantitative
  input. The upper degree bound additionally retains a separate upper cluster
  bound. No lower separation bound is inverted into an upper-closeness claim.

### Exact straddling-root separation (4.7(2))

- Same file, endpoints `manuscript_straddling_root_gap` and
  `manuscript_straddling_root_gap_of_norm_bound`.
- Original gap: the actual spectrum already had an exact norm disk, while the
  straddling-root clause was not assembled as an actual primitive-polynomial
  endpoint.
- Correction: add the distances on the two sides of the actual zeta center;
  derive the exact gap `2 / norm(whitened pencil)` unconditionally under the
  structural admissibility and root/straddling hypotheses. A separately proved
  norm upper bound gives the exponential version with the correct direction.
- This closes the finite straddling geometry, not the outstanding family-wide
  numerical bound or same-factor root separation.

### Actual divisor heights for the same-factor route (4.7(3))

- File: `src/LeanPaper/Section4FactorHeight.lean`.
- Dependencies: `LeanPaper.Section4ConjugateBounds`,
  `Mathlib.Data.Nat.Choose.Bounds`.
- Original gap: the finite separation route had no proved height estimate for
  actual divisors of the manuscript polynomial. Assuming such a bound would
  only move the missing arithmetic into a premise.
- Correction: the actual integer cofactor has Mahler measure at least one
  because its leading coefficient is a nonzero integer. Apply Mathlib's
  Mignotte coefficient bound and Landau inequality to that cofactor, then
  bound the binomial coefficient and divisor degree. This proves
  `H(F) <= 2^deg(P) * sqrt(deg(P)+1) * H(P)` for every divisor `F` of every
  nonzero integer polynomial `P`, with an actual manuscript specialization.
- Public endpoints: `integer_mahler_one_le`,
  `integer_divisor_coefficient_bound`, `integer_divisor_height_bound`,
  `manuscript_divisor_height_bound`.
- Remaining work: the actual parent's numerical quadratic height rate and a
  root separation estimate for the same irreducible factor are still needed
  to derive the paper's quantitative asymptotic separation assertion.

### Actual closest-root existence from center decay (4.7(1))

- File: `src/LeanPaper/Section4ClosestRoot.lean`.
- Dependency: `LeanPaper.Section4ConjugateBounds`.
- Original gap: the printed closest-root implication was not assembled for
  actual roots from the center value of the primitive integer polynomial.
- Correction: construct the complex root factorization with multiplicities.
  If every root lay outside the proposed disk, its product would be strictly
  larger than the center-value bound, contradicting the integer leading
  coefficient lower bound. The actual manuscript root is also proved real.
- Public endpoints: `polynomial_close_root`, `integer_polynomial_close_root`,
  `manuscript_real_close_root`.
- Exact endpoint: if the actual primitive center value is at most
  `exp(-h*t)`, an actual real root lies within `exp(-t)` of the zeta center.
  The concrete family-wide estimate on the actual center value remains to be
  established before inserting the printed numerical rate.

### Cluster-only denominator exclusion, including small denominators (4.8(1))

- File: `src/LeanPaper/Section4RationalCluster.lean`.
- Dependencies: `LeanPaper.Section4TransferComplete`,
  `Mathlib.Algebra.Order.Floor.Ring`.
- Original gap: the paper improperly applied a lower root-separation estimate
  as an upper cluster radius. The valid cluster-only implication also required
  handling all denominators below the onset of the approximation measure.
- Correction: retain actual upper closeness; prove irrationality from any
  eventual real-exponent rational measure by rescaling rational denominators;
  construct a positive fixed-denominator gap from the two integers surrounding
  `b*xi`; induct over the denominator bound; let the exponential cluster radius
  fall below that positive gap. The large-denominator logarithmic comparison
  then applies uniformly to **every** positive denominator.
- Public endpoints: `irrational_of_real_measure`,
  `fixed_denominator_separation`, `bounded_denominator_separation`,
  `cluster_denominator_lower`, `eventual_rational_cluster_exclusion`.
- Exact endpoint: for `mu>0`, `tau>0` and the stated eventual measure, eventually
  in natural `K`, every `a : Z`, `b : N`, `b>0` with
  `abs(xi-a/b) <= exp(-tau*K)` satisfies `exp((tau/mu)*K) < b`.
  No roots outside the cluster are excluded by this theorem.

### Newly identified exponent-rounding error in 4.8(1)

- Endpoint `Section4RationalCluster.paper_cluster_denominator_arithmetic`.
- The proof's final inference remains numerically invalid even if its earlier
  upper-closeness premise were supplied: exactly
  `1/2252 < (11411/1000)/25687 < 1/2251`.
  In particular, `11.411*2251=25686.161 < 25687`.
- Repair: keep the exact rate `tau/mu`, or use the supported weaker rate
  `1/2252` when `tau=11.411`, `mu=25687`. This does not repair the missing
  all-root upper-closeness premise.

### Formal diagnostic for the reversed arithmetic-rate inference in 4.6

- Endpoint `Section4FactorDegreeBounds.paper_upper_rate_counterexample`.
- Exact rational witness `A=-3` satisfies the quoted upper premise
  `A <= -2.32425` but `A+2.557199 < 0.23`.
- It refutes the implication used in the proof, not the actual family theorem.
  An independent lower bound or certified two-sided interval is still required.

## Review of every Chapter 4 numbered result

| Item | Review / action | Remaining exact obstacle and repair |
| --- | --- | --- |
| 4.1 | Read full transfer/index-selection/complex-comparison/effective-budget sources and original paper statement. Existing existential transfer is complete; explicit effective thresholds already have rational-rate/onset premises. | The printed claim of an effectively computable onset does not follow from unspecified eventual hypotheses. Keep the existential statement or supply effective moduli; concrete family bounds belong to 4.4/4.5. |
| 4.2 | Read resultant, conjugate bounds, limsup, lattice and algebraic-height construction. `proposition_4_2_algebraic_numbers` constructs the primitive integer minimal polynomial, exact extension degree and naive height. No mathematical wrapper gap remains in that conditional statement. | Receiving full CI + transitive audit required. Do not demand concrete zeta bounds: those are hypotheses of the printed transfer criterion itself. Source integration alone is not a pass. |
| 4.3 | Retained full integer-polynomial complex p-adic disk endpoint and actual manuscript bridge. | No mathematical change needed for the original exact proposition; no family valuation or p-adic zeta claim is added. |
| 4.4 | Inspected printed proof and the available transfer/actual norm-disk infrastructure; checked prior external-source comparison. | Need actual `K=30n,N=3n,h=27n` denominator multiplier, integral decay, and certified uniform norm rate 11.411 with effective onsets. The previously investigated external proof uses `K=40n,h=37n` and a different normalization/toolchain; its claims do not provide the paper's exact rates. A rigorous parameter-identification and quantitative estimate port is required. |
| 4.5 | Reviewed stated coupled-weight result, retained linear-family/shift transfer infrastructure and available scope reports. | Need the actual coupled positive density cone, cancellation/valuation loss and quantitative denominator/decay estimates uniformly in permitted coefficients. Finite shifted matrices do not identify the infinite measure or its rates. |
| 4.6 | Read finite leading coefficient barrier and actual manuscript determinant bridge; added exact rational counterexample to the invalid rate inference. | The constants 0.23310,3.73980,10.27 and the arithmetic lower rate require actual asymptotic determinant/height estimates. Existing upper multiplier rate cannot serve as a lower rate. |
| 4.7 | Read cap/average counting proof, actual spectral-exponent bridge and printed clauses; implemented exact actual straddling-root gap, its norm-bound transfer, coefficient/height bounds for genuine integer divisors, and actual real closest-root existence from center decay. | Numerical rates still require actual uniform cap/average/center-decay estimates; same-factor separation needs the parent's numerical height asymptotic and a root separation inequality. Root mean-to-matrix-trace identification is also separate from the finite counting argument. |
| 4.8 | Implemented full conditional cluster-only denominator mechanism (including all small denominators) and actual-divisor logarithmic degree bounds. Identified and formalized the additional exponent-rounding error. | Blanket exclusion of all rational roots still lacks an independent argument for roots outside the cluster. Numerical instantiation requires 4.4/4.6 rates; new generic implications must not be labelled proof of that unqualified printed statement. |

## Verification handoff

- All four modules have explicit `#print axioms` calls for all 21 public endpoints;
  root agent must include the modules in `modules.txt`, Lake roots and the
  all-project `KernelAudit` registry.
- No placeholders, new axioms, proof-field assumptions, changed theorem
  definitions or weakened existing declarations were introduced.
- Source/manual checks are not Lean acceptance. Append exact CI SHA/run and
  final audit outcome after the receiving build is inspected.

### Receiving CI repair, run 40318924083

- Commit `96ffaabc6051e7ebbf66b3f86aeea91cb7602111`: both
  `Section4FactorDegreeBounds` and `Section4FactorHeight` completed fresh CI
  compilation. The project-wide audit did not run because other modules failed.
- `Section4RationalCluster` exposed a Lean lexer collision between the closing
  absolute-value bar and multiplication (`|*`), a redundant `ring` after a
  completed `field_simp`, and an unexpanded function composition in the
  exponential-limit transfer. Added whitespace, removed the redundant tactic,
  and explicitly simplified `Function.comp_def`. Statements are unchanged.
- Checked the queued `Section4ClosestRoot` source for these patterns; none
  occurs. Corrected cluster proof awaits the next receiving CI run.

### Receiving CI repair, run 40320889232

- `Section4RationalCluster` completed compilation after the preceding repairs.
- `Section4ClosestRoot`'s generic complex and integer-polynomial endpoints
  elaborated without nonstandard axioms. The actual manuscript wrapper failed
  because `simp only` did not unfold the `Polynomial.IsRoot` predicate returned
  by `mem_roots` before applying `eval_map`.
- Correction: first give the root fact the explicit evaluation-equals-zero
  type, then transport it with `eval_map`. This is the same transport pattern
  already compiled in `Section4FactorDegreeBounds`; no hypotheses or conclusion
  changed. The repaired wrapper awaits the next receiving run.
