# Frozen target 5.1 — finite off-diagonal Beukers kernel identity

**Anchor:** `ZETA_HYPERBOLIC_TARGET_5_1_OFFDIAGONAL_KERNEL_1`  
**Status:** `_construction`; one target only, no accepted compilation yet.  
**Receiving baseline:** `zetahyperbolic-axiom/main@54136b39ec280b200c108ee48e80a5c247b1fa6b`, with 222 existing Lean modules and three previously merged standalone donor components (6.17, 6.16, 4.2). Compiler Lean 4.33.0 and pinned Mathlib `db584cd6d46c92f209a44c0f1c829460d327499d`.  
**New source:** `src/LeanPaper/BeukersOffDiagonalKernel.lean`, Git blob `3b083ed855d2635a7b6355bdcd3528df45fecb25`.

## Exact mathematical claim and why it is useful

The original paper's Theorem 5.1 identifies the diagonal moment with `ζ(7)-H_r^(7)`, and **claims off-diagonal moments are rational**. The previously staged [two-variable analytic donor on PR #7](https://github.com/randogelist/zetahyperbolic-axiom/pull/7) produces a geometric-series/Mellin expression before this final rational simplification. The present **independent finite algebra** addresses precisely the six-factor arithmetic step of that expression.

For nonzero rational `a,b`, define

```text
K_6(a,b) = 1/(a b^6) + 1/(a^2 b^5) + ... + 1/(a^6 b)
(b-a) K_6(a,b) = a^(-6) - b^(-6)
```

On the manuscript grid `a=r+n+1`, `b=t+n+1`, the gap is `b-a=t-r`, *independent of n*. Therefore, for every finite cutoff `N`,

```text
(t-r) Σ_(n<N) K_6(r+n+1,t+n+1)
   = Σ_(n<N) [ (r+n+1)^(-6) - (t+n+1)^(-6) ] .
```

The new source formally states `sixKernel_eq_sum`, `divided_difference`, `shifted_divided_difference`, and `finiteKernelSum_divided_difference`. The underlying rational identity was also independently checked algebraically before staging; **Lean proof admission still requires recipient CI**.

## Still-open original-paper bridge

This module does **not** prove that the Beukers `dΩ₇` two-variable integral equals the analytic geometric-series/Mellin expression. Nor does it pass to an infinite sum or prove off-diagonal rational moments. Those further steps require (1) a successful, axiom-clean and original-data-matched PR #7; (2) summability/Fubini permission; (3) a rigorous `ζ(6)` tail-difference/harmonic telescoping argument; (4) equality with the receiving paper's rational `dualConstant 7 r t`. Exact denominator estimates already exist in `LeanPaper.BeukersDenominator`; do not assume the current finite calculation alone establishes them for the analytic integral.

## Separate merge gate

- This branch introduces **one mathematical source file** and only the three necessary build/audit inventory changes (`modules.txt`, `lakefile.toml`, `LeanPaper.KernelAudit.lean`), plus this receipt.
- The independent branch's 223-module Lean 4.33.0 CI and complete all-declaration axiom gate must pass; permitted axioms only `propext`, `Quot.sound`, and `Classical.choice`.
- This is intentionally a **draft PR** while earlier frozen merge targets are pending. It must be reconciled against the latest accepted `main` and recompiled/audited with *all* intervening accepted sources before being eligible for merge.
- For a claim about the actual analytic off-diagonal moments, the stronger PR #7 dependency must independently pass and be merged before the final identification can be promoted. This finite lemma may be merged as a helper without claiming that identification.
- Preserve the 45-item printed manuscript status at **7 fully proved** until exact remaining clauses are proved. No new rationality/transcendence result is asserted for ζ(7).

## Receipt fields

Frozen branch: `feat/gwf-target-51-beukers-offdiag-kernel-v0_1_0`. PR, isolated CI run, full combined CI run, final admitted merge SHA, and qualified theorem names must be recorded only after verified GitHub evidence. Never label `!!!!` or `!!!` based solely on a generic finite algebra lemma.
