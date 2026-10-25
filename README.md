# Zetahyperbolic — Leaned Paper

Canonical source-level formalization branch of the 52-page manuscript *Spectral Theory and Diophantine Bounds for Hankel Determinants of Odd Zeta Values* (21 October 2026).

**Mission:** build the full Leaned Paper from the IRRATIONALITY project's sources and compatible Lean bases in cross-branch repositories. Research inputs may accelerate derivation, discovery and source generation, but never count as proven until statement alignment, Lean compilation and transitive-axiom audit.

**Source provenance:** the Section 2 Lean files and build configuration here are byte-for-byte from [snditeration](https://github.com/randogelist/snditeration/commit/ef9beea7cb3f58a4047aed7e5a2974dfb94fba30); [upstream CI succeeded](https://github.com/randogelist/snditeration/actions/runs/40170263068). User-native Windows Lean 4.33.0 + LEAN_ANCHORINGS verification is a separate gate. This foundation **does not** prove ζ(5) irrationality or the full paper.

## Implemented algebraic foundations
- Definition 2.1 rational moments and affine pencil data.
- Theorem 2.4 rational change-of-basis and primitive normalization.
- Theorem 2.5 pole Vandermonde slope factorization and diagonal X-dependence.

## Open targets
Lemmas 2.2–2.3 (full rational pullback, reflection and difference); actual positive integral Gram representation (3.2), Theorem 3.1 real spectral transfer, and later spectral, analytic and arithmetic endpoints of Sections 4–6.

Lean 4.33.0; Mathlib reference commit `db584cd6d46c92f209a44c0f1c829460d327499d`. Use Github CI to compile from pinned dependencies. For accelerated offline Windows native compilation, use the GOODWORKFLOWFRONTIER construction ZIP with its single `run.cmd` and existing cached Mathlib.

See [ledger](docs/FORMALIZATION_LEDGER.md) and [cross-branch source policy](docs/CROSS_BRANCH_POLICY.md).
