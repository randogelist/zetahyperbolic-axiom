# Zetahyperbolic — persistent missing-paper tracker

**Repository:** [`randogelist/zetahyperbolic-axiom`](https://github.com/randogelist/zetahyperbolic-axiom)  
**Branch:** `persistent/zetahyperbolic-paper-gap-tracker`  
**Purpose:** permanently track every unproved, partially completed or mathematically incorrect item in the original 52-page Zetahyperbolic manuscript, together with the exact Lean proof needed to close it. **`snditeration` is a cross-repository source of reusable proofs, not the repository being modified.**

**Full research inventory:** [45-item missing-pieces register and targeted proof agenda](docs/PERSISTENT_PAPER_GAPS.md).  
**Original proof repository:** [`main` README](https://github.com/randogelist/zetahyperbolic-axiom/blob/86ca99a23d65cde4880a9005a49076c43e7bc968/README.md). This tracking branch deliberately does not edit active Lean proof modules.

## 1. Established proof tiers

The **YOU_ARE_GOODWORKFLOWFRONTIER** tierlist (from [WORKFLOW.txt](WORKFLOW.txt)) is:

| Marker | Tier | Definition |
|:---:|:---|:---|
| `!` | **B-Tier** | On-paper mathematical derivation, conditional on reasoning; not yet Lean-verified. |
| `!!` | **A-Tier** | The exact statement parses, elaborates and compiles in Lean; its **transitive axiom audit** passes with no `sorryAx`, hidden axioms or unstated hypotheses. An A-Tier *conditional theorem* proves only the stated implication. |
| `!!!` | **Formal closure** | A-Tier conditional chain reduces the target to acceptance of **finite witness data** by a terminating checker; no actual accepted witness yet. |
| `!!!!` | **S-Tier** | Concrete finite witness data pass the checker, and the axiom-audited downstream Lean transfer to the final claim passes. |

**Partial proof:** `!!` may already apply to individual mathematical components, **not** to the whole printed theorem. `Partially formalized`, `Not formalized` and `Blocked` describe manuscript coverage, **not** extra proof tiers. A false literal claim remains blocked even if a corrected proposition is fully A-Tier. No manuscript-wide `!!!` or `!!!!` certificate is asserted.

## 2. All 45 manuscript items — immediately after the tier definitions

The ~~struck-through titles~~ are the **seven complete literal A-Tier paper results**. A `✓` after any other item marks **only its already-proved subclaim**, not the original complete theorem. `BLOCKED` denotes a false printed clause requiring a corrected mathematical statement. No complete manuscript item currently reaches `!!!` or `!!!!`.

| Paper item | Original manuscript statement | Whole-item proof gate | Already crossed / exact scope |
|:---|:---|:---|:---|
| 2.2 | ~~Rational functional pullback~~ | **!! RESOLVED** | ✓ Actual RatFunc pullback and μ functional |
| 2.3 | ~~Reflection and difference identities for Tau~~ | **!! RESOLVED** | ✓ Full τ reflection, finite difference, derivative bridge |
| 2.4 | ~~Canonical basis invariance~~ | **!! RESOLVED** | ✓ Arbitrary-basis primitive invariance |
| 2.5 | ~~Lagrange pole diagonalization~~ | **!! RESOLVED** | ✓ Actual Lagrange rational-functional diagonalization |
| 3.1 | ~~Universal hyperbolicity and zero-free disk~~ | **!! RESOLVED** | ✓ Actual primitive hyperbolicity; sharp norm disk |
| 3.2 | Continuous hyperbolic pencil for all real s > 1 | **BLOCKED** literal claim | ✓ Corrected real-s pencil; printed normalization false |
| 3.3 | Total positivity, leading sign, universal signature | Partial — A-Tier subproofs | ✓ Actual signature; ζ(5) sign/root counts in snditeration |
| 3.4 | Root interlacing and Dodgson condensation | **BLOCKED** literal claim | ✓ Rank-aware root reality; all-rank Dodgson |
| 3.5 | Stieltjes J-fraction from interlacing roots | **BLOCKED** literal claim | ✓ Actual rank-one counterexample and corrected fraction |
| 3.6 | Stieltjes reciprocal-root power sums | **BLOCKED** literal claim | ✓ Entire corrected finite-rank reciprocal corollary |
| 3.7 | Turanian non-negativity and Newton log-concavity | Partial — A-Tier subproofs | ✓ All-derivative Turán and centered strict Newton |
| 3.8 | Christoffel-Darboux pole representation and Jacobi derivative | Partial — A-Tier subproofs | ✓ Actual finite pole characteristic spectrum |
| 3.9 | Hurwitz and Dirichlet hyperbolicity | Partial — A-Tier subproofs | ✓ Finite Fekete kernels and shifted-pole spectrum |
| 4.1 | Spectral irrationality measure criterion | Partial — A-Tier subproofs | ✓ Conditional rational transfer, effective-onset version |
| 4.2 | Transfer for algebraic approximations | Partial — A-Tier subproofs | ✓ Integer resultants and limsup algebraic transfer |
| 4.3 | ~~Ultrametric zero-free disk~~ | **!! RESOLVED** | ✓ Complete ultrametric zero-free disk |
| 4.4 | Spectral bound and irrationality measure for zeta(5) | Partial — A-Tier subproofs | ✓ Norm–root gap and arithmetic rate comparisons *only* |
| 4.5 | Irrationality and measure for b*zeta(5)+a*zeta(3) | Partial — A-Tier subproofs | ✓ Finite coupled-shift algebra *only* |
| 4.6 | Determinant bounds and coefficient heights | Partial — A-Tier subproofs | ✓ Finite determinant/leading-coefficient identity |
| 4.7 | Root collapse and separation | Partial — A-Tier subproofs | ✓ Finite cluster-count implication |
| 4.8 | Rational root exclusion and cluster degree bounds | Partial — A-Tier subproofs | ✓ Conditional factor-distance inequalities |
| 5.1 | Two-variable Beukers measure for zeta(7) | Partial — A-Tier subproofs | ✓ Finite coefficient/slope Gram identity |
| 5.2 | Dual hyperbolicity and Krein decomposition | Partial — A-Tier subproofs | ✓ Real roots of finite dual pencil; dimension obstruction |
| 5.3 | Beukers measure and dual pencil for beta(4) | Partial — A-Tier subproofs | ✓ Finite β weighted-Gram models only |
| 5.4 | ~~Higher-zeta cancellation on even pole pairs~~ | **!! RESOLVED** | ✓ Exact even-pole τ cancellation |
| 5.6 | Weight-seven prime-sum evaluation and pole refinement | Open — no full item | ✓ Rational sign check, **not** integral evaluation |
| 5.7 | Double-pole determinant for 1,zeta(5),zeta(6) | Open — no full item | — actual double-pole valuation open |
| 6.1 | Divided-difference valuation and intrinsic p^-6 barrier | Open — no full item | — p-adic divided-difference valuation open |
| 6.2 | Simultaneous weight-(6,7) Beukers functional | Partial — A-Tier subproofs | ✓ Exact finite harmonic common denominator |
| 6.3 | q-adic nonvanishing and positive-cone approximations | **BLOCKED** literal claim | ⚠ Printed cone refuted by non-Lean rational certificate |
| 6.4 | Character-Vandermonde sign cancellation and beta hyperbolicity | Partial — A-Tier subproofs | ✓ Oriented finite character/Vandermonde sign |
| 6.5 | q-adic nonvanishing at zero | Open — no full item | — q-adic nonvanishing open |
| 6.6 | Generalized multi-weight positive-definite pencil | Partial — A-Tier subproofs | ✓ Finite multiweight anchored cone |
| 6.7 | Universal multi-weight Beukers Krein decomposition | Open — no full item | — infinite Krein measure open |
| 6.8 | Three-term linear-independence cone | Open — no full item | — full 3-term arithmetic linear forms open |
| 6.9 | Triple-pole and multi-weight determinants | Partial — A-Tier subproofs | ✓ Corrected finite triple-pole Hermite algebra |
| 6.10 | Potential-gap identity and quadratic derivative growth | Partial — A-Tier subproofs | ✓ Finite determinant identities |
| 6.11 | Distribution growth and 2-adic quotient obstruction | Open — no full item | ✓ Odd-square scaling and parity identities |
| 6.12 | Full-dimension sign-flip positivity and q-adic nonvanishing | Open — no full item | — full sign-flip pencil open |
| 6.13 | Central-factorial secant differential identity | **BLOCKED** literal claim | ✓ Finite secant identity and corrected sign |
| 6.14 | Even-pole cosh scaling and coupled pencils | Open — no full item | — even-pole cosh estimates open |
| 6.15 | Arithmetic transcendence, positive measure and rank-one law | **BLOCKED** literal claim | ✓ Independent odd-beta transcendence and independence |
| 6.16 | Generalized multi-weight Zeta-Beta pencil | Open — no full item | — actual combined infinite density open |
| 6.17 | Universal two-variable Zeta-Beta pencil | Partial — A-Tier subproofs | ✓ Counterexamples to local harmonic pole argument |
| 6.18 | Principal-minor 2-adic integrality and dyadic heights | Partial — A-Tier subproofs | ✓ Exact quotient threshold and degree |

**Outside these 45 numbered results:** the order-s moment-functional foundation in **Definition 2.1** is constructed and audited. It is not silently counted as an eighth completed item.

[See the complete, source-linked 45-item residual proof register](docs/PERSISTENT_PAPER_GAPS.md) and the [six-round source/CI audit](docs/MULTIROUND_RESOLUTION_AUDIT.md) for hypotheses, literal errors, cross-branch receipt distinctions and remaining theorem statements.

## 3. Cross-branch resolutions already available

The audit of passing `zetahyperbolic-axiom` and `snditeration` branches also confirmed these **resolved subproofs** (not complete parent statements):

- **3.3:** Actual intrinsic signature locally; **ζ(5) primitive sign and exact root-side counts** already passed in [`snditeration/main`](https://github.com/randogelist/snditeration/actions/runs/40186793090). Mixed minors/Carleman are not yet closed.
- **3.4, 3.6, 3.7:** All-rank Dodgson + rank-sensitive principal reality, the **entire corrected** finite-rank reciprocal corollary, and actual all-derivative Turán/strict Newton criteria have already been audited locally.
- **4.1–4.2:** Conditional real/lattice transfer, a computable denominator threshold **given effective rate inputs**, integer resultants and conditional algebraic transfer are proved. The concrete `K=30n` prime/decay estimates are still absent.
- **5.2, 6.13, 6.15:** Finite dual real-root spectra, corrected central-factorial differential identities, and odd Dirichlet-beta transcendence/finite independence are already proved components.

Exact theorem names, sources, proof scope and remaining bridges are in the [45-item crossed-off register](docs/PERSISTENT_PAPER_GAPS.md). The `snditeration` broad continuation branch **failed CI** and supplies candidates only. This tracker revision modifies no Lean source and claims no new compiler result.

## 4. Verified mathematical baseline (25 October 2026)

**219 Lean modules passed compilation and independent transitive axiom auditing**, covering 3,135 declarations, including 2,489 kernel theorem declarations (private/generated included). [Passing build](https://github.com/randogelist/zetahyperbolic-axiom/actions/runs/40188664869). The corresponding Leaned Paper is substantially advanced mathematically, with real rational-moment identities, positive actual Gram pencils, unconditional hyperbolicity and zero-free disks, spectral and strict Newton/reciprocal-moment results, algebraic transfer, and independent odd-beta transcendence.

Printed manuscript classification: **7 complete**, **21 partial**, **10 not formalized**, **7 literally blocked**. The 7 fully proved numbered results are **2.2, 2.3, 2.4, 2.5, 3.1, 4.3 and 5.4**. These numbers count whole paper statements, **not** Lean declarations. Source: [audited 45-result manuscript status](docs/FORMALIZATION_STATUS.md).

## 5. Missing-work priorities

| Workstream | Necessary closure |
|:---|:---|
| **F2 — ζ(5) quantitative result** | Actual `K=30n,N=3n` denominator/integrality and `exp(-K²/2500)` decay, genuine spectral `11.411` exponent, effective transfer to the printed irrationality measure `25687`. Fauzan's cited `K=40n,N=3n` estimates cannot simply be reused. |
| **F1 — spectral/analytic** | 3.3 mixed-minor strict positivity + Carleman, 3.4 corrected rank-aware interlacing, 3.5–3.6 normalized finite-rank replacements, 3.8 genuine Christoffel–Darboux/Laplace bridge, 3.9 Hurwitz/Dirichlet integral pencil. |
| **F3 — ζ(7), Beukers, β(4)** | Actual double-integral moments and infinite Krein tails, 5.6 outer prime sum `453803/288000` and corrected local pole gain, 5.7 q-adic Hermite blocks. **6.3(2)'s printed cone is false at h=4** and requires a new tail-controlled construction. |
| **F4 — multiweight and prime arithmetic** | Actual combined zeta–beta density, q-/2-adic local nonvanishing and height estimates, 6.13 secant-series sign correction, 6.15 exterior asymptotic repair, 6.17 harmonic pole-class repair. |

**Key diagnostic:** the paper's 4.6 lower height bound uses an upper bound in the wrong direction; 4.8's claimed global rational-root exclusion similarly applies a lower root-gap as an upper bound. These are *unproved paper inferences*, not reasons to discard the certified structural mathematics.

## 6. Persistent tracking procedure

- Work from the actual manuscript and the existing [machine-readable item ledger](docs/formalization_status.json), preserve all 45 item IDs, and freeze unchanged certified Lean modules.
- For each improvement record **the literal paper claim, exact constructed function/matrix, fully qualified Lean theorem, audited commit/runner receipt, retained hypotheses, and next open endpoint**.
- Keep **corrected theorem**, **failed printed claim**, **conditional implication**, and **unconditional proof** distinct. No guessed compiler PASS or imported assertions as axioms.
- Pull useful statements from [`snditeration`](https://github.com/randogelist/snditeration) only with pinned source and a proved translation bridge. Its main checkpoint reports **846 audited theorem declarations**; its wider continuation branch currently has failed CI, so these extra files are candidates only.
- The standard workflow remains `YOU_ARE_GOODWORKFLOWFRONTIER`, `LEAN_ANCHORINGS`, Lean 4.33.0 with cached pinned Mathlib. A documentation commit to this branch is **not** a new Lean build or native Windows audit.

**Status: full manuscript remains open.** No unproved claim of ζ(5)/ζ(7) irrationality from the paper's explicit family, finite-witness admission or whole-paper completion is made.
