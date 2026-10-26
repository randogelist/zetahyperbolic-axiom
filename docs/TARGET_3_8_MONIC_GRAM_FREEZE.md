# Frozen target 3.8 — monic Gram orthogonal-basis prelude

**Anchor:** `ZETA_HYPERBOLIC_TARGET_3_8_MONIC_GRAM_1`  
**Tag:** `_construction` (unverified receiving compilation).  
**Branch:** `feat/gwf-target-38-monic-orthogonal-v0_1_0`  
**Receiving baseline:** `main@9536243c136b88a9a69e921ada7bae4cba6b190c`, containing 223 accepted modules; Lean 4.33.0; Mathlib `db584cd6d46c92f209a44c0f1c829460d327499d`.

## Donor and target boundary

Donor: [snditeration/ChristoffelDarboux.lean@0cee4ea](https://github.com/randogelist/snditeration/blob/0cee4ea2e32b1f476488f92b476c4eb224285160/Zetahyperbolic/Section3/ChristoffelDarboux.lean), Git blob `2a004aecbf3e21aca754af7b7afbaef7f60fc3bd`, **FAILED** in [donor CI 40188938699](https://github.com/randogelist/snditeration/actions/runs/40188938699). Original full module contains several unsolved LDL/inverse-kernel proofs and a wrong/missing `Matrix.diagonal_mulVec` reference. It does **not** provide an axiom-audited Christoffel–Darboux proof.

The receiving file `src/LeanPaper/Section3MonicOrthogonal.lean` (Git blob `7638ff43138e47a73e76c64652e887cc87955954`) ports **only the seven generic pre-error declarations** from donor: `lower_diagonal_ne_zero`, `diagonal_positive`, `squaredNorm_positive`, `monicPolynomial_coeff_self`, `monicPolynomial_coeff_above`, `monicPolynomial_natDegree`, `monicPolynomial_monic`, plus definitions `orthogonalCoefficients`, `monicPolynomial`, `squaredNorm`. It adds three **actual-manuscript wrappers**: `actualMonicPolynomial_monic`, `actualMonicPolynomial_degree`, `actualSquaredNorm_positive`, using the already accepted `ManuscriptChain.GRAM_POSITIVE`; no additional analytic positivity assumption is introduced.

**Exact mathematical scope:** Given the concrete odd-zeta positive Gram `G`, every `i : Fin p.h` has an explicitly constructed **monic** degree-`i` polynomial with a **positive LDL-normalization scalar**. This is an essential *finite Gram basis prelude* of manuscript 3.8, not an assertion that these polynomials have yet been proved orthogonal against the actual measure.

## Still open

1. Prove coefficient-matrix Gram orthogonality and exact integral squared-norm identification for the actual measure.
2. Prove the inverse-Gram reproducing kernel `K_n(t,u)` identity (the previously failing donor lemma), then connect to the original pole/whitened spectral kernel.
3. Prove justified Laplace deformation differentiation under the integral in 3.8(2).
4. Do not confuse generic monic LDL construction with a full **Christoffel–Darboux** identity, nor use this to promote printed 3.8.

## CI and merge gate

- This branch adds precisely one new mathematical source file, this freeze receipt, and one registration each in `modules.txt`, `lakefile.toml` and `LeanPaper.KernelAudit.lean`.
- Reuse pinned Mathlib and the frozen 223 mathematical modules. Initial CI must pass a full **224-module** Lean 4.33.0 build, then print `AXIOM_AUDIT_ACCEPTED=ALL_PROJECT_DECLARATIONS`; allowed foundational axioms `propext`, `Quot.sound`, `Classical.choice` only.
- Before merging, rebase/reconcile onto the **then-current** `main` and pass the complete *combined* build and axiom gate after any earlier concurrent PR merges. Only then mark ready and merge; until then **DRAFT**.
- No other mathematical target belongs to this branch. Successful merge credits only an exact **A-Tier subclaim**, not the full 3.8 or another manuscript item. No new raw finite-witness checker is asserted.
