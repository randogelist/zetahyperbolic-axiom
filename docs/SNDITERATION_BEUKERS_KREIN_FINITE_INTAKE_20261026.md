# snditeration finite Beukers Krein integration — frozen source scope

**Status:** `_construction`; source staged, NOT merged. Destination: `randogelist/zetahyperbolic-axiom/main`.

This is a dependent, source-preserving extension of [Theorem 5.1 integration PR #28](https://github.com/randogelist/zetahyperbolic-axiom/pull/28), exact source parent `762f8cf640b652099cf2c05eb5c7c765b198083b`. PR #28 itself depends on receiving PR #23. Neither is yet verified on the final receiving source HEAD. Do not merge this branch until 5.1 and its source fingerprints are accepted.

## Frozen donor and exact source
- Donor `randogelist/snditeration@372deda8edc77bba6312b8f80137e00e1b75e74f`.
- [Lean 4.33.0 successful donor audit, CI 40271072845](https://github.com/randogelist/snditeration/actions/runs/40271072845), with six exact target axiom checks and allowed foundational axioms only.
- `src/LeanPaper/BeukersKreinMonomialActual.lean` from `Zetahyperbolic/Section5/KreinMonomial.lean`; immutable original Git blob `9f4e12d26e12e55ad1ab42603d40706eefa88ed7`. Only the import line changes; every theorem statement and proof body is otherwise identical.
- `src/LeanPaper/BeukersKreinPolynomialActual.lean` from `Zetahyperbolic/Section5/KreinPolynomial.lean`; immutable original Git blob `f420c1fdcd638724c1aa0be1c46957c023d6d172`. Only the import line changes; every theorem statement and proof body is otherwise identical.

## Mathematical scope — actual partial Theorem 5.2(2)
- Actual ζ(7) Beukers **monomial** moments equal a convergent 1/1440-normalized signed Krein-channel expression, without replacing the genuine measure with formal coefficients.
- Finite rational polynomial coefficient bilinear and quadratic extensions are established from those exact monomial moments.
- Complete printed Theorem 5.2(2), for *arbitrary f∈L²(0,1)*, is **not** proved: polynomial-product double-integral transport, joint continuity, convergence and infinite-mode tail control remain explicit.
- No positive/negative all-dimensional polynomial cone conclusion (Theorem 5.2(3)); no ζ(7) irrationality or overall manuscript closure.

## Receiving integration gate
- This branch adds exactly **two** Lean proof modules and changes only `modules.txt`, `lakefile.toml`, `src/LeanPaper/KernelAudit.lean`, and this note. It keeps all inherited mathematics unchanged.
- Expected candidate: **230 modules** inclusive of KernelAudit. Need exact final source/Mathlib-compatible Lean 4.33.0 CI build plus independent complete axiom audit `AXIOM_AUDIT_ACCEPTED=ALL_PROJECT_DECLARATIONS`, with only `propext`, `Quot.sound`, `Classical.choice`, no `sorryAx`.
- Any rebase, changed dependency, source fingerprint, or toolchain invalidates a donor or earlier-target PASS claim for this new combined source.
- LOCAL_COMPILER remains the user's proof execution target. GitHub CI is a separate receiving integration check.
