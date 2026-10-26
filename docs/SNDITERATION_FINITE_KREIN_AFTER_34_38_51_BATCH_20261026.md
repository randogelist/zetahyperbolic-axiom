# Unified intake: snditeration proof components for Theorem 5.2(2)

Status: `_construction`; **not merged** and no recipient combined-build certification asserted.

Canonical stacked source: `zetahyperbolic-axiom` PR #26 (3.4/3.8/5.1) → PR #30 (all actual 5.1 identities) → this branch (finite 5.2(2) signed Krein). Exact parent commit `1b1d14cabb8477ee684da2a6355c057ddba04a84`; source baseline 224-module `main@7d09dce140f83fddd13a8d9c3a0050072076a0f9`.

The prior #28/#31 donor lane is byte-identical on all four 5.1 files; therefore **do not merge it independently** with this lane. These two original `src/LeanPaper/BeukersKrein*` proof source blobs are imported without modification:
- `src/LeanPaper/BeukersKreinMonomialActual.lean`: Git blob `3a0cb3795036a114af28094ef9733a223051ecca`, original `snditeration/Zetahyperbolic/Section5/KreinMonomial.lean` blob `9f4e12d26e12e55ad1ab42603d40706eefa88ed7` (only import line adapted).
- `src/LeanPaper/BeukersKreinPolynomialActual.lean`: Git blob `f64d1da65450652368ea704d153610fa53279971`, original `snditeration/Zetahyperbolic/Section5/KreinPolynomial.lean` blob `f420c1fdcd638724c1aa0be1c46957c023d6d172` (only import line adapted).

Donor proof: [Lean 4.33.0 CI and foundational-only axiom gate 40271072845](https://github.com/randogelist/snditeration/actions/runs/40271072845), passed. **The proof is genuinely only the monomial actual ζ(7) signed Krein formula and finite coefficient polynomial extension**, not the arbitrary-`L²` theorem, infinite Krein cones, Theorem 5.2(3), or ζ(7) irrationality.

Exactly 2 new mathematical source files, `modules.txt`, `lakefile.toml`, `src/LeanPaper/KernelAudit.lean`, and this provenance note modified relative to parent. 233 modules planned including KernelAudit; previous source unchanged.

Merge gate: PR #26, then PR #30 must be accepted against the correct main; afterward require this **exact SHA** (or exact reconciled SHA) to pass a new full Lean 4.33.0 pinned-Mathlib 233-module receiving CI and independent `AXIOM_AUDIT_ACCEPTED=ALL_PROJECT_DECLARATIONS` with no `sorryAx`, custom axioms, or proof-admission shortcuts. Native Windows LOCAL_COMPILER target remains separate. No full manuscript theorem promotion from source staging or donor evidence alone.
