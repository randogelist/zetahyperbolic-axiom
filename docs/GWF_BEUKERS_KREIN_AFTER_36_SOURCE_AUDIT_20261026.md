# Leaned Paper: actual Beukers / Krein integration on latest audited structural main

Source base: dea277cc309e863f84fbf392ac13a08cd8c369f4, 228 registered Lean 4.33.0 modules, with manuscript Section 3.4 and 3.8 frozen mathematical sources already merged in PR #36. The accepted Section 5.1 diagonal source was merged earlier through PR #23.

Five new Lean modules, sourced exactly from previous frozen PR #35 head 6f8c9dafff92f654a0cabb4ed6259823fec241e3, with unchanged Git blobs:
- src/LeanPaper/BeukersOffDiagonalActual.lean — f7f6cd208ce587d01e58a829b96e040edf1ca2c2
- src/LeanPaper/BeukersDensityActual.lean — 9e1bb8066fd01b00ad251a5fbc89be31d2235d2b
- src/LeanPaper/BeukersRationalityActual.lean — 7ed9310ff921c9fc5e0827c8791c68157390c819
- src/LeanPaper/BeukersKreinMonomialActual.lean — 3a0cb3795036a114af28094ef9733a223051ecca
- src/LeanPaper/BeukersKreinPolynomialActual.lean — f64d1da65450652368ea704d153610fa53279971

Mathematics: exact off-diagonal actual Beukers integral moment and rationality witness, strict density positivity, genuine signed Krein monomial identity, finite rational-polynomial bilinear/quadratic extension.
Not claimed: arbitrary L² Krein decomposition, full 5.2, cone theorem, ζ(7) irrationality or full paper closure. Original 5.1 completion must still be checked against the PDF and the exact receiving Lean certificates.

This PR is a source-preserving additive merge candidate: all previous 228 mathematical modules, toolchain, pinned Mathlib, runner, preexisting provenance and author text remain byte-for-byte unchanged. The only changes beyond the five new Lean source files are this receipt and the exact registry additions in modules.txt, lakefile.toml and LeanPaper.KernelAudit. New count: 233.

Mandatory before main acceptance: Lean 4.33.0 / matching Mathlib full 233-module exact-head source compile and independently complete AXIOM_AUDIT_ACCEPTED=ALL_PROJECT_DECLARATIONS; only foundational propext, Quot.sound, Classical.choice. Prior source/donor runs may support source provenance but not a new SHA CI PASS. Keep LOCAL_COMPILER proof target locked; CI is an integration gate, Windows compilation is separate.
