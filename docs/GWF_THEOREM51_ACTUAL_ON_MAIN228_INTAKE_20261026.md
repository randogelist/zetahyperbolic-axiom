# Integration: actual manuscript Theorem 5.1 on 228-module main

Stage: _construction; exact main parent `dea277cc309e863f84fbf392ac13a08cd8c369f4` (source- and axiom-audited 228-module checkpoint from PR #36). Target: fully evaluated actual two-variable Beukers moments in original printed Theorem 5.1, not ζ(7) irrationality.

Three frozen proof modules reused byte-for-byte from [PR #30](https://github.com/randogelist/zetahyperbolic-axiom/pull/30), themselves the receiving import translations of independently verified `randogelist/snditeration` proofs: 
- `BeukersOffDiagonalActual`: blob `f7f6cd208ce587d01e58a829b96e040edf1ca2c2`; exact off-diagonal unit-square integral and full diagonal/off-diagonal cases.
- `BeukersDensityActual`: blob `9e1bb8066fd01b00ad251a5fbc89be31d2235d2b`; positivity/measurability.
- `BeukersRationalityActual`: blob `7ed9310ff921c9fc5e0827c8791c68157390c819`; genuine rational witness.

Existing 228 mathematical sources are unchanged. Three mandatory registry files, each with precisely three additional entries, match the frozen 231-module PR #30 code word-for-word. Toolchain 4.33.0, pinned Mathlib, native Windows `run.cmd`, and 45-item manuscript ledger unchanged.

**Mandatory merge gate:** fresh exact-head CI Lean 4.33.0 all 231 modules and independent `AXIOM_AUDIT_ACCEPTED=ALL_PROJECT_DECLARATIONS` under only `propext`, `Classical.choice`, `Quot.sound`; no `sorryAx`. Equivalent successful code-tree evidence from prior run may be used only with exact matching Lean/registry/dependency fingerprints and prior PASS for this GITHUB_CI target; old donor source PASS is insufficient. Check main SHA and actual printed theorem before manuscript status promotion.

Do not merge this construction candidate without A-Tier gate; proof execution remains LOCAL_COMPILER independently.
