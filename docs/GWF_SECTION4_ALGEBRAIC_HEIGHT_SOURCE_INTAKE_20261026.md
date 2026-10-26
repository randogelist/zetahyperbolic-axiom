# GWF v1_0_25 — Section 4.2 algebraic-height source integration

Status: `_construction`, merged-source eligibility only; not a new A-Tier proof receipt.
Receiving HEAD baseline: `83698abfbf9b8a35bd1ef5750632bb6f8e808464` (235 registered Lean modules).
Donor repository: `randogelist/snditeration`, source commit `ee34192c0db37c71c7e4bd792f353905b16fd104`, `Zetahyperbolic/Section4/AlgebraicHeight.lean`, Git blob `1318764ca344668e5feeed3c02f0c26bc50aff5b`.
Independent donor Lean 4.33.0 build and axiom audit: [GitHub run 40270563393](https://github.com/randogelist/snditeration/actions/runs/40270563393) PASS. Mathlib commit `db584cd6d46c92f209a44c0f1c829460d327499d`.

Receiving file `src/LeanPaper/Section4AlgebraicHeight.lean` changes ONLY its import `Zetahyperbolic.Section4.AlgebraicLattice` to `LeanPaper.Section4AlgebraicLattice` and its namespace openings to the matching `LeanPaper.Section4Resultant` / `LeanPaper.Section4AlgebraicLattice`. It retains the donor's exact namespace `ManuscriptChain.Section4AlgebraicHeight`, its definitions, full theorem statements and proofs, quantifiers, and axiom checks.

Actual scope: `integerMinimalPolynomial` from a rational minimal polynomial by integer normalization and primitive part; correct polynomial degree and root; constructed naive algebraic height; conditional Proposition 4.2 conclusion for every algebraic complex number of bounded degree, using actual minimal-polynomial height. No concrete zeta decay, separation, denominator estimate, or unconditional irrationality of ζ(5), ζ(7), etc.

Existing 235-module source and toolchain preserved byte-for-byte. Adds precisely one module and extends the three required registry files (`modules.txt`, `lakefile.toml`, `src/LeanPaper/KernelAudit.lean`) to 236 modules inclusive of the audit. No release of old receipt locks.

User has explicitly authorized direct SOURCE-ONLY main integration. Final receipt for a 236-module A-Tier must still be obtained by an exact SHA full Lean 4.33.0 compile and complete independent `AXIOM_AUDIT_ACCEPTED=ALL_PROJECT_DECLARATIONS` restricted to `propext`, `Classical.choice`, `Quot.sound`; no `sorryAx`, custom axioms or unverified source reuse. The separate LOCAL_COMPILER proof target remains locked. If the receiving build fails, repair or revert the exact source; never claim proof from source admission alone.
