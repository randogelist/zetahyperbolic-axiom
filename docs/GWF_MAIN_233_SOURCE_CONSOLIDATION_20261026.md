# Zetahyperbolic Leaned Paper — source-preserving manuscript consolidation

Receiving main commit: db4db45e35c5f98e9bd38402222d700847b17e2f (PR #23 actual Beukers moment series merged).
Workflow: YOU_ARE_GOODWORKFLOWFRONTIER v1_0_25.
Build tag: _construction. Preserve LOCAL_COMPILER proof-target lock; Linux GitHub Actions serves only the integration audit.
Pinned Lean: 4.33.0; Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d.
225 existing active Lean source files unchanged, with their exact source blobs and audit registry entries retained.
Eight independently manuscript-relevant source files added; total 233 modules including KernelAudit.

Incoming Git blobs (read from frozen project PR heads):
- src/LeanPaper/SignatureRestriction.lean: d1f107761de75eead018d29b69a4f86a476c2efc (source ref 79093f5badec777a29eb0f51fe223d97214a1225)
- src/LeanPaper/Section3MonicOrthogonal.lean: 7638ff43138e47a73e76c64652e887cc87955954 (source ref 79093f5badec777a29eb0f51fe223d97214a1225)
- src/LeanPaper/MatrixCurveJacobi.lean: 5dacaee0aae1ef9e17840a0de80e081eff48fbe8 (source ref 79093f5badec777a29eb0f51fe223d97214a1225)
- src/LeanPaper/BeukersOffDiagonalActual.lean: f7f6cd208ce587d01e58a829b96e040edf1ca2c2 (source ref 1b1d14cabb8477ee684da2a6355c057ddba04a84)
- src/LeanPaper/BeukersDensityActual.lean: 9e1bb8066fd01b00ad251a5fbc89be31d2235d2b (source ref 1b1d14cabb8477ee684da2a6355c057ddba04a84)
- src/LeanPaper/BeukersRationalityActual.lean: 7ed9310ff921c9fc5e0827c8791c68157390c819 (source ref 1b1d14cabb8477ee684da2a6355c057ddba04a84)
- src/LeanPaper/BeukersKreinMonomialActual.lean: 3a0cb3795036a114af28094ef9733a223051ecca (source ref 91e221591ff33fb4aceedd0437829478b399118e)
- src/LeanPaper/BeukersKreinPolynomialActual.lean: f64d1da65450652368ea704d153610fa53279971 (source ref 91e221591ff33fb4aceedd0437829478b399118e)

Previous source-level verification:
- SignatureRestriction — https://github.com/randogelist/zetahyperbolic-axiom/actions/runs/40270783080
- Section3MonicOrthogonal — https://github.com/randogelist/zetahyperbolic-axiom/actions/runs/40271486561
- MatrixCurveJacobi — https://github.com/randogelist/zetahyperbolic-axiom/actions/runs/40266602343
- Beukers actual offdiagonal + density + rationality — donor https://github.com/randogelist/snditeration/actions/runs/40268502325
- Actual finite Krein identities — donor https://github.com/randogelist/snditeration/actions/runs/40271072845

Section 3.4: finite signature-restriction prerequisite, NOT the false literal r-root enumeration.
Section 3.8: finite Gram monic polynomial and Jacobi differential prerequisites, NOT complete Christoffel–Darboux/Laplace identity.
Section 5.1: actual diagonal/offdiagonal moment formula, positivity and rationality; completion of original statement requires an exact receiving-source compile and independent audit.
Section 5.2: signed Krein monomial/finite rational-polynomial identities ONLY, NOT arbitrary L², all-dimensional cones or irrationality.

Mandatory acceptance: exact new-head 233-module sequential Lean 4.33.0 / pinned Mathlib build, proof integrity/no sorryAx and all-project transitive AXIOM_AUDIT_ACCEPTED=ALL_PROJECT_DECLARATIONS under only propext, Quot.sound, Classical.choice. Check manuscript original definitions/quantifiers and full printed-item correspondence before changing any of the frozen 45 status rows. Any source/dependency changes invalidate previous receipts. Do not replace the main's verified Lean sources, pins, audits, run.cmd or documentation.

Branches PR #26/#30/#33 and related old per-target PRs are input donors and may be closed only after this source is accepted, with no double merge. Separate Section 3.3 shifted-solid minors remains queued pending exact integration PASS.
