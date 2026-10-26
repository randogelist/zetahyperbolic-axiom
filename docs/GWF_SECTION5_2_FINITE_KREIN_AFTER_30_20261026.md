# Leaned Paper: Section 5.2(2) finite Krein channels on PR #30

This is a source-preserving integration candidate, not a completed manuscript theorem.

Base: PR #30 exact head 1b1d14cabb8477ee684da2a6355c057ddba04a84, containing the actual Beukers 5.1 density/diagonal/off-diagonal and rationality components on top of manuscript structural PR #26.
Two new proof sources copied verbatim from PR #31 receiving files (which were adapted only in the import line from snditeration donor):
- src/LeanPaper/BeukersKreinMonomialActual.lean — blob 3a0cb3795036a114af28094ef9733a223051ecca
- src/LeanPaper/BeukersKreinPolynomialActual.lean — blob f64d1da65450652368ea704d153610fa53279971

Donor: randogelist/snditeration@372deda8edc77bba6312b8f80137e00e1b75e74f, Lean 4.33.0 CI and targeted axiom audit PASS https://github.com/randogelist/snditeration/actions/runs/40271072845.
The statements identify actual Beukers monomial moments with signed Krein channels and extend to finite rational-polynomial coefficient forms; they do NOT prove Theorem 5.2(2) for arbitrary L², infinite cones or any irrationality.

Source plan 233 unique Lean modules including KernelAudit; only 2 new mathematical sources, this handoff note, and 3 mandatory registries differ from PR #30.
All existing source files/pins unchanged. Need exact-head 233-module Lean build and full independent transitive axiom audit on receiving configuration, only propext, Quot.sound, Classical.choice. Admit to main only after PR #26, then #30, each with actual successful exact-source integration audit and final-main reconciliation. Axioms/hypotheses cannot be added to cure proof failures. LOCAL_COMPILER target unchanged; remote CI is integration only.
