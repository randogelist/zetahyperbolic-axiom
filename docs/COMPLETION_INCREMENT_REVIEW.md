# Verification of v0_1_4_construction

The local final build passed **166/166 modules**, with the same Lean 4.33.0 and pinned Mathlib environment as the retained baseline. The expanded audit traversed **2,248 project declarations** and **77,529 transitive dependency declarations**. Its **1,710 kernel theorem declarations** include generated and private declarations and are not a manuscript-coverage count. The only encountered axioms were `propext`, `Classical.choice` and `Quot.sound`.

The 12 new modules contain 106 explicit public theorem/lemma declarations and 22 other public declarations; all 128 names are checked by the final audit module. The complete active source scan found zero `sorry`, `admit` or project-axiom tokens after stripping nested comments and strings. Independent transitive proof inspection supplies the stronger dependency check. The deliberately invalid audit regression fixtures are outside the active import closure.

All 153 prior mathematical and audit-helper source files remain byte-identical. Only `LeanPaper.KernelAudit` changes among the prior Lean files, to include the new module ownership and target lists. Both the strict local runner and native Windows runner are unchanged. New names and module documentation are descriptive; retained public APIs are preserved.

The full run revalidated the exact compiler/environment, source, import, output and log fingerprints. It reused the 165 valid module artifacts, including the newly compiled modules, and compiled the changed final audit. It did not treat unverified archive objects as passes. Source hashes in the final receipt match the final files.

Independent semantic review accepted the actual primitive-polynomial Theorem 3.1 endpoint: its matrix norm is explicitly the Euclidean operator norm, its Gram positivity and slope invertibility are constructed from admissibility, and its boundary is attained. It assumes neither root simplicity nor an external spectral witness. Principal-minor degree/root counts use rank and algebraic multiplicity. Higher-derivative Turán and weak normalized Newton apply to the actual primitive polynomial; strict normalized Newton remains open.

The new rational-domain and reciprocal-root modules were separately reviewed for representation independence, actual-family linkage, signs and hypotheses. Higher reciprocal derivative/rationality orders and lifted rational substitution/linearity are not inferred from the new lower-order results.

The 45-item semantic tracker counts **one newly completed printed item (3.1)** and **one retained complete item (4.3)**. The remaining **43** consist of 24 partial, 16 not formalized and 3 blocked literal items. Definition 2.1 and supporting constructions are mapped separately.

Full-paper completion is mathematically blocked by the printed statements of 3.4–3.6. The actual admissible singular-principal example refutes universal full root enumeration; the actual finite root family's Hankel determinant vanishes at order h+1; the normalized continued fraction and odd logarithmic-derivative sign require correction. Corrected proofs do not certify the false originals. Many additional analytic and arithmetic estimates remain unproved, with exact gaps in the tracker. Completing the paper requires a corrected mathematical specification and proofs of those remaining estimates; a green build alone cannot supply them.

The Lake configuration, all locked dependencies, module ownership inventory and embedded CI scripts passed local configuration/static validation. Official action references were checked and pinned. Remote Actions results must be read from the resulting commit; no local result is labeled a remote CI pass. Native Windows execution remains untested.

This workspace is an API-managed source snapshot, not a local Git checkout. Publication uses the verified base commit `b378cba25cca544a8a2a45529a6673960d175f66`, a lease-guarded branch update and complete remote-tree byte verification. The package excludes generated caches and preserves the single native `run.cmd`.
