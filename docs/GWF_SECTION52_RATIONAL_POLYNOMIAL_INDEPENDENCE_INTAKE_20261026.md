# Section 5.2(1): rational polynomial independence actual dual spectrum — source intake

Workflow: YOU_ARE_GOODWORKFLOWFRONTIER v1_0_25, `_construction`.

Receiving HEAD baseline `22454229428c282352912f28e769983b166a6319` (236 registered modules, including KernelAudit). Donor: repository `randogelist/zetahyperbolic-axiom`, unreconciled PR #44 source HEAD `c06a1b200beb0a88e520874ca50904fcf2a2dcd9`, Lean source blob `d7e8ba3a4ef4f40abde344d8f55ddd6183254a0b`, `src/LeanPaper/Section5RationalIndependence.lean`.

Original failed proof before repair used 200,000 heartbeats. The donor's only mathematical-file change is elaboration budget `set_option maxHeartbeats 3000000 in` before the first theorem. This integration carries the exact source blob with unchanged declarations/hypotheses/proof bodies. It has no `sorry`, `admit`, or asserted mathematical axioms. Its own 236-module CI [run 40279008094](https://github.com/randogelist/zetahyperbolic-axiom/actions/runs/40279008094) was pending at source intake; **no donor or receiving A-Tier PASS is claimed**.

The finite statement strengthens the actual rational dual-pencils: rational row independence implies positive definite real slope, determinant degree h and only real complex roots; the polynomial wrapper quantifies over a linearly independent rational polynomial family with degree bound K. It does NOT prove the infinite Krein L² extension, arbitrary cones, or ζ(7) irrationality. Keep Theorem 5.2 manuscript whole-item status partial.

Exactly one frozen source blob is added; existing sources, Lean 4.33.0/Mathlib `db584cd6d46c92f209a44c0f1c829460d327499d`, Windows runner and prior receipts are preserved. Only `modules.txt`, `lakefile.toml`, and `src/LeanPaper/KernelAudit.lean` extend to 237 modules. This is user-authorized direct source integration.

Required promotion: exact merged-HEAD full Lean 4.33.0 build and independent `AXIOM_AUDIT_ACCEPTED=ALL_PROJECT_DECLARATIONS` (only `propext`, `Classical.choice`, `Quot.sound`; no `sorryAx`); if failing, repair or revert, never claim verified proof. `LOCAL_COMPILER` target is unchanged; GitHub CI validates merge-integrity separately.
