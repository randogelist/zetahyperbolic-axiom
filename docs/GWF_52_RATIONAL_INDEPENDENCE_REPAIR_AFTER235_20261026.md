# Manuscript 5.2(1): rational polynomial independence and dual spectrum — compiler repair

WORKFLOW=YOU_ARE_GOODWORKFLOWFRONTIER
TAG=_construction
RECEIVING_MAIN=83698abfbf9b8a35bd1ef5750632bb6f8e808464
OLD_SOURCE_REF=89de573761eb58558976cfe8c53895a8c2cc32ed
OLD_SOURCE_BLOB=ba40e1cf2c0531af573648c026b730859c090f75
MATHLIB_COMMIT=db584cd6d46c92f209a44c0f1c829460d327499d
LEAN_VERSION=4.33.0
PLAN=236 modules including final KernelAudit
USER_PROOF_TARGET=LOCAL_COMPILER
INTEGRATION_GATE=GitHub Linux CI (separate)

The original PR #15 source proved the intended Section 5.2(1) rational-polynomial independence to dual real spectrum, but failed actual receiving CI 40268002608 with deterministic whnf heartbeat timeout (200000) at the first theorem; the subsequent missing constant is a cascade, not an admitted proof. The previous failing run printed the theorem in its dependency axioms; no claim of A-Tier proof can be made.

This repair retains every theorem/lemma declaration, proposition, hypothesis, parameter, proof tactic and import unchanged, adding ONLY the command `set_option maxHeartbeats 3000000 in` immediately before `real_rows_separate_of_rational_injective`. This changes elaboration budget only, no mathematical content, no axioms, no proof-omissions. It may or may not pass CI; no previous PASS.

All 235 previous project modules, compiler pin, Mathlib, runner and project audit implementation remain unchanged; exactly one new module plus this note and required three registries.

MANDATORY acceptance before merging as Lean proof: actual full 236-module exact SHA compiled, plus complete independent transitive AXIOM_AUDIT_ACCEPTED=ALL_PROJECT_DECLARATIONS with only propext, Classical.choice, Quot.sound and no sorryAx. If it fails again, repair in its own branch without merging an uncompiled proof module to main. This finite theorem does not establish the printed arbitrary-L² Krein decomposition or zeta7 irrationality.
