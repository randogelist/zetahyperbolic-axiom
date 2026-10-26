# ZETA_HYPERBOLIC_TARGET_5_1_BEUKERS_MOMENT_SERIES_1 — current-main integration

Status: _construction; not a theorem-completion certificate.
Receiver: randogelist/zetahyperbolic-axiom main@7d09dce140f83fddd13a8d9c3a0050072076a0f9 (after PR #6).
Original frozen donor: feat/gwf-target-51-beukers-moment-series-v0_1_0@b55e7c1a93348e318b23af40355607f00150408f.
Proof source: src/LeanPaper/BeukersMomentSeries.lean (Git blob 5eff67223443f63e2447a6409ed33cf13458b038), BYTE-IDENTICAL to donor and independently audited 225-module preflight PR #18.
Frozen scope receipt: docs/TARGET_5_1_BEUKERS_MOMENT_SERIES_FREEZE.md (Git blob 9af3743d56899440964c033fef69bf2ab83e2613).
Registry blobs after exact comparison with baseline, each differing by ONE new registration:
modules.txt bfa4662e6cc4beb4b5fd7c257600438565b39c1b
lakefile.toml ac137a683536312bfb2ac87c8e4325ede877999c
src/LeanPaper/KernelAudit.lean b36b10071611ca0edcc65e1f39f75afa678aa72b
Before integration: 224 modules; after integration: 225 modules. All 224 pre-existing active Lean module sources, pinned Lean 4.33.0, Mathlib, dependencies, run.cmd, and previous proof receipts unchanged.
Original standalone full Lean+transitive-axiom CI PASS: https://github.com/randogelist/zetahyperbolic-axiom/actions/runs/40264406071 (221 modules). Preflight #18 is TEST ONLY, not itself a merge candidate.
Receiving branch must independently PASS a fresh exact-head combined 225-module full Lean 4.33.0 build and AXIOM_AUDIT_ACCEPTED=ALL_PROJECT_DECLARATIONS with no sorryAx or new axioms beyond propext, Quot.sound, Classical.choice before promotion/merge. Native Windows status not inferred from Linux CI.
Precise mathematical scope: actual Beukers density moment series and its diagonal zeta(7) tail. NOT the off-diagonal rational identity, actual 2-variable integral equivalence, whole manuscript Theorem 5.1, or irrationality of zeta(7).
