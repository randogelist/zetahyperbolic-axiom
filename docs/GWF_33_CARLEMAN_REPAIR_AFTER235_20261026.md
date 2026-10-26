# 3.3 abstract Carleman criterion — compiler repair candidate, no theorem status promotion

Receiving main=83698abfbf9b8a35bd1ef5750632bb6f8e808464; source PR16@6b9aad3512b96cbaef8c766ce7fffe2644018f9e; source original Git blob 5460760348493a71d7fe471a3ec2d0c1ab881d33.
Lean 4.33.0; pinned Mathlib=db584cd6d46c92f209a44c0f1c829460d327499d; target=LOCAL_COMPILER, separate GitHub CI for integration.

PR #16 original [CI 40268735312](https://github.com/randogelist/zetahyperbolic-axiom/actions/runs/40268735312) FAILED with errors: line48 `Nat.lt_two_pow_self r` function expected; line65 redundant `ring` after `simp only`; line90 `positivity` on nonpositivity. Transitive axiom checks were not valid and the error-recovered theorem showed `sorryAx`. No PASS is claimed.
This branch changes ONLY those three tactic lines: explicitly infer the Nat lemma argument from expected type, omit surplus ring, and prove negative reciprocal nonpositivity from positive reciprocal. All theorem statements, hypotheses, constants and domains remain IDENTICAL. If any repair fails Lean, the candidate remains open until corrected, not merged into main as a theorem.

New 236-module configuration adds one source, this receipt and exact module/Lake/KernelAudit registrations. All existing mathematical sources and pinned dependencies unchanged.
Scope: abstract moment upper factorial bound ⇒ Carleman root-series divergence, still conditional on unproved actual ζ-family moment growth and Stieltjes uniqueness. No original manuscript theorem, ζ irrationality or A-Tier claim follows from source staging.
Require exact SHA Lean compile + independent full AXIOM_AUDIT_ACCEPTED=ALL_PROJECT_DECLARATIONS with only propext, Classical.choice, Quot.sound and no sorryAx before proof admission.