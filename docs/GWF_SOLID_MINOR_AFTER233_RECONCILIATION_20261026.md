# Frozen shifted-solid Hankel minor integration (main-derived 234)

Source donor PR #25: `src/LeanPaper/ShiftedSolidMinors.lean`, Git blob `e6c8c22df1f4fb085b356d61f8820b684a365b99`. Lean 4.33.0 donor head `00700d6b4709dbfbcf5397672fdac123d3f7893f` passed all 225 modules and complete independent transitive axiom audit in [GitHub run 40273397775](https://github.com/randogelist/zetahyperbolic-axiom/actions/runs/40273397775), with only `Quot.sound`, `Classical.choice`, `propext`.

Receiving source parent: 233-module manuscript consolidation PR #37 at `83b7513b1b9702f306ab7ec7fb52b2e4759b1541`, descended from verified main 225. Exactly one immutable mathematical source and the three exact changed module/Lake/audit registries are added. No prior mathematical source modified. Modules: 234 including KernelAudit.

Original manuscript Theorem 3.3 contribution: true Stieltjes shifted-moment positivity, all-order *solid* shifted Hankel minors and corresponding actual Gram solid minors. It **does not** prove arbitrary mixed minors, complete Stieltjes determinacy or the whole printed 3.3.

**Admission:** merge PR #37 first or reconcile the source on its accepted main; then require a new full 234-module Lean 4.33.0 compile and independent `AXIOM_AUDIT_ACCEPTED=ALL_PROJECT_DECLARATIONS` with only foundational axioms, no sorryAx, exact SHA/dependencies/source fingerprints. Donor PASS by itself does not certify 234 new HEAD. Keep LOCAL_COMPILER as user proof-target; GitHub CI is a separate integration gate. This draft is `_construction`, not merged.
