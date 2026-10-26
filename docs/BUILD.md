# Reproducible Lean build

The standard Lake configuration uses `src/`, Lean **4.33.0**, and Mathlib
commit `db584cd6d46c92f209a44c0f1c829460d327499d`. `lake-manifest.json` also
locks all eight transitive packages. Keep it committed; do not run `lake update`
as part of an ordinary verification run. The library roots must remain exactly
the active, dependency-ordered list in `modules.txt`.

## Standard Linux setup

With Elan already installed, commands in the repository select the version in
`lean-toolchain`. Fetch the compatible dependency artifacts once:

```bash
lake exe cache get
```

This setup step uses the network. It follows the committed manifest rather
than selecting a new Mathlib revision. Confirm the selected revision:

```bash
lean --version
git -C .lake/packages/mathlib rev-parse HEAD
```

Build the active modules sequentially to keep memory usage controlled. Each
Lean compiler uses two threads through `moreLeanArgs` in `lakefile.toml`.
The final module executes the actual independent transitive axiom audit.

```bash
set -euo pipefail
mkdir -p .build/ci-lean
while IFS= read -r module || [[ -n "$module" ]]; do
  module="${module%$'\r'}"
  [[ -z "$module" || "$module" == \#* ]] && continue
  lake --no-cache build "+${module}:olean" 2>&1 | tee ".build/ci-lean/${module}.log"
done < modules.txt
if ! grep -Fq 'AXIOM_AUDIT_ACCEPTED=ALL_PROJECT_DECLARATIONS' \
    .build/ci-lean/LeanPaper.KernelAudit.log; then
  lake --no-cache env lean -j 2 src/LeanPaper/KernelAudit.lean 2>&1 | \
    tee -a .build/ci-lean/LeanPaper.KernelAudit.log
fi
grep -Fq 'AXIOM_AUDIT_ACCEPTED=ALL_PROJECT_DECLARATIONS' \
  .build/ci-lean/LeanPaper.KernelAudit.log
```

The fallback runs the audit directly if Lake reused its compiled object and emitted no audit output. Lake reuses compatible outputs using its dependency traces. Do not pass
`--old`, which ignores transitive dependency changes. A bare `lake build` also
builds the library, but can launch multiple compiler processes; the sequential
loop is the recommended low-memory route. Missing external artifacts must be
provisioned before an offline run. The `--no-cache` option disables build-cache
downloads; it does not make a missing dependency checkout available offline.

## GitHub Actions

The current repair uses `GITHUB_CI`; no local Lean or Lake command was run.
`.github/workflows/lean.yml` checks out the exact pull-request head, pins its
actions by commit, obtains the locked Mathlib artifacts, and validates the
complete source/module/audit inventory. It runs `scripts/ci_verify.py` in GitHub
Actions with two dependency-aware compiler workers. A failed module does not
prevent unrelated modules from being checked; failed dependents are skipped.

Project output starts in a fresh isolated directory. Reuse requires a prior
same-target transitive audit and matching compiler, dependency, runner, policy,
source, imported-object, output and log fingerprints. A failing run may cache
only its separately audited dependency-closed completed subset. Its receipt
remains `FAIL` with scope `COMPLETED_PROJECT_SUBSET`; that cache is never a
full-project acceptance.

Full acceptance requires every registered module, a fresh
`LeanPaper.KernelAudit` over all project declarations, and fresh isolated
negative-audit regression checks. The permitted foundational axioms are only
`propext`, `Quot.sound` and `Classical.choice`. Printed theorem names and a
workflow's existence are not proof receipts. The Python scheduler/cache tests
also run before compilation.

The artifact retains `.build/ci-lean/summary.json`, the environment manifest,
per-module logs/states, source/import/object hashes, the global audit and the
negative-regression evidence, even if compilation fails. Current accepted
receipts are recorded under `validation/github/`; historical Linux and Windows
receipts remain separate. Exact theorem scope is recorded in the manuscript
ledger and correction log, independently of build success.

## Existing cached local and native workflows

The existing `tools/test_local.py` remains the strict fingerprinted local
receipt generator. Its documented command is in `LOCAL_TESTING.md`. It expects
a standalone Mathlib checkout with its own `.lake/packages`, unlike the root
Lake workspace's sibling dependency directories. Use the matching layout for
the selected runner; neither runner silently imports the other's receipts.

The native Windows offline `run.cmd` is unchanged and remains separate. A
Linux Lake or local-runner pass does not certify Windows execution. Cache
directories `.lake/` and `.build/` are generated artifacts and must be excluded
from source packages. None of these build routes closes the mathematical
obligations listed in the manuscript ledger.

The GitHub preflight also checks that every `dependencies/<module>.txt` exists and lists exactly the source's direct project imports, without duplicates. This catches omissions before the native CMD runner's strict import-plan gate; it is a static consistency check, not a native Windows execution receipt.
