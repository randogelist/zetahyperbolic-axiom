# Native Windows runner

This package uses `run.cmd`, installed native Windows Lean **4.33.0**, existing compiled Mathlib, and standard Windows commands. It does not invoke Lake setup, Python, PowerShell, WSL, elan downloads, or a network setup. This release has been statically reviewed; the native compiler and Windows CMD execution are still to be run by the user.

## Run and cache settings

Run the package's sole `run.cmd` from CMD. The usual installed toolchain and several customary existing Mathlib cache locations are detected automatically. If discovery fails, set the existing paths in the same CMD session:

```cmd
set "LEAN_EXE=C:\path\to\lean-4.33.0\bin\lean.exe"
set "MATHLIB_CACHE=C:\path\to\cached-project"
call "C:\path\to\package\run.cmd"
```

`MATHLIB_CACHE` can be an existing project root, an existing Mathlib checkout, or the compiled directory containing `Mathlib.olean`. A genuine aggregate `Mathlib.olean` is required; this runner does not generate or substitute a local Mathlib facade. It discovers compiled dependencies in the containing project's `.lake\packages`, Mathlib's own `.lake\packages`, and sibling package caches. For a nonstandard packages directory, set `LEAN_PAPER_PACKAGES_DIR` to the existing directory containing the package checkouts. No dependency is downloaded or rebuilt.

The native toolchain path must name the actual installed compiler, not an elan shim. `LEAN_PAPER_CACHE` can override the default `%USERPROFILE%\lean-native\zetahyperbolic_leaned_paper_strict_v1` cache. `VERSION` supplies the package's canonical log version without changing runner source bytes between releases.

The runner deliberately ignores inherited `LEAN_PATH`. Imports resolve through a temporary view containing only project objects already verified in the current run, followed by explicitly discovered compiled external packages and the installed Lean standard library.

Paths containing `!` or `%` are unsupported and are rejected before delayed expansion is enabled. Use ordinary Windows paths; spaces are supported. The toolchain, external caches and package sources must remain unchanged while the runner is executing. A cache writer lock prevents two copies of this runner from writing the same project cache concurrently. A stale lock is reported rather than silently removed.

## Reuse and audit boundaries

Every run hashes the relevant cached binary trees once, including compiler/runtime files, standard-library objects, Mathlib, and its compiled package dependencies. This is deliberately conservative and may take several minutes on large caches, including on later runs. It is file verification, not Lean recompilation. Timestamp-only shortcuts and the aggregate Mathlib object's hash alone do not establish unchanged transitive dependencies.

For each project module, `lean --deps` parses the actual import header without elaborating the module. The resolved local imports must agree with the supplied dependency plan. Their accepted receipt hashes, the source hash, direct dependency plan, compiler flags, external environment, produced object/companion files and compiler log determine whether reuse is valid. Missing or mismatched provenance causes recompilation of that module and the dependent modules invalidated by its new receipt. Legacy `.ok`, source snapshots and bare `.olean` objects are not imported as verified new-schema cache entries.

A successfully elaborated module receives a **COMPILED_ONLY** receipt. This preserves incremental progress even if a later module fails. Its log state ends in `AUDIT_PENDING`; it does not certify an A-tier result, a whole manuscript theorem, or mathematical equivalence to a paper statement.

`LeanPaper.KernelAudit` must be last. It checks all declarations originating in the active project modules against the allowed axiom set and must print the exact standalone sentinel:

```text
AXIOM_AUDIT_ACCEPTED=ALL_PROJECT_DECLARATIONS
```

The intended allowed axioms are `propext`, `Quot.sound`, and `Classical.choice`. The Lean audit source owns the actual allowlist check. Unknown/custom axioms, `sorryAx`, and trusted native-decision bridges are not accepted. The final audit may itself be reused only when all its source, targets, full module plan, imports, object and log fingerprints match; its required sentinel is checked again. The run-wide `audit.accepted` receipt is written only after the final audit succeeds, through a verified temporary copy followed by rename. Any package-level acceptance marker from a previous run is removed at startup.

`BUILD_RECEIPT.txt` records the final build summary, new compilations, verified compilation reuse, rejected reuse and module count. A successful native build and axiom audit still leave manuscript equivalence and conditional mathematical endpoints at their separately recorded status. The runner never turns an assumed premise into an unconditional theorem.

## Maintainer input contract

- `src/<Module/Path>.lean`: active sources only.
- `modules.txt`: dotted module names, one per line, in topological order, ending in `LeanPaper.KernelAudit`.
- `dependencies/<dotted-module>.txt`: direct local import names, one per line; empty when there are none. These are checked against Lean's actual `--deps` output.
- `targets.txt`: the exact key endpoints, bound into the final audit receipt; the audit source must check their existence as well as the declaration allowlist.
- `src/LeanPaper/KernelAudit.lean`: full active module declaration audit and exact acceptance sentinel.
- `VERSION`: canonical package/log version.

Module and dependency lists allow `#` comment lines. Preserve source bytes for previously accepted unchanged modules. Changes to dependency plans, flags, compiler/runtime, Mathlib or runner integrity rules invalidate the corresponding receipts. Outputs are staged, physically checked and content-hashed before the compile receipt commit marker is written.

## Primary implementation references

The native dependency inspection and output handling were checked against the pinned Lean 4.33.0 sources, without executing Lean:

- [Lean shell driver](https://github.com/leanprover/lean4/blob/v4.33.0/src/Lean/Shell.lean): `--deps` dispatches to import parsing; `-o` requests the `.olean` output and `-i` requests optional `.ilean` metadata.
- [Lean import inspection](https://github.com/leanprover/lean4/blob/v4.33.0/src/Lean/Elab/Import.lean): `printImports` parses the header and prints each directly imported `.olean` path.
- [Lean import artifact types](https://lean-lang.org/doc/api/Lean/Setup.html): artifacts include `.olean`, server/private companions and IR/signature files. The runner fingerprints/copies any produced `.olean.private`, `.olean.server`, `.ilean`, `.ir`, and `.ir.sig` alongside the required nonempty `.olean`.
