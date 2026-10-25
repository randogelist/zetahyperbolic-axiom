# Local Lean 4.33 testing

The user authorized local installation and compilation on 2026-10-25. The
released Linux Lean 4.33.0 archive was checked against GitHub's SHA256 release
digest. Mathlib is pinned to `db584cd6d46c92f209a44c0f1c829460d327499d`
(`v4.33.0`), also the version named in the supplied assembled base's manifest.
All 8,690 requested Mathlib cache files were downloaded and decompressed.

The current environment contains:

- Compiler: `/workspace/toolchains/lean-4.33.0-linux/bin/lean`
- Mathlib: `/workspace/toolchains/mathlib4-4.33.0`
- Convenience wrappers: `/workspace/toolchains/bin/lean` and `lake`

This host permits the executable lookup `/proc/self/exe` while rejecting the
equivalent numeric path `/proc/PID/exe` used by Lean. The narrow compatibility
library in `tools/self_exe_compat.c` redirects only the current process's own
lookup to `/proc/self/exe`. The downloaded Lean executable and kernel are
unchanged. The library's hash is included in the local environment receipt.
No system-wide installation or change to global shell configuration is required.

From this repository, run:

```sh
python3 tools/test_local.py \
  --lean /workspace/toolchains/lean-4.33.0-linux/bin/lean \
  --mathlib /workspace/toolchains/mathlib4-4.33.0 \
  --preload /workspace/toolchains/compat/self_exe.so --jobs 1
```

The local runner compiles the complete active module plan in dependency order,
retains per-module compiler logs, and checks the final independent axiom-audit
sentinel. It reuses a successful local compilation only if source, imported
object files, compiler/runtime/cache binary trees, flags and compiler log match
the saved fingerprints. A failed dependency blocks downstream modules. All
cached local artifacts are under `.build/local-lean433`.

The independent audit traverses types and proof bodies, including private
declarations, inductive cycles, constructors and recursors. Missing constants
fail the audit. Only `propext`, `Quot.sound` and `Classical.choice` are allowed.
The focused regression fixtures under `tests/axiom_walk` deliberately declare
custom axioms to check rejection. They are never active project imports.

Local Linux compilation does not test Windows CMD execution. The offline
Windows `run.cmd` remains available and maintains separate native receipts.
Compilation and axiom acceptance certify the exact Lean statements, including
their explicit hypotheses; they do not close remaining manuscript obligations.
