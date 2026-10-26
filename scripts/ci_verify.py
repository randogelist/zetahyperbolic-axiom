#!/usr/bin/env python3
"""Fresh, dependency-aware GitHub CI compilation and transitive axiom audit.

This runner never imports local/Windows proof receipts or reuses project objects
from another run. Only the pinned external Mathlib cache is used. Its direct
compiler invocation matches the existing fingerprinted tools/test_local.py,
but its output directory and evidence target are exclusively GITHUB_CI.
"""
from __future__ import annotations

import argparse
from concurrent.futures import FIRST_COMPLETED, ThreadPoolExecutor, wait
import hashlib
import json
import os
from pathlib import Path
import platform
import re
import shutil
import subprocess
import time

PIN = "db584cd6d46c92f209a44c0f1c829460d327499d"
AUDIT = "LeanPaper.KernelAudit"
SENTINEL = "AXIOM_AUDIT_ACCEPTED=ALL_PROJECT_DECLARATIONS"


def digest(path: Path) -> str:
    with path.open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()


def atomic_json(path: Path, value: object) -> None:
    temporary = path.with_suffix(path.suffix + ".tmp")
    temporary.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n")
    temporary.replace(path)


def schedule(modules, dependencies, compile_one, on_result, jobs=2):
    """Compile each node once; failed dependencies never block unrelated nodes."""
    results, pending, running = {}, set(modules), {}
    with ThreadPoolExecutor(max_workers=jobs) as pool:
        while pending or running:
            for module in modules:
                if module not in pending:
                    continue
                bad = [d for d in dependencies[module]
                       if d in results and results[d]["status"] != "completed"]
                if bad:
                    results[module] = {"module": module, "status": "skipped_dependency",
                                       "failed_dependencies": bad}
                    pending.remove(module)
                    on_result(module, results[module])
                elif len(running) < jobs and all(d in results for d in dependencies[module]):
                    inputs = {d: results[d]["output_hashes"] for d in dependencies[module]}
                    running[pool.submit(compile_one, module, inputs)] = module
                    pending.remove(module)
            if not running:
                if pending:
                    raise RuntimeError("Dependency cycle or missing nodes: " + ", ".join(sorted(pending)))
                break
            done, _ = wait(running, return_when=FIRST_COMPLETED)
            for future in done:
                module = running.pop(future)
                try:
                    result = future.result()
                except Exception as error:
                    result = {"module": module, "status": "failed", "runner_error": repr(error)}
                results[module] = result
                on_result(module, result)
    return results


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--jobs", type=int, default=2)
    args = parser.parse_args()
    if os.environ.get("GITHUB_ACTIONS") != "true":
        raise SystemExit("This runner executes Lean only inside GitHub Actions.")
    if args.jobs < 1:
        raise SystemExit("--jobs must be positive")

    root = Path(__file__).resolve().parents[1]
    build = root / ".build/ci-lean"
    objects, logs, states = [build / name for name in ("objects", "logs", "states")]
    # No project object from an earlier run is evidence for this run.
    for path in (objects, logs, states):
        if path.exists():
            shutil.rmtree(path)
        path.mkdir(parents=True)

    def capture(command):
        return subprocess.check_output(command, cwd=root, text=True).strip()

    prefix = Path(capture(["lake", "--no-cache", "env", "lean", "--print-prefix"]))
    lean = prefix / "bin/lean"
    version = capture([str(lean), "--version"])
    if "version 4.33.0," not in version:
        raise RuntimeError("Unexpected Lean compiler: " + version)
    actual_pin = capture(["git", "-C", ".lake/packages/mathlib", "rev-parse", "HEAD"])
    if actual_pin != PIN:
        raise RuntimeError("Unexpected Mathlib revision: " + actual_pin)

    lake_path = capture(["lake", "--no-cache", "env", "printenv", "LEAN_PATH"])
    project_lake_objects = (root / ".lake/build/lib/lean").resolve()
    external = []
    for value in lake_path.split(os.pathsep):
        path = Path(value)
        path = (root / path).resolve() if not path.is_absolute() else path.resolve()
        if path != project_lake_objects and path not in external:
            external.append(path)
    if not any("mathlib" in str(path) for path in external):
        raise RuntimeError("Pinned Mathlib artifacts are absent from the Lake environment")
    environment = os.environ.copy()
    environment["LEAN_PATH"] = os.pathsep.join(map(str, [objects, *external]))
    environment["LEAN_SYSROOT"] = str(prefix)

    binary_hashes = {}
    suffixes = (".olean", ".olean.private", ".olean.server", ".ir", ".ir.sig", ".so")
    for tree in [prefix / "lib/lean", *external]:
        for path in sorted(tree.rglob("*")):
            if path.is_file() and path.name.endswith(suffixes):
                binary_hashes[str(path)] = digest(path)
    commit = capture(["git", "rev-parse", "HEAD"])
    evidence = {"target": "GITHUB_CI", "commit": commit,
                "run_id": os.environ.get("GITHUB_RUN_ID"),
                "run_attempt": os.environ.get("GITHUB_RUN_ATTEMPT"),
                "runner_os": platform.platform(), "machine": platform.machine(),
                "runner_image": os.environ.get("ImageVersion"),
                "lean_version": version, "compiler_sha256": digest(lean),
                "mathlib_commit": actual_pin, "flags": ["-j", "2"],
                "lean_path": environment["LEAN_PATH"], "binary_tree": binary_hashes,
                "runner_sha256": digest(Path(__file__)),
                "configuration": {name: digest(root / name) for name in
                                  ("lean-toolchain", "lakefile.toml", "lake-manifest.json", "modules.txt")}}
    atomic_json(build / "environment.json", evidence)
    environment_hash = digest(build / "environment.json")
    (build / "commit.txt").write_text(commit + "\n")
    (build / "toolchain.txt").write_text(version + "\n")

    modules = [line.strip() for line in (root / "modules.txt").read_text().splitlines()
               if line.strip() and not line.lstrip().startswith("#")]
    if len(modules) != len(set(modules)) or not modules or modules[-1] != AUDIT:
        raise RuntimeError("Invalid module plan")
    paths = {m: root / "src" / (m.replace(".", "/") + ".lean") for m in modules}
    source_hashes = {m: digest(path) for m, path in paths.items()}
    imports = {m: re.findall(r"^import\s+([A-Za-z0-9_.]+)", path.read_text(), re.M)
               for m, path in paths.items()}
    dependencies = {m: [d for d in imports[m] if d in paths] for m in modules}
    for module, names in imports.items():
        if any(name not in paths and not name.startswith(("Mathlib", "Lean", "Std", "Init"))
               for name in names):
            raise RuntimeError("Unknown import in " + module)
    observed = {m: {"module": m, "status": "untouched", "source_sha256": source_hashes[m]}
                for m in modules}

    def save_summary(state="RUNNING", regressions=None):
        summary = {"target": "GITHUB_CI", "commit": commit, "state": state,
                   "environment_sha256": environment_hash, "module_count": len(modules),
                   "completed": sum(row["status"] == "completed" for row in observed.values()),
                   "failed": [m for m, row in observed.items() if row["status"] == "failed"],
                   "skipped_dependency": [m for m, row in observed.items()
                                          if row["status"] == "skipped_dependency"],
                   "axiom_audit_accepted": observed[AUDIT].get("audit_accepted", False),
                   "axiom_regressions": regressions, "native_windows_status": "NOT_RUN",
                   "full_manuscript_equivalence": "NOT_CERTIFIED",
                   "modules": [observed[m] for m in modules]}
        atomic_json(build / "summary.json", summary)
        return summary

    def compile_one(module, dependency_hashes):
        output = objects / (module.replace(".", "/") + ".olean")
        output.parent.mkdir(parents=True, exist_ok=True)
        log = logs / (module + ".log")
        start = time.monotonic()
        command = [str(lean), "-j", "2", "-o", str(output), module.replace(".", "/") + ".lean"]
        with log.open("w") as stream:
            process = subprocess.run(command, cwd=root / "src", env=environment,
                                     stdout=stream, stderr=subprocess.STDOUT)
        valid = (process.returncode == 0 and output.exists()
                 and digest(paths[module]) == source_hashes[module])
        audit_accepted = module == AUDIT and valid and SENTINEL in log.read_text()
        if module == AUDIT:
            valid = valid and audit_accepted
        result = {"module": module, "status": "completed" if valid else "failed",
                  "action": "FRESH_CI_COMPILE", "returncode": process.returncode,
                  "seconds": round(time.monotonic() - start, 3), "command": command,
                  "source_sha256": source_hashes[module], "environment_sha256": environment_hash,
                  "dependencies": dependency_hashes, "log_sha256": digest(log),
                  "output_hashes": {str(p.relative_to(objects)): digest(p)
                                    for p in sorted(output.parent.glob(output.stem + ".*"))
                                    if valid and p.is_file()}}
        if module == AUDIT:
            result["audit_accepted"] = audit_accepted
        atomic_json(states / (module + ".json"), result)
        return result

    def on_result(module, result):
        result.setdefault("source_sha256", source_hashes[module])
        observed[module] = result
        save_summary()
        print(module + ": " + result["status"], flush=True)
        if result["status"] == "failed":
            log = logs / (module + ".log")
            if log.exists():
                print("\n".join(log.read_text().splitlines()[-160:]), flush=True)

    save_summary()
    schedule(modules, dependencies, compile_one, on_result, args.jobs)

    # Deliberately bad fixtures get a separate search path only AFTER the main
    # compilation/audit. They can never be imported into the project objects.
    regression = {"status": "skipped_dependency"}
    if observed["LeanPaper.AxiomWalk"]["status"] == "completed":
        test_objects = build / "audit-test-objects"
        if test_objects.exists():
            shutil.rmtree(test_objects)
        test_objects.mkdir()
        test_env = environment.copy()
        test_env["LEAN_PATH"] = str(test_objects) + os.pathsep + environment["LEAN_PATH"]
        tests = []
        for name in ("AuditFixtures", "AuditRegression"):
            log = logs / (name + ".log")
            source = root / "tests/axiom_walk" / (name + ".lean")
            with log.open("w") as stream:
                process = subprocess.run([str(lean), "-j", "2", "-o",
                                          str(test_objects / (name + ".olean")), source.name],
                                         cwd=source.parent, env=test_env,
                                         stdout=stream, stderr=subprocess.STDOUT)
            tests.append({"name": name, "returncode": process.returncode,
                          "source_sha256": digest(source), "log_sha256": digest(log)})
            if process.returncode:
                print(log.read_text(), flush=True)
                break
        regression_ok = (len(tests) == 2 and all(t["returncode"] == 0 for t in tests)
                         and "AXIOM_WALK_REGRESSIONS=PASS" in (logs / "AuditRegression.log").read_text())
        regression = {"status": "completed" if regression_ok else "failed", "tests": tests}
        print("AXIOM_REGRESSION_STATUS=" + regression["status"], flush=True)
    accepted = (all(row["status"] == "completed" for row in observed.values())
                and observed[AUDIT].get("audit_accepted", False)
                and regression["status"] == "completed")
    summary = save_summary("PASS" if accepted else "FAIL", regression)
    print(json.dumps({key: value for key, value in summary.items() if key != "modules"}), flush=True)
    return 0 if accepted else 1


if __name__ == "__main__":
    raise SystemExit(main())
