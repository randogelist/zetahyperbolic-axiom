#!/usr/bin/env python3
"""Fresh, dependency-aware GitHub CI compilation and transitive axiom audit.

This runner never imports local/Windows proof receipts. Project reuse requires
a previous accepted GitHub CI audit and exact input/object/log fingerprints.
The global audit and its negative regressions always run freshly. Its direct
compiler invocation matches the existing fingerprinted tools/test_local.py;
its output directory and evidence target are exclusively GITHUB_CI.
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
import tomllib

PIN = "db584cd6d46c92f209a44c0f1c829460d327499d"
AUDIT = "LeanPaper.KernelAudit"
SENTINEL = "AXIOM_AUDIT_ACCEPTED=ALL_PROJECT_DECLARATIONS"
SUBSET_SENTINEL = "AXIOM_AUDIT_ACCEPTED=COMPLETED_PROJECT_SUBSET"


def audit_body(source):
    marker = "run_cmd Elab.Command.liftCoreM do"
    if source.count(marker) != 1:
        raise ValueError("Expected one independent global audit command")
    body = marker + source.split(marker, 1)[1]
    expected = "let allowed : List Name := [``propext, ``Quot.sound, ``Classical.choice]"
    if expected not in body or body.count(SENTINEL) != 1:
        raise ValueError("Unexpected global audit policy")
    return body


def subset_audit_source(source, modules):
    """Retain the exact global walker/check; change only audited ownership/scope."""
    if not modules or AUDIT in modules or len(modules) != len(set(modules)):
        raise ValueError("Invalid subset membership")
    if any(re.fullmatch(r"[A-Za-z][A-Za-z0-9_.]*", module) is None for module in modules):
        raise ValueError("Invalid module name")
    body, count = re.subn(r"  let projectModules : Array Name := #\[[\s\S]*?\]\n",
                         "  let projectModules : Array Name := #[\n    " +
                         ",\n    ".join("`" + module for module in modules) + "]\n",
                         audit_body(source))
    if count != 1:
        raise ValueError("Expected one audited module array")
    body = body.replace(SENTINEL, SUBSET_SENTINEL)
    body = body.replace("AUDITED_PROJECT_", "AUDITED_SUBSET_PROJECT_")
    return ("\n".join("import " + module for module in modules) +
            "\n\nopen Lean\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\n\n" + body)


def digest(path: Path) -> str:
    with path.open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()


def atomic_json(path: Path, value: object) -> None:
    temporary = path.with_suffix(path.suffix + ".tmp")
    temporary.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n")
    temporary.replace(path)


def json_digest(value: object) -> str:
    return hashlib.sha256(json.dumps(value, sort_keys=True, separators=(",", ":")).encode()).hexdigest()


def accepted_cache(cache: Path, proof_context_hash: str):
    """Accept only a complete, internally consistent prior same-target receipt."""
    try:
        summary = json.loads((cache / "summary.json").read_text())
        evidence = json.loads((cache / "environment.json").read_text())
        context = evidence["proof_context"]
        if not (summary["cache_verification_status"] == "PASS" and summary["target"] == "GITHUB_CI"
                and evidence["target"] == "GITHUB_CI" and context["target"] == "GITHUB_CI"
                and summary["axiom_regressions"]["status"] == "completed"
                and summary["environment_sha256"] == digest(cache / "environment.json")
                and evidence["proof_context_sha256"] == json_digest(context) == proof_context_hash
                and summary["completed"] == summary["module_count"] == len(summary["modules"])
                and all(row["status"] == "completed" for row in summary["modules"])):
            return None
        modules = {row["module"]: row for row in summary["modules"]}
        if len(modules) != len(summary["modules"]):
            return None
        # The cached set must be closed under all project imports, with the
        # exact same outputs used by each dependent compilation.
        for row in modules.values():
            if any(dep not in modules or hashes != modules[dep]["output_hashes"]
                   for dep, hashes in row.get("dependencies", {}).items()):
                return None
        scope = summary["verification_scope"]
        if scope == "ALL_PROJECT_DECLARATIONS":
            if not (summary["state"] == "PASS" and summary["axiom_audit_accepted"] is True
                    and modules[AUDIT]["audit_accepted"] is True):
                return None
        elif scope == "COMPLETED_PROJECT_SUBSET":
            subset = summary["subset_audit"]
            if not (summary["state"] == "FAIL" and not summary["axiom_audit_accepted"]
                    and subset["accepted"] is True and subset["returncode"] == 0
                    and set(subset["modules"]) == set(modules) and AUDIT not in modules
                    and len(subset["modules"]) == len(modules)
                    and digest(cache / "subset-audit/CompletedSubsetAudit.lean") == subset["source_sha256"]
                    and digest(cache / "subset-audit/audit.log") == subset["log_sha256"]
                    and SUBSET_SENTINEL in (cache / "subset-audit/audit.log").read_text()):
                return None
        else:
            return None
        return {"root": cache, "summary": summary, "modules": modules,
                "run_id": evidence["run_id"], "commit": evidence["commit"]}
    except (OSError, KeyError, TypeError, ValueError):
        return None


def reuse_module(cache, module, source_hash, dependencies, objects, log, environment_hash):
    """Copy verified unchanged outputs into the fresh run; never reuse the audit."""
    if cache is None or module == AUDIT:
        return None
    try:
        previous = cache["modules"][module]
        if not (previous["status"] == "completed" and previous["returncode"] == 0
                and previous["environment_sha256"] == cache["summary"]["environment_sha256"]
                and previous["source_sha256"] == source_hash
                and previous["dependencies"] == dependencies and previous["output_hashes"]):
            return None
        source_log = cache["root"] / "logs" / (module + ".log")
        if digest(source_log) != previous["log_sha256"]:
            return None
        stem = module.replace(".", "/")
        if stem + ".olean" not in previous["output_hashes"]:
            return None
        for name, expected_hash in previous["output_hashes"].items():
            relative = Path(name)
            if (relative.is_absolute() or ".." in relative.parts
                    or relative.parent != Path(stem).parent
                    or not relative.name.startswith(Path(stem).name + ".")):
                return None
            source = cache["root"] / "objects" / relative
            if not source.resolve().is_relative_to((cache["root"] / "objects").resolve()):
                return None
            if digest(source) != expected_hash:
                return None
        for name in previous["output_hashes"]:
            destination = objects / name
            destination.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(cache["root"] / "objects" / name, destination)
        shutil.copy2(source_log, log)
        result = dict(previous)
        result.update(action="REUSED_CI_AUDITED_PASS", seconds=0,
                      environment_sha256=environment_hash,
                      reused_from={"commit": cache["commit"], "run_id": cache["run_id"],
                                   "summary_sha256": digest(cache["root"] / "summary.json")})
        return result
    except (OSError, KeyError, TypeError, ValueError):
        return None


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
    cache_path = root / ".build/ci-cache"
    objects, logs, states = [build / name for name in ("objects", "logs", "states")]
    # Cache objects are copied here only after all reuse checks have passed.
    for path in (objects, logs, states, build / "subset-audit"):
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

    config = tomllib.loads((root / "lakefile.toml").read_text())
    if len(config["lean_lib"]) != 1:
        raise RuntimeError("Expected one project library")
    library = config["lean_lib"][0]
    if (library.get("srcDir") != "src"
            or set(library) - {"name", "srcDir", "moreLeanArgs", "roots"}):
        raise RuntimeError("Unsupported library configuration: update the CI runner explicitly")
    flags = library.get("moreLeanArgs", [])
    if not isinstance(flags, list) or not all(isinstance(arg, str) for arg in flags):
        raise RuntimeError("Invalid moreLeanArgs")
    # Adding a root changes the inventory, not the compiler semantics of old
    # modules. Sources/imports/objects are checked independently per module.
    semantic_config = dict(config)
    semantic_config["lean_lib"] = [{key: value for key, value in library.items() if key != "roots"}]

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
                "mathlib_commit": actual_pin, "flags": flags,
                "lean_path": environment["LEAN_PATH"], "binary_tree": binary_hashes,
                "runner_sha256": digest(Path(__file__)),
                "configuration": {name: digest(root / name) for name in
                                  ("lean-toolchain", "lakefile.toml", "lake-manifest.json", "modules.txt")}}
    proof_context = {key: evidence[key] for key in
                     ("target", "runner_os", "machine", "runner_image", "lean_version",
                      "compiler_sha256", "mathlib_commit", "flags", "lean_path",
                      "binary_tree", "runner_sha256")}
    proof_context["configuration"] = semantic_config
    proof_context["toolchain_sha256"] = evidence["configuration"]["lean-toolchain"]
    proof_context["manifest_sha256"] = evidence["configuration"]["lake-manifest.json"]
    policy = re.sub(r"  let projectModules : Array Name := #\[[\s\S]*?\]\n", "",
                    audit_body((root / "src/LeanPaper/KernelAudit.lean").read_text()))
    proof_context["audit_policy_sha256"] = hashlib.sha256(policy.encode()).hexdigest()
    proof_context["auditor_sha256"] = digest(root / "src/LeanPaper/AxiomWalk.lean")
    proof_context["negative_fixtures"] = {name: digest(root / "tests/axiom_walk" / name)
                                          for name in ("AuditFixtures.lean", "AuditRegression.lean")}
    evidence["proof_context"] = proof_context
    evidence["proof_context_sha256"] = json_digest(proof_context)
    atomic_json(build / "environment.json", evidence)
    environment_hash = digest(build / "environment.json")
    cache = accepted_cache(cache_path, evidence["proof_context_sha256"])
    print("PRIOR_CI_CACHE=" + ("ACCEPTED_FOR_PER_MODULE_CHECKS" if cache else "ABSENT_OR_REJECTED"), flush=True)
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

    def save_summary(state="RUNNING", regressions=None, subset=None):
        summary = {"target": "GITHUB_CI", "commit": commit, "state": state,
                   "environment_sha256": environment_hash, "module_count": len(modules),
                   "completed": sum(row["status"] == "completed" for row in observed.values()),
                   "reused": sum(row.get("action") == "REUSED_CI_AUDITED_PASS" for row in observed.values()),
                   "failed": [m for m, row in observed.items() if row["status"] == "failed"],
                   "skipped_dependency": [m for m, row in observed.items()
                                          if row["status"] == "skipped_dependency"],
                   "axiom_audit_accepted": observed[AUDIT].get("audit_accepted", False),
                   "axiom_regressions": regressions, "native_windows_status": "NOT_RUN",
                   "subset_audit": subset,
                   "full_manuscript_equivalence": "NOT_CERTIFIED",
                   "modules": [observed[m] for m in modules]}
        atomic_json(build / "summary.json", summary)
        return summary

    def compile_one(module, dependency_hashes):
        output = objects / (module.replace(".", "/") + ".olean")
        output.parent.mkdir(parents=True, exist_ok=True)
        log = logs / (module + ".log")
        reused = reuse_module(cache, module, source_hashes[module], dependency_hashes,
                              objects, log, environment_hash)
        if reused is not None:
            atomic_json(states / (module + ".json"), reused)
            return reused
        start = time.monotonic()
        command = [str(lean), *flags, "-o", str(output), module.replace(".", "/") + ".lean"]
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
        print(module + ": " + result["status"] + " " + result.get("action", ""), flush=True)
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
    subset = None
    completed_modules = [m for m in modules if m != AUDIT and observed[m]["status"] == "completed"]
    if not accepted and regression["status"] == "completed" and completed_modules:
        subset_root = build / "subset-audit"
        subset_objects = subset_root / "objects"
        subset_objects.mkdir()
        for module in completed_modules:
            if any(dep not in completed_modules for dep in dependencies[module]):
                raise RuntimeError("Completed subset is not dependency-closed")
            for name, expected_hash in observed[module]["output_hashes"].items():
                if digest(objects / name) != expected_hash:
                    raise RuntimeError("Completed object changed before subset audit")
                destination = subset_objects / name
                destination.parent.mkdir(parents=True, exist_ok=True)
                shutil.copy2(objects / name, destination)
        source = subset_root / "CompletedSubsetAudit.lean"
        source.write_text(subset_audit_source(paths[AUDIT].read_text(), completed_modules))
        source_hash = digest(source)
        subset_env = environment.copy()
        subset_env["LEAN_PATH"] = os.pathsep.join(map(str, [subset_objects, *external]))
        log = subset_root / "audit.log"
        output = subset_root / "CompletedSubsetAudit.olean"
        with log.open("w") as stream:
            process = subprocess.run([str(lean), *flags, "-o", str(output), source.name],
                                     cwd=subset_root, env=subset_env,
                                     stdout=stream, stderr=subprocess.STDOUT)
        subset_ok = (process.returncode == 0 and output.exists() and digest(source) == source_hash
                     and SUBSET_SENTINEL in log.read_text())
        subset = {"accepted": subset_ok, "scope": "COMPLETED_PROJECT_SUBSET",
                  "returncode": process.returncode, "modules": completed_modules,
                  "source_sha256": source_hash, "log_sha256": digest(log),
                  "environment_sha256": environment_hash}
        print("SUBSET_AXIOM_AUDIT=" + ("PASS" if subset_ok else "FAIL"), flush=True)
        if not subset_ok:
            print("\n".join(log.read_text().splitlines()[-160:]), flush=True)
    summary = save_summary("PASS" if accepted else "FAIL", regression, subset)
    cache_ready = accepted or (subset is not None and subset["accepted"])
    if cache_ready:
        # A failing project may publish ONLY its independently audited closed
        # subset. Its CI state remains FAIL; the receipt labels this scope.
        cache_modules = modules if accepted else completed_modules
        cache_receipt = dict(summary)
        cache_receipt.update(cache_verification_status="PASS",
                             verification_scope="ALL_PROJECT_DECLARATIONS" if accepted else "COMPLETED_PROJECT_SUBSET",
                             project_module_count=len(modules), module_count=len(cache_modules),
                             completed=len(cache_modules), modules=[observed[m] for m in cache_modules])
        atomic_json(build / "cache-receipt.json", cache_receipt)
        staging = root / ".build/ci-cache.next"
        if staging.exists():
            shutil.rmtree(staging)
        staging.mkdir()
        for name in ("objects", "logs", "states"):
            (staging / name).mkdir()
        for module in cache_modules:
            for name, expected_hash in observed[module]["output_hashes"].items():
                if digest(objects / name) != expected_hash:
                    raise RuntimeError("Object changed before cache publication")
                destination = staging / "objects" / name
                destination.parent.mkdir(parents=True, exist_ok=True)
                shutil.copy2(objects / name, destination)
            shutil.copy2(logs / (module + ".log"), staging / "logs" / (module + ".log"))
            shutil.copy2(states / (module + ".json"), staging / "states" / (module + ".json"))
        shutil.copy2(build / "cache-receipt.json", staging / "summary.json")
        shutil.copy2(build / "environment.json", staging / "environment.json")
        if not accepted:
            (staging / "subset-audit").mkdir()
            for name in ("CompletedSubsetAudit.lean", "audit.log"):
                shutil.copy2(build / "subset-audit" / name, staging / "subset-audit" / name)
        if cache_path.exists():
            shutil.rmtree(cache_path)
        staging.replace(cache_path)
    if os.environ.get("GITHUB_OUTPUT"):
        with open(os.environ["GITHUB_OUTPUT"], "a") as stream:
            stream.write("cache-ready=" + ("true" if cache_ready else "false") + "\n")
    print(json.dumps({key: value for key, value in summary.items() if key != "modules"}), flush=True)
    return 0 if accepted else 1


if __name__ == "__main__":
    raise SystemExit(main())
