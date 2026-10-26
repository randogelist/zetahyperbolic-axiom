"""Scheduler regression tests; never invoke Lean, Lake or any compiler."""
import unittest
import json
from pathlib import Path
import tempfile

from ci_verify import (AUDIT, SENTINEL, SUBSET_SENTINEL, accepted_cache, digest,
                       json_digest, reuse_module, schedule, subset_audit_source)


class SchedulingTests(unittest.TestCase):
    def test_failure_skips_only_dependents_and_continues_independent_branch(self):
        calls, observed = [], {}
        modules = ["bad", "child", "independent", "leaf", "audit"]
        dependencies = {"bad": [], "child": ["bad"], "independent": [],
                        "leaf": ["independent"], "audit": ["child", "leaf"]}

        def compile_one(module, inputs):
            calls.append(module)
            return {"status": "failed" if module == "bad" else "completed",
                    "output_hashes": {module: "test-digest"}}

        result = schedule(modules, dependencies, compile_one, observed.__setitem__, jobs=2)
        self.assertEqual(set(calls), {"bad", "independent", "leaf"})
        self.assertEqual(result["child"]["status"], "skipped_dependency")
        self.assertEqual(result["audit"]["status"], "skipped_dependency")
        self.assertEqual(result["leaf"]["status"], "completed")
        self.assertEqual(set(observed), set(modules))

    def test_dependency_hashes_are_passed_before_a_child_runs(self):
        inputs_seen = {}

        def compile_one(module, inputs):
            inputs_seen[module] = inputs
            return {"status": "completed", "output_hashes": {module: "hash-" + module}}

        schedule(["a", "b"], {"a": [], "b": ["a"]}, compile_one, lambda *_: None)
        self.assertEqual(inputs_seen["b"], {"a": {"a": "hash-a"}})

    def test_worker_exception_is_a_failure_not_an_acceptance(self):
        def compile_one(module, inputs):
            raise OSError("simulated failure")

        result = schedule(["a", "b"], {"a": [], "b": ["a"]}, compile_one, lambda *_: None)
        self.assertEqual(result["a"]["status"], "failed")
        self.assertEqual(result["b"]["status"], "skipped_dependency")

    def test_cycle_is_rejected(self):
        with self.assertRaisesRegex(RuntimeError, "Dependency cycle"):
            schedule(["a", "b"], {"a": ["b"], "b": ["a"]}, None, lambda *_: None)


class CacheTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        root = Path(self.temporary.name)
        self.cache, self.objects, self.logs = root / "cache", root / "objects", root / "logs"
        for path in (self.cache / "objects", self.cache / "logs", self.objects, self.logs):
            path.mkdir(parents=True)
        self.context = {"target": "GITHUB_CI", "compiler": "test-compiler-hash"}
        self.context_hash = json_digest(self.context)
        self.environment = {"target": "GITHUB_CI", "run_id": "123", "commit": "old-commit",
                            "proof_context": self.context, "proof_context_sha256": self.context_hash}
        self.write("environment.json", self.environment)
        environment_hash = digest(self.cache / "environment.json")
        (self.cache / "objects/A.olean").write_bytes(b"mock compiler output")
        (self.cache / "logs/A.log").write_text("mock successful compile\n")
        self.module = {"module": "A", "status": "completed", "returncode": 0,
                       "source_sha256": "source-hash", "dependencies": {},
                       "environment_sha256": environment_hash,
                       "log_sha256": digest(self.cache / "logs/A.log"),
                       "output_hashes": {"A.olean": digest(self.cache / "objects/A.olean")}}
        self.summary = {"target": "GITHUB_CI", "state": "PASS", "module_count": 2, "completed": 2,
                        "cache_verification_status": "PASS", "verification_scope": "ALL_PROJECT_DECLARATIONS",
                        "axiom_audit_accepted": True, "axiom_regressions": {"status": "completed"},
                        "environment_sha256": environment_hash,
                        "modules": [self.module, {"module": AUDIT, "status": "completed", "audit_accepted": True}]}
        self.write("summary.json", self.summary)

    def write(self, name, value):
        (self.cache / name).write_text(json.dumps(value))

    def reuse(self, module="A", source="source-hash", dependencies=None):
        info = accepted_cache(self.cache, self.context_hash)
        return reuse_module(info, module, source, dependencies or {},
                            self.objects, self.logs / (module + ".log"), "current-environment")

    def test_matching_audited_module_is_copied_but_audit_is_never_reused(self):
        result = self.reuse()
        self.assertEqual(result["action"], "REUSED_CI_AUDITED_PASS")
        self.assertEqual((self.objects / "A.olean").read_bytes(), b"mock compiler output")
        self.assertEqual(result["environment_sha256"], "current-environment")
        self.assertEqual(result["reused_from"]["run_id"], "123")
        self.assertIsNone(self.reuse(AUDIT))

    def test_failed_or_other_target_receipt_is_rejected(self):
        for field, value in (("state", "FAIL"), ("target", "LINUX_LOCAL"),
                             ("axiom_audit_accepted", False), ("completed", 1)):
            with self.subTest(field=field):
                changed = dict(self.summary)
                changed[field] = value
                self.write("summary.json", changed)
                self.assertIsNone(accepted_cache(self.cache, self.context_hash))

    def test_environment_or_source_or_dependency_change_rejects_reuse(self):
        self.assertIsNone(accepted_cache(self.cache, "different-context"))
        self.assertIsNone(self.reuse(source="changed-source"))
        self.assertIsNone(self.reuse(dependencies={"NewImport": {"NewImport.olean": "different"}}))

    def test_corrupt_output_or_log_is_rejected(self):
        (self.cache / "objects/A.olean").write_bytes(b"corruption")
        self.assertIsNone(self.reuse())
        (self.cache / "objects/A.olean").write_bytes(b"mock compiler output")
        (self.cache / "logs/A.log").write_text("changed log")
        self.assertIsNone(self.reuse())

    def test_failed_audit_regression_rejects_cache(self):
        self.summary["axiom_regressions"] = {"status": "failed"}
        self.write("summary.json", self.summary)
        self.assertIsNone(accepted_cache(self.cache, self.context_hash))

    def make_subset_receipt(self):
        folder = self.cache / "subset-audit"
        folder.mkdir()
        (folder / "CompletedSubsetAudit.lean").write_text("mock generated scoped audit source\n")
        (folder / "audit.log").write_text(SUBSET_SENTINEL + "\n")
        self.summary.update(state="FAIL", verification_scope="COMPLETED_PROJECT_SUBSET",
                            axiom_audit_accepted=False, module_count=1, completed=1,
                            modules=[self.module],
                            subset_audit={"accepted": True, "returncode": 0, "modules": ["A"],
                                          "source_sha256": digest(folder / "CompletedSubsetAudit.lean"),
                                          "log_sha256": digest(folder / "audit.log")})
        self.write("summary.json", self.summary)

    def test_independently_audited_subset_can_be_reused_without_global_pass(self):
        self.make_subset_receipt()
        info = accepted_cache(self.cache, self.context_hash)
        self.assertIsNotNone(info)
        self.assertEqual(info["summary"]["state"], "FAIL")
        self.assertFalse(info["summary"]["axiom_audit_accepted"])
        self.assertEqual(self.reuse()["action"], "REUSED_CI_AUDITED_PASS")

    def test_subset_must_be_audited_and_exactly_match_cache_membership(self):
        self.make_subset_receipt()
        subset = dict(self.summary["subset_audit"])
        for field, value in (("accepted", False), ("returncode", 1), ("modules", ["A", "failed"])):
            with self.subTest(field=field):
                self.summary["subset_audit"] = dict(subset, **{field: value})
                self.write("summary.json", self.summary)
                self.assertIsNone(accepted_cache(self.cache, self.context_hash))

    def test_cached_subset_must_be_dependency_closed(self):
        self.make_subset_receipt()
        self.module["dependencies"] = {"failed": {"failed.olean": "hash"}}
        self.write("summary.json", self.summary)
        self.assertIsNone(accepted_cache(self.cache, self.context_hash))

    def test_subset_audit_source_or_log_corruption_rejects_cache(self):
        self.make_subset_receipt()
        (self.cache / "subset-audit/audit.log").write_text("missing acceptance")
        self.assertIsNone(accepted_cache(self.cache, self.context_hash))


class SubsetSourceTests(unittest.TestCase):
    def test_generation_preserves_policy_and_replaces_only_membership_and_scope(self):
        source = ("import Old\nrun_cmd Elab.Command.liftCoreM do\n"
                  "  let allowed : List Name := [``propext, ``Quot.sound, ``Classical.choice]\n"
                  "  let projectModules : Array Name := #[`Old]\n"
                  "  let result := LeanPaper.AxiomWalk.collect env roots\n"
                  "  match LeanPaper.AxiomWalk.check result allowed with\n"
                  "  | .error msg => throwError msg\n  | .ok () => pure ()\n"
                  '  IO.println "' + SENTINEL + '"\n')
        generated = subset_audit_source(source, ["A", "B.C"])
        self.assertTrue(generated.startswith("import A\nimport B.C\n"))
        self.assertIn("`A,\n    `B.C", generated)
        self.assertIn("LeanPaper.AxiomWalk.check result allowed", generated)
        self.assertIn(SUBSET_SENTINEL, generated)
        self.assertNotIn(SENTINEL, generated)
        with self.assertRaises(ValueError):
            subset_audit_source(source, [AUDIT])
        with self.assertRaises(ValueError):
            subset_audit_source(source.replace("``Classical.choice", "``sorryAx"), ["A"])


if __name__ == "__main__":
    unittest.main()
