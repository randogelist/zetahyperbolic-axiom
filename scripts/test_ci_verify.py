"""Scheduler regression tests; never invoke Lean, Lake or any compiler."""
import unittest

from ci_verify import schedule


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


if __name__ == "__main__":
    unittest.main()
