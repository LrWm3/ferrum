"""Check that corpus triage never treats crashes or matching failures as success."""

import sys
import unittest

from compare_upstream import classify, compare, run


class ComparisonTests(unittest.TestCase):
    def test_success_requires_exit_code_and_verification_marker(self):
        self.assertEqual(classify("ferrum", 0, "Verification succeeded.", False), "verified")
        self.assertNotEqual(classify("ferrum", 0, "Parsing completed.", False), "verified")
        self.assertNotEqual(classify("ferrum", 2, "Verification succeeded.", False), "verified")

    def test_errors_remain_distinct(self):
        self.assertEqual(classify("ferrum", -11, "", False), "process_crash")
        self.assertEqual(classify("ferrum", -9, "", True), "harness_timeout")
        self.assertEqual(classify("ferrum", 2, 'Unsupported("feature")', False), "unsupported")
        self.assertEqual(classify("ferrum", 1, "[timeout.error]", False), "verifier_timeout")
        self.assertEqual(classify("silicon", 1, "Silicon found 2 errors:", False), "reported_failure")

    def test_matching_failures_are_not_claimed_compatible(self):
        native = {"outcome": "verification_failure"}
        reference = {"outcome": "reported_failure"}
        self.assertEqual(compare(native, reference), "review_both_failed")
        self.assertEqual(compare({"outcome": "verified"}, reference), "review_native_success")
        self.assertEqual(compare(native, {"outcome": "verified"}), "native_rejection_or_failure")
        self.assertEqual(compare({"outcome": "verified"}, {"outcome": "harness_timeout"}),
                         "reference_inconclusive")

    def test_timeout_kills_a_descendant_holding_stdout(self):
        result = run("ferrum", [sys.executable, "-c",
                     "import subprocess,sys; subprocess.Popen([sys.executable,'-c',"
                     "'import time; time.sleep(60)'])"], timeout=0.1)
        self.assertEqual(result["outcome"], "harness_timeout")
        self.assertLess(result["wall_seconds"], 5)


if __name__ == "__main__":
    unittest.main()
