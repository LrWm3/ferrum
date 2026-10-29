"""Keep diagnostic comparisons conservative when output is incomplete."""

import unittest

from compare_diagnostics import classify


class DiagnosticComparisonTests(unittest.TestCase):
    message = "undeclared identifier `x` (test.vpr@2.3--2.4)"

    def source(self, **changes):
        source = {
            "output": f"Silicon found 1 error:\n  [ 0] {self.message}\n",
            "exit_code": 1,
            "outcome": "reported_failure",
        }
        source.update(changes)
        return source

    def test_padded_indices_and_native_ids(self):
        category, native, source = classify(
            "[typechecker.error] " + self.message, 2, False, self.source()
        )
        self.assertEqual(category, "identical_diagnostic_lines")
        self.assertEqual(native, source)

    def test_matching_prefix_does_not_hide_incomplete_execution(self):
        for ending in (
            "panicked at failure", "aborted exceptionally", "Unsupported(feature)",
            "Backend(Execution(error))", "not connected", "[timeout.error]",
            "Verification timed out",
        ):
            with self.subTest(ending=ending):
                category, _, _ = classify(
                    self.message + "\n" + ending, 2, False, self.source()
                )
                self.assertEqual(category, "unavailable")
        for code, timed_out in ((0, False), (-11, False), (-9, True), (None, True)):
            self.assertEqual(
                classify(self.message, code, timed_out, self.source())[0],
                "unavailable",
            )

    def test_reference_failures_and_missing_lines_are_inconclusive(self):
        for outcome in ("harness_timeout", "process_crash", "execution_error", "verifier_timeout"):
            self.assertEqual(
                classify(self.message, 2, False, self.source(outcome=outcome))[0],
                "unavailable",
            )
        self.assertEqual(classify(self.message, 2, False, self.source(exit_code=0))[0], "unavailable")
        self.assertEqual(classify("", 2, False, self.source())[0], "unavailable")
        self.assertEqual(classify(self.message, 2, False, self.source(output=""))[0], "unavailable")

    def test_multiline_and_unverified_reference_require_review(self):
        source = self.source(output="[ 0] parse-tree failure\n  detail (test.vpr@2.3--2.4)")
        self.assertEqual(classify(self.message, 2, False, source)[0], "multiline_review")
        self.assertEqual(
            classify(self.message, 2, False, self.source(), reference_verified=False)[0],
            "unverified_reference_review",
        )

    def test_equal_failures_with_different_messages_are_not_matches(self):
        self.assertEqual(
            classify("another error (test.vpr@2.3--2.4)", 2, False, self.source())[0],
            "different_diagnostic_lines",
        )


if __name__ == "__main__":
    unittest.main()
