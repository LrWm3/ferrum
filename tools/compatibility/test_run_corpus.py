import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

import run_corpus


class CorpusEvidence(unittest.TestCase):
    def test_failed_isolated_retry_remains_incomplete(self):
        result = {"isolated_retry_selected": True, "observation": {
            "session_outcome": "process_error", "exit_code": 0}}
        self.assertEqual(run_corpus.comparison_scope({"source": result, "native": result}),
            "incomplete_batch")
        result["observation"]["session_outcome"] = "completed"
        self.assertEqual(run_corpus.comparison_scope({"source": result, "native": result}),
            "isolated_retry")

    def test_new_ignored_resource_invalidates_frozen_inventory(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            repository = root / "reference"
            repository.mkdir()
            subprocess.run(["git", "init", "--quiet", str(repository)], check=True)
            source = repository / "input.vpr"
            source.write_text("method test() {}\n")
            (repository / ".gitignore").write_text("ignored.vpr\n")
            subprocess.run(["git", "add", "."], cwd=repository, check=True)
            subprocess.run(["git", "-c", "user.name=Fixture", "-c", "user.email=fixture@example.invalid",
                "commit", "--quiet", "-m", "fixture: Freeze resources"], cwd=repository, check=True)
            revision = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=repository, text=True).strip()
            selection = root / "selection.json"
            selection.write_text(json.dumps({"cases": [{"key": "input", "path": str(source),
                "sha256": run_corpus.digest(source), "group": "test", "options": []}]}))
            settings = root / "settings.json"
            settings.write_text("{}")
            evidence = root / "evidence.json"
            evidence.write_text(json.dumps({"binaries": {}, "repositories": {"source": {
                "root": str(repository), "revision": revision, "git_status": "",
                "vpr_files": {"input.vpr": run_corpus.digest(source)}}}}))
            command = [sys.executable, str(Path(run_corpus.__file__)), "--selection", str(selection),
                "--settings", str(settings), "--evidence", str(evidence), "--tools", str(root),
                "--output", str(root / "out")]
            initial = subprocess.run(command, capture_output=True, text=True, timeout=5)
            self.assertIn("missing source command prefix", initial.stderr)
            (repository / "ignored.vpr").write_text("method added() {}\n")
            self.assertEqual(subprocess.check_output(["git", "status", "--porcelain",
                "--untracked-files=all"], cwd=repository, text=True), "")
            changed = subprocess.run(command, capture_output=True, text=True, timeout=5)
            self.assertNotEqual(changed.returncode, 0)
            self.assertIn("source resource inventory changed", changed.stderr)

    def test_messages_warnings_and_phases_are_not_hidden_by_matching_ids(self):
        source = {"session_outcome": "completed", "exit_code": 0, "phase": "Verification", "warnings": ["warning"], "errors": [
            {"id": "assert.failed:assertion.false", "position": "1.1", "message": "source"}]}
        native = {"session_outcome": "completed", "exit_code": 0, "phase": "verification", "warnings": [], "errors": [
            {"id": "assert.failed:assertion.false", "position": "1.1", "message": "native"}]}
        self.assertEqual(run_corpus.diagnostic_comparison(source, native), {
            "same_error_messages": False, "same_error_order": False,
            "same_warnings": False, "same_configuration_warnings": None, "same_phase": True})
        source["configuration_warnings"] = ["config"]
        self.assertIsNone(run_corpus.diagnostic_comparison(source, native)["same_configuration_warnings"])
        native["configuration_warnings"] = []
        self.assertFalse(run_corpus.diagnostic_comparison(source, native)["same_configuration_warnings"])
        native["configuration_warnings"] = ["config"]
        self.assertTrue(run_corpus.diagnostic_comparison(source, native)["same_configuration_warnings"])
        self.assertIsNone(run_corpus.diagnostic_comparison({}, {})["same_error_messages"])
        bad = {**native, "session_outcome": "process_error"}
        self.assertTrue(all(value is None for value in run_corpus.diagnostic_comparison(source, bad).values()))

    def test_malformed_runner_result_is_retained(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "result.json"
            for text in ("{", "[]", '{"records":{}}'):
                path.write_text(text)
                result = run_corpus.load_session(path, 0, ["driver"])
                self.assertEqual(result["outcome"], "runner_error")
                self.assertIn("runner_result_error", result)

    def test_record_order_and_coverage_are_required(self):
        for records in ([{"case": "b"}, {"case": "a"}], [{"case": "a"}],
                        [{"case": "a"}, {"case": "a"}]):
            session = {"outcome": "completed", "records": records}
            run_corpus.validate_records(session, ["a", "b"])
            self.assertEqual(session["outcome"], "process_error")
            self.assertTrue(session["coverage_errors"])

    def test_failed_reuse_is_retained_after_successful_isolated_retry(self):
        tools = Path(os.environ.get("FERRUM_COMPATIBILITY_TOOLS",
            str(Path(__file__).resolve().parents[1])))
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            rows = []
            for name in ("pass", "crash", "difference"):
                path = root / f"{name}.vpr"
                path.write_text(f"method {name}() {{}}\n")
                rows.append({"key": name, "group": "test", "path": str(path),
                    "sha256": run_corpus.digest(path), "options": []})
            driver = root / "driver.py"
            driver.write_text('''import json, pathlib, sys
mode = sys.argv[1]
files = sys.argv[sys.argv.index("--") + 1:]
for path in files:
    stem = pathlib.Path(path).stem
    if stem == "crash" and len(files) > 1:
        print("@@COMPAT@@" + json.dumps({"case": path, "outcome": "failure", "errors": [{"id": "prover.interaction.failed", "position": "<no position>", "message": "solver protocol"}]}))
        break
    failure = mode == "native" and stem == "difference"
    print("@@COMPAT@@" + json.dumps({"case": path, "outcome": "failure" if failure else "verified", "errors": [{"id": "assert.failed:assertion.false", "position": "1.1"}] if failure else []}))
''')
            selection = root / "selection.json"
            selection.write_text(json.dumps({"cases": rows}))
            settings = root / "settings.json"
            settings.write_text(json.dumps({**{mode: [sys.executable, str(driver), mode]
                for mode in ("source", "native")}, "command_artifacts": {"source": [], "native": []}}))
            evidence = root / "evidence.json"
            evidence.write_text(json.dumps({"binaries": {"driver": {
                "path": str(driver), "sha256": run_corpus.digest(driver)}, "python": {"path": sys.executable, "sha256": run_corpus.digest(sys.executable)}}, "repositories": {}}))
            output = root / "out"
            command = [sys.executable, str(Path(run_corpus.__file__)), "--selection", str(selection),
                "--settings", str(settings), "--evidence", str(evidence), "--tools", str(tools),
                "--output", str(output), "--jobs", "2", "--batch-size", "3", "--case-budget", "2", "--grace", "1"]
            process = subprocess.run(command, capture_output=True, text=True, timeout=30)
            self.assertEqual(process.returncode, 0, process.stderr)
            pairs = [json.loads(line) for line in (output / "pairs.jsonl").read_text().splitlines()]
            self.assertEqual(len(pairs), 3)
            summary = json.loads((output / "summary.json").read_text())
            self.assertEqual(summary["retry_selected_pairs"], 3)
            self.assertEqual(summary["failed_initial_sessions"], 2)
            self.assertTrue(all(pair["comparison_scope"] == "isolated_retry" for pair in pairs))
            comparisons = {pair["key"]: pair["comparison"] for pair in pairs}
            self.assertEqual(comparisons, {"pass": "both_verified", "crash": "both_verified", "difference": "different_outcome"})
            for pair in pairs:
                for mode in ("source", "native"):
                    self.assertEqual(pair[mode]["first_observation"]["session_outcome"], "process_error")
                    self.assertNotEqual(pair[mode]["initial_session_path"], pair[mode]["session_path"])
                    self.assertFalse(pair[mode]["reused_session_completed"])
                    self.assertTrue(pair[mode]["isolated_retry_selected"])
            first = next(pair for pair in pairs if pair["key"] == "crash")["source"]["first_observation"]
            self.assertEqual(first["outcome"], "prover_error")
            self.assertEqual(first["errors"][0]["id"], "prover.interaction.failed")
            self.assertEqual(first["errors"][0]["message"], "solver protocol")
            # Omitting an executable from the manifest must prevent execution.
            evidence_data = json.loads(evidence.read_text())
            missing = dict(evidence_data)
            missing["binaries"] = {"python": evidence_data["binaries"]["python"]}
            evidence.write_text(json.dumps(missing))
            rejected = subprocess.run(command, capture_output=True, text=True, timeout=5)
            self.assertNotEqual(rejected.returncode, 0)
            self.assertIn("command artifacts not frozen", rejected.stderr)
            evidence.write_text(json.dumps(evidence_data))
            # Mutating any frozen executable/input artifact must prevent execution.
            driver.write_text(driver.read_text() + "\n# changed\n")
            rejected = subprocess.run(command, capture_output=True, text=True, timeout=5)
            self.assertNotEqual(rejected.returncode, 0)
            self.assertIn("artifact changed", rejected.stderr)


if __name__ == "__main__":
    unittest.main()
