#!/usr/bin/env python3
"""Compare selected files in bounded sessions, retaining every failed attempt.

Settings JSON provides source/native command prefixes (through the Z3 argument),
shared_options and optional environment overrides. Each process runs a bounded
batch; failed batches are retried one file at a time without erasing the original
failure. Such retries cannot establish compatibility of session reuse.
"""

import argparse
from collections import Counter, defaultdict
from concurrent.futures import ThreadPoolExecutor, as_completed
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import subprocess
import signal
import shutil
import sys
import traceback


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def observation(session, path):
    records = [row for row in session["records"] if row.get("case") == path]
    row = records[0] if len(records) == 1 else {"outcome": "missing_or_duplicate_result"}
    return {**row, "session_outcome": session["outcome"], "exit_code": session["exit_code"]}


def validate_records(session, expected):
    actual = [r.get("case") for r in session["records"] if "case" in r]
    # The driver stops at an exception; only an ordered prefix is legitimate.
    problems = []
    if actual != expected[:len(actual)]:
        problems.append("case records are not an ordered prefix of requested inputs")
    if len(actual) != len(expected):
        problems.append("not all requested inputs produced records")
    if problems:
        session["outcome"] = "process_error" if session["outcome"] == "completed" else session["outcome"]
    session["coverage_errors"] = problems


def diagnostic_comparison(source, native):
    """Keep reporting differences visible even when proof outcomes agree."""
    if any(r.get("session_outcome") != "completed" or r.get("exit_code") != 0 for r in (source, native)):
        return {"same_error_messages": None, "same_error_order": None, "same_warnings": None, "same_configuration_warnings": None, "same_phase": None}
    a, b = source.get("errors"), native.get("errors")
    complete = all(isinstance(errors, list) and all(isinstance(error, dict)
        and all(isinstance(error.get(key), str) for key in ("id", "position", "message"))
        for error in errors) for errors in (a, b))
    messages = None
    order = None
    if complete:
        key = lambda error: (error["id"], error["position"], error["message"])
        messages = sorted(map(key, a)) == sorted(map(key, b))
        order = a == b
    warnings = None
    if all(isinstance(row.get("warnings"), list) and all(isinstance(w, str)
            for w in row["warnings"]) for row in (source, native)):
        warnings = source["warnings"] == native["warnings"]
    configuration_warnings = None
    if all(isinstance(row.get("configuration_warnings"), list) and all(isinstance(w, str)
            for w in row["configuration_warnings"]) for row in (source, native)):
        configuration_warnings = source["configuration_warnings"] == native["configuration_warnings"]
    # Source state names are an enum; native names describe the same phases.
    phase_names = {"Parsing": "parsing", "SemanticAnalysis": "semantic_analysis",
        "Translation": "translation", "ConsistencyCheck": "consistency",
        "Verification": "verification"}
    phase = None
    if source.get("phase") and native.get("phase"):
        phase = phase_names.get(source["phase"], source["phase"]) == native["phase"]
    return {"same_error_messages": messages, "same_error_order": order,
        "same_warnings": warnings, "same_configuration_warnings": configuration_warnings, "same_phase": phase}


def load_session(path, returncode, command):
    try:
        session = json.loads(path.read_text())
        if not isinstance(session, dict) or not isinstance(session.get("records"), list) or any(not isinstance(r, dict) for r in session["records"]) or not isinstance(session.get("outcome"), str) or not isinstance(session.get("exit_code"), (int, type(None))):
            raise ValueError("invalid session envelope")
        return session
    except (OSError, ValueError) as error:
        return {"outcome": "runner_error", "exit_code": returncode, "command": command,
                "records": [], "runner_result_error": str(error)}


def comparison_scope(pair):
    if any(part["observation"].get("session_outcome") != "completed"
            or part["observation"].get("exit_code") != 0 for part in pair.values()):
        return "incomplete_batch"
    if any(part["isolated_retry_selected"] for part in pair.values()):
        return "isolated_retry"
    return "completed_batch"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--selection", type=Path, required=True)
    parser.add_argument("--settings", type=Path, required=True)
    parser.add_argument("--tools", type=Path, required=True, help="Ferrum tools directory")
    parser.add_argument("--evidence", type=Path, required=True, help="frozen compatibility evidence manifest")
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--jobs", type=int, default=2)
    parser.add_argument("--batch-size", type=int, default=8)
    parser.add_argument("--case-budget", type=float, default=60, help="outer budget per input, including frontend phases")
    parser.add_argument("--grace", type=float, default=30)
    args = parser.parse_args()
    if min(args.jobs, args.batch_size, args.case_budget, args.grace) <= 0:
        parser.error("counts and time budgets must be positive")
    selection = json.loads(args.selection.read_text())
    settings = json.loads(args.settings.read_text())
    evidence = json.loads(args.evidence.read_text())
    rows = selection["cases"]
    if not rows or len({r["key"] for r in rows}) != len(rows):
        parser.error("empty selection or duplicate keys")
    artifacts = list(evidence["binaries"].values()) + evidence.get("extra_artifacts", [])
    frozen = {str(Path(artifact["path"]).resolve()): artifact["sha256"] for artifact in artifacts}
    for path, expected_hash in frozen.items():
        if digest(path) != expected_hash:
            parser.error(f"artifact changed: {path}")
    for repository in evidence["repositories"].values():
        root = Path(repository["root"])
        actual_revision = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=root, text=True).strip()
        actual_status = subprocess.check_output(["git", "status", "--porcelain", "--untracked-files=all"], cwd=root, text=True)
        if actual_revision != repository["revision"] or actual_status != repository["git_status"]:
            parser.error(f"source revision or status changed: {root}")
        current = {str(p.relative_to(root)): digest(p) for p in sorted(root.rglob("*.vpr")) if p.is_file()}
        if current != repository["vpr_files"]:
            parser.error(f"source resource inventory changed: {root}")
    for row in rows:
        if digest(row["path"]) != row["sha256"]:
            parser.error(f"selected file changed: {row['path']}")
    for backend in ("source", "native"):
        prefix = settings.get(backend)
        if not isinstance(prefix, list) or not prefix:
            parser.error(f"missing {backend} command prefix")
        path_environment = settings.get("environment", {}).get("PATH", os.environ.get("PATH"))
        executable = shutil.which(prefix[0], path=path_environment) or prefix[0]
        # Freeze the exact executable selected under the child's environment.
        prefix[0] = str(Path(executable).resolve())
        required = {str(Path(executable).resolve())}
        # File arguments include JVM classpath entries, scripts, jars and Z3.
        for token in prefix[1:]:
            for item in token.split(os.pathsep):
                if Path(item).is_file():
                    required.add(str(Path(item).resolve()))
        declared = settings.get("command_artifacts", {}).get(backend)
        if not isinstance(declared, list):
            parser.error(f"{backend} command_artifacts must be an explicit list")
        for index, token in enumerate(prefix[:-1]):
            if token in ("-cp", "-classpath", "--class-path"):
                for entry in prefix[index + 1].split(os.pathsep):
                    directory = Path(entry)
                    if directory.is_dir():
                        required.update(str(p.resolve()) for p in directory.rglob("*.class") if p.is_file())
        required.update(str(Path(path).resolve()) for path in declared)
        missing = required - frozen.keys()
        if missing:
            parser.error(f"{backend} command artifacts not frozen: {sorted(missing)}")
    runner = args.tools / "compatibility/run_session.py"
    classifier_path = args.tools / "compatibility_evidence.py"
    spec = importlib.util.spec_from_file_location("evidence", classifier_path)
    classifier = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(classifier)
    args.output.mkdir(parents=True, exist_ok=False)
    sessions_dir = args.output / "sessions"
    sessions_dir.mkdir()
    metadata = {"selection": selection, "settings": settings, "evidence": evidence,
        "runner_sha256": digest(runner), "classifier_sha256": digest(classifier_path),
        "orchestrator_sha256": digest(__file__), "batch_size": args.batch_size,
        "jobs": args.jobs, "outer_seconds_per_case": args.case_budget,
        "outer_grace_seconds": args.grace}
    (args.output / "manifest.json").write_text(json.dumps(metadata, indent=2) + "\n")
    groups = defaultdict(list)
    for row in rows:
        groups[(row["group"], tuple(row["options"]))].append(row)
    tasks = []
    for (group, options), members in groups.items():
        for index in range(0, len(members), args.batch_size):
            batch = members[index:index + args.batch_size]
            for backend in ("source", "native"):
                tasks.append((f"{group}-{index:04}-{backend}", backend, list(options), batch))

    def run_session(name, backend, options, batch):
        output = sessions_dir / f"{name}.json"
        command = [*settings[backend], *settings.get("shared_options", []), *options,
            "--", *(r["path"] for r in batch)]
        outer_budget = args.case_budget * len(batch) + args.grace
        supervisor_path = sessions_dir / f"{name}.supervisor.json"
        inner = [sys.executable, str(runner), "--timeout", str(outer_budget),
                 "--output", str(output), "--", *command]
        supervisor = [sys.executable, str(runner), "--timeout", str(outer_budget + 5),
                      "--output", str(supervisor_path), "--", *inner]
        with (sessions_dir / f"{name}.runner.log").open("w") as log:
            process = subprocess.Popen(supervisor,
                env={**os.environ, **settings.get("environment", {})},
                stdout=log, stderr=subprocess.STDOUT, start_new_session=True)
            outer_timeout = False
            try:
                process.wait(timeout=outer_budget + 15)
            except subprocess.TimeoutExpired:
                outer_timeout = True
                try:
                    os.killpg(process.pid, signal.SIGKILL)
                except ProcessLookupError:
                    pass
                process.wait()
        supervision = load_session(supervisor_path, process.returncode, supervisor)
        if output.exists():
            # Never overwrite malformed or partial runner evidence with normalized JSON.
            output.with_suffix(".raw.json").write_bytes(output.read_bytes())
        if outer_timeout or process.returncode or supervision.get("outcome") != "completed" or not output.exists():
            session = {"outcome": "runner_error", "exit_code": process.returncode,
                "outer_timeout": outer_timeout, "command": command, "records": [],
                "cleanup_note": "outer supervisor terminated; detached descendants may survive" if outer_timeout else None, "supervisor": supervision}
        else:
            session = load_session(output, process.returncode, command)
        session["supervisor"] = supervision
        validate_records(session, [r["path"] for r in batch])
        session["keys"] = [r["key"] for r in batch]
        output.write_text(json.dumps(session, indent=2) + "\n")
        return session, str(output)

    def run_batch(task):
        name, backend, options, batch = task
        session, path = run_session(name, backend, options, batch)
        attempts = [{"path": path, "outcome": session["outcome"], "sha256": digest(path)}]
        results = []
        for index, row in enumerate(batch):
            first = observation(session, row["path"])
            chosen = first
            selected_path = path
            if session["outcome"] != "completed" and len(batch) > 1:
                retry, selected_path = run_session(f"{name}-retry-{index:02}", backend, options, [row])
                chosen = observation(retry, row["path"])
                attempts.append({"path": selected_path, "outcome": retry["outcome"], "sha256": digest(selected_path)})
            results.append({"key": row["key"], "backend": backend, "observation": chosen,
                "first_observation": first, "session_path": selected_path,
                "initial_session_path": path, "reused_session_completed": session["outcome"] == "completed",
                "isolated_retry_selected": selected_path != path})
        return {"batch": name, "attempts": attempts, "results": results}

    pairs = defaultdict(dict)
    counts = Counter()
    scopes = Counter()
    failed_initial_sessions = 0
    retry_selected_pairs = 0
    worker_exceptions = []
    with (args.output / "batches.jsonl").open("w") as batch_log, (args.output / "pairs.jsonl").open("w") as pair_log:
        with ThreadPoolExecutor(max_workers=args.jobs) as pool:
            futures = {pool.submit(run_batch, task): task for task in tasks}
            for future in as_completed(futures):
                task = futures[future]
                try:
                    completed = future.result()
                except Exception:
                    name, backend, _, batch = task
                    detail = traceback.format_exc()
                    worker_exceptions.append({"batch": name, "traceback": detail})
                    failure_path = sessions_dir / f"{name}.worker-error.json"
                    failure = {"outcome": "runner_error", "exit_code": None,
                               "records": [], "worker_exception": detail}
                    failure_path.write_text(json.dumps(failure, indent=2) + "\n")
                    results = [{"key": row["key"], "backend": backend,
                                "observation": observation(failure, row["path"]),
                                "first_observation": observation(failure, row["path"]),
                                "session_path": str(failure_path), "initial_session_path": str(failure_path),
                                "reused_session_completed": False, "isolated_retry_selected": False}
                               for row in batch]
                    completed = {"batch": name, "attempts": [{"path": str(failure_path),
                        "outcome": "runner_error", "sha256": digest(failure_path)}], "results": results}
                if completed["attempts"][0]["outcome"] != "completed":
                    failed_initial_sessions += 1
                batch_log.write(json.dumps(completed) + "\n")
                batch_log.flush()
                for result in completed["results"]:
                    pair = pairs[result["key"]]
                    pair[result["backend"]] = result
                    if len(pair) == 2:
                        comparison = classifier.compare(pair["source"]["observation"], pair["native"]["observation"])
                        diagnostics = diagnostic_comparison(pair["source"]["observation"], pair["native"]["observation"])
                        scope = comparison_scope(pair)
                        retry_selected_pairs += any(part["isolated_retry_selected"] for part in pair.values())
                        record = {"key": result["key"], "comparison": comparison,
                            "comparison_scope": scope, "diagnostics": diagnostics, **pair}
                        scopes[scope] += 1
                        counts[comparison] += 1
                        pair_log.write(json.dumps(record) + "\n")
                        pair_log.flush()
                print(json.dumps({"batch": completed["batch"], "paired": sum(counts.values()), "counts": dict(counts)}), flush=True)
    (args.output / "summary.json").write_text(json.dumps({"selected": len(rows),
        "paired": sum(counts.values()), "counts": counts,
        "incomplete_coverage": len(rows) - sum(counts.values()) + scopes["incomplete_batch"],
        "comparison_scopes": scopes, "failed_initial_sessions": failed_initial_sessions,
        "retry_selected_pairs": retry_selected_pairs, "worker_exceptions": worker_exceptions,
        "limitations": ["Initial session failures remain failures even when isolated retries complete.",
            "Matching IDs/positions does not establish message, warning or phase agreement."]}, indent=2) + "\n")


if __name__ == "__main__":
    main()
