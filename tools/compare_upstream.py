#!/usr/bin/env python3
"""Run a reproducible, bounded CLI comparison against pinned Silicon fixtures.

This is coarse outcome triage, not the upstream annotation harness or proof of
diagnostic compatibility. Full output is retained for reviewing each mismatch.
Each invocation is cold; the timings are not warm-session performance results.
"""

import argparse
import concurrent.futures
import hashlib
import json
import os
from pathlib import Path
import re
import signal
import subprocess
import time


SUITES = (
    "consistency", "all", "quantifiedpermissions", "quantifiedpredicates",
    "quantifiedcombinations", "wands", "termination", "refute", "examples",
)


def sha256(path):
    with Path(path).open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()


def classify(backend, code, output, timed_out):
    if timed_out:
        return "harness_timeout"
    if code < 0:
        return "process_crash"
    if "timeout.error" in output or "Verification timed out" in output:
        return "verifier_timeout"
    if "aborted exceptionally" in output or "panicked at" in output:
        return "execution_error"
    if backend == "ferrum":
        if code == 0 and "Verification succeeded" in output:
            return "verified"
        if "Unsupported(" in output or "not connected" in output:
            return "unsupported"
        if code == 1 and "Verification failed with" in output:
            return "verification_failure"
        return "frontend_or_execution_error"
    if code == 0 and "finished verification successfully" in output:
        return "verified"
    # The source CLI prints frontend and verification errors using one message.
    # Do not infer verification failure from its exit status alone.
    if re.search(r"Silicon found \d+ errors?", output):
        return "reported_failure"
    return "frontend_or_execution_error"


def compare(native, reference):
    if native["outcome"] == reference["outcome"] == "verified":
        return "same_success"
    if reference["outcome"] == "verified":
        return "native_rejection_or_failure"
    if native["outcome"] == "verified":
        if reference["outcome"] in ("reported_failure", "frontend_or_execution_error"):
            return "review_native_success"
        return "reference_inconclusive"
    # Equal nonzero exits cannot establish matching obligations or diagnostics.
    return "review_both_failed"


def run(backend, command, timeout):
    started = time.monotonic()
    child = subprocess.Popen(
        command, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
        start_new_session=True,
    )
    timed_out = False
    try:
        output, _ = child.communicate(timeout=timeout)
    except subprocess.TimeoutExpired:
        timed_out = True
        os.killpg(child.pid, signal.SIGKILL)
        output, _ = child.communicate()
    finally:
        # Also clean up descendants if a verifier crashes without stopping Z3.
        try:
            os.killpg(child.pid, signal.SIGKILL)
        except ProcessLookupError:
            pass
    output = output.decode("utf-8", errors="replace")
    return {
        "command": command, "exit_code": child.returncode,
        "wall_seconds": time.monotonic() - started,
        "outcome": classify(backend, child.returncode, output, timed_out),
        "output": output,
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--ferrum", type=Path, required=True)
    parser.add_argument("--silicon-jar", type=Path, required=True)
    parser.add_argument("--java", type=Path, required=True)
    parser.add_argument("--z3", type=Path, required=True)
    parser.add_argument("--silver", type=Path, default=Path("../silver"))
    parser.add_argument("--silicon", type=Path, default=Path("../silicon"))
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--suite", action="append", choices=SUITES)
    parser.add_argument("--filter", default="", help="substring of relative fixture path")
    parser.add_argument("--limit", type=int)
    parser.add_argument("--jobs", type=int, default=2)
    parser.add_argument("--timeout", type=float, default=30)
    parser.add_argument("--workers", type=int, default=1)
    parser.add_argument("--parallel-branches", action="store_true")
    args = parser.parse_args()
    if args.jobs < 1 or args.workers < 1 or args.timeout <= 0:
        parser.error("jobs, workers and timeout must be positive")
    if args.limit is not None and args.limit < 1:
        parser.error("limit must be positive")
    args.output.mkdir(parents=True, exist_ok=False)
    binaries = {name: getattr(args, name).resolve()
                for name in ("ferrum", "silicon_jar", "java", "z3")}
    revisions = {}
    fixtures = []
    for repo in ("silver", "silicon"):
        checkout = getattr(args, repo).resolve()
        revisions[repo] = subprocess.check_output(
            ["git", "rev-parse", "HEAD"], cwd=checkout, text=True,
        ).strip()
        for suite in args.suite or SUITES:
            root = checkout / "src/test/resources" / suite
            for path in root.rglob("*.vpr"):
                key = f"{repo}/{path.relative_to(checkout)}"
                if args.filter in key:
                    fixtures.append((key, path))
    fixtures.sort()
    if args.limit:
        fixtures = fixtures[:args.limit]
    if not fixtures:
        parser.error("no matching fixtures")
    common = ["--z3Exe", str(binaries["z3"]), "--disableCaches",
              "--numberOfParallelVerifiers", str(args.workers)]
    if args.parallel_branches:
        common.append("--parallelizeBranches")
    metadata = {
        "kind": "cold_cli_outcome_triage", "revisions": revisions,
        "binaries": {name: {"path": str(path), "sha256": sha256(path)}
                     for name, path in binaries.items()},
        "timeout_seconds": args.timeout, "jobs": args.jobs, "options": common,
        "fixtures": [{"key": key, "path": str(path), "sha256": sha256(path)}
                     for key, path in fixtures],
        "limitations": ["failure IDs and locations require separate review",
                        "same_success is not full compatibility",
                        "timings include process/JVM startup and concurrent load"],
    }
    (args.output / "manifest.json").write_text(json.dumps(metadata, indent=2) + "\n")

    def check(item):
        key, path = item
        native = run("ferrum", [str(binaries["ferrum"]), *common, str(path)], args.timeout)
        reference = run("silicon", [str(binaries["java"]), "-Xss128m", "-jar",
                        str(binaries["silicon_jar"]), *common, str(path)], args.timeout)
        return {"fixture": key, "comparison": compare(native, reference),
                "ferrum": native, "silicon": reference}

    counts = {}
    with (args.output / "results.jsonl").open("w") as stream:
        with concurrent.futures.ThreadPoolExecutor(max_workers=args.jobs) as pool:
            tasks = [pool.submit(check, item) for item in fixtures]
            for task in concurrent.futures.as_completed(tasks):
                result = task.result()
                stream.write(json.dumps(result) + "\n")
                stream.flush()
                category = result["comparison"]
                counts[category] = counts.get(category, 0) + 1
                print(f"{result['fixture']}: {category}", flush=True)
    (args.output / "summary.json").write_text(json.dumps(counts, indent=2) + "\n")
    print(json.dumps(counts, sort_keys=True))


if __name__ == "__main__":
    main()
