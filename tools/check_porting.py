#!/usr/bin/env python3
"""Check port inventory, provenance, stage boundaries and bundled resources."""

import argparse
import csv
import hashlib
from collections import Counter
from pathlib import Path
import subprocess
import tomllib


ROOT = Path(__file__).resolve().parents[1]
HEADINGS = (
    "Upstream", "Purpose", "Planned Rust structure", "Behavior to preserve",
    "Integration", "Rust adaptations", "Open decisions", "Status",
)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("paths", nargs="*", help="Check just these destination files")
    parser.add_argument("--complete", action="store_true", help="Require every file to be described or further along")
    parser.add_argument("--upstream", action="store_true", help="Check inventory against local pinned Git trees")
    args = parser.parse_args()
    sources = tomllib.loads((ROOT / "porting/sources.toml").read_text())["repositories"]
    inventory = tomllib.loads((ROOT / "porting/modules.toml").read_text())
    modules = inventory["modules"]
    scaffolding = inventory["scaffolding"]
    entries = modules + scaffolding
    destinations = [entry["destination"] for entry in entries]
    assert len(destinations) == len(set(destinations)), "Duplicate destinations"
    assert len(destinations) == len({path.casefold() for path in destinations}), "Case collision"
    source_keys = [(entry["repository"], entry["upstream"]) for entry in modules]
    assert len(source_keys) == len(set(source_keys)), "Duplicate source mappings"
    actual = {str(path.relative_to(ROOT)) for base in ("src", "crates", "tests", "examples") for path in (ROOT / base).rglob("*.rs")}
    assert actual == set(destinations), f"Unmapped/missing Rust files: {actual ^ set(destinations)}"
    selected = set(args.paths) if args.paths else set(destinations)
    assert selected <= set(destinations), f"Unknown destination: {selected - set(destinations)}"
    for entry in entries:
        status = entry["status"]
        assert status in ("mapped", "described", "skeleton", "ported", "wired", "validated"), f"Unknown status: {status}"
        if args.complete:
            assert status != "mapped", f"Not described: {entry['destination']}"
        name = entry["destination"]
        if name not in selected:
            continue
        body = (ROOT / name).read_text()
        if not body.strip():
            assert status == "mapped" and not args.complete, f"Missing brief: {name}"
            continue
        if status in ("mapped", "described"):
            assert all(not line.strip() or line.startswith("//!") for line in body.splitlines()), f"Code needs implementation status: {name}"
            for heading in HEADINGS:
                assert f"//! {heading}:" in body, f"Missing {heading}: {name}"
            assert "description only; implementation has not started" in body, f"Incorrect stage: {name}"
        elif entry.get("role") != "assembly":
            assert "//! Status:" in body, f"Missing implementation status: {name}"
            assert "description only; implementation has not started" not in body, f"Stale stage: {name}"
        if "repository" in entry:
            source = sources[entry["repository"]]
            link = f"{source['url']}/blob/{source['revision']}/{entry['upstream']}"
            assert link in body, f"Incorrect pinned source link: {name}"
            if status not in ("mapped", "described"):
                assert "Mozilla Public" in body and "Copyright" in body, f"Missing source attribution: {name}"
        else:
            assert "Ferrum" in body and "PLAN.md" in body, f"Missing assembly provenance: {name}"
    resource_path = ROOT / "porting/resources.toml"
    if resource_path.exists():
        for resource in tomllib.loads(resource_path.read_text())["resources"]:
            data = (ROOT / resource["destination"]).read_bytes()
            assert hashlib.sha256(data).hexdigest() == resource["sha256"], f"Changed bundled resource: {resource['destination']}"
            if args.upstream:
                source = sources[resource["repository"]]
                original = subprocess.check_output(
                    ["git", "show", f"{source['revision']}:{resource['upstream']}"],
                    cwd=ROOT / source["checkout"],
                )
                assert data == original, f"Resource differs from pinned upstream: {resource['destination']}"
    if args.upstream:
        with (ROOT / "porting/non_rust_files.tsv").open(newline="") as stream:
            assets = list(csv.DictReader(stream, delimiter="\t"))
        asset_keys = [(row["repository"], row["upstream"]) for row in assets]
        assert len(asset_keys) == len(set(asset_keys)), "Duplicate ancillary entries"
        assert not set(asset_keys) & set(source_keys), "Source also classified as ancillary"
        assert all(row["disposition"] for row in assets), "Missing disposition"
        for repo, source in sources.items():
            checkout = ROOT / source["checkout"]
            paths = subprocess.check_output(
                ["git", "ls-tree", "-rz", "--name-only", source["revision"]], cwd=checkout
            ).decode().strip("\0").split("\0")
            inventoried = {p for r, p in source_keys + asset_keys if r == repo}
            assert set(paths) == inventoried, f"Upstream inventory differs for {repo}"
    counts = Counter(entry["status"] for entry in entries)
    print(f"Checked {len(selected)} destination(s); {len(modules)} source mappings, {len(scaffolding)} assembly files; {dict(counts)}")


if __name__ == "__main__":
    main()
