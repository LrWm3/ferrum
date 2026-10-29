#!/usr/bin/env python3
"""Select pinned-source compatibility inputs without suppressing annotations.

This is a differential corpus, not Silicon's ScalaTest annotation evaluator.
All annotations are preserved as metadata, including ignores and missing outputs.
"""

import argparse
import hashlib
import json
from pathlib import Path


# Suite directories and options come from the named pinned Silicon test classes.
# The per-program deadline is supplied by the executor, separately from selection.
GROUPS = {
    "default": ("SiliconTests", ["consistency", "all", "quantifiedpermissions",
        "quantifiedpredicates", "quantifiedcombinations", "wands", "termination",
        "refute", "examples"], []),
    "sif": ("SiliconTestsSIFPlugin", ["sif"],
        ["--plugin=viper.silver.plugin.sif.SIFPlugin"]),
    "arp": ("ARPPluginTests", ["arp"],
        ["--plugin=viper.silver.plugin.standard.arp.ARPPlugin"]),
    "adt": ("AdtPluginTests", ["adt"],
        ["--plugin=viper.silver.plugin.standard.adt.AdtPlugin"]),
    "quasihavoc": ("SiliconTestsQuasihavoc", ["quasihavoc"],
        ["--enableMoreCompleteExhale"]),
    "greedy_qp": ("SiliconTestsGreedyQP", ["greedyQP"], ["--exhaleModeQP=0"]),
    "complete_exhale": ("SiliconTestsMoreCompleteExhale",
        ["moreCompleteExhale", "issue387"], ["--exhaleMode=1"]),
    "conditional_permissions": ("SiliconTestsConditionalizePermissions",
        ["conditionalizePermissions"], ["--conditionalizePermissions"]),
    "old_permissions": ("SiliconTestsOldPermSemantics", ["oldpermsemantics"],
        ["--respectFunctionPrePermAmounts"]),
    "old_axioms": ("SiliconTestsOldAxiomatization", ["oldaxiomatization"],
        ["--useOldAxiomatization"]),
    "simplified_unfold": ("SiliconTestsSimplifiedUnfold", ["all/predicates"],
        ["--enableSimplifiedUnfolds"]),
    "parallel_examples": ("SiliconTestsParallelBranches", ["examples"],
        ["--parallelizeBranches", "--numberOfParallelVerifiers", "2"]),
    "mask_heap": ("SiliconTestsMaskHeapMode", ["all/basic", "all/functions",
        "all/inhale_exhale", "all/old", "all/permissions", "examples",
        "quantifiedpredicates/basic", "quantifiedcombinations", "wands/mwsf",
        "wands/examples"], ["--maskHeapMode"]),
}


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def select(roots, groups):
    rows = []
    for group in groups:
        test_class, directories, options = GROUPS[group]
        for repository, root in roots.items():
            selected = set()
            for directory in directories:
                selected.update(p.resolve() for p in
                    (root / "src/test/resources" / directory).rglob("*.vpr")
                    if p.is_file())
            for path in sorted(selected):
                relative = str(path.relative_to(root))
                annotations = [{"line": number, "text": line.strip()}
                    for number, line in enumerate(path.read_text().splitlines(), 1)
                    if "::" in line and "//" in line]
                rows.append({"key": f"{group}/{repository}/{relative}",
                    "group": group, "repository": repository, "path": str(path),
                    "relative_path": relative, "sha256": digest(path),
                    "options": options, "source_test_class": test_class,
                    "annotations": annotations})
    return rows


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--silver", type=Path, required=True)
    parser.add_argument("--silicon", type=Path, required=True)
    parser.add_argument("--group", action="append", choices=GROUPS)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    roots = {name: getattr(args, name).resolve() for name in ("silver", "silicon")}
    groups = args.group or list(GROUPS)
    rows = select(roots, groups)
    counts = {group: sum(row["group"] == group for row in rows) for group in groups}
    if not rows or not all(counts.values()):
        parser.error(f"empty selection or suite: {counts}")
    data = {"kind": "selected_differential_corpus", "counts": counts,
        "limitations": ["Only .vpr inputs are selected; .sil files are excluded.",
            "Annotations are retained, not interpreted or used to suppress cases.",
            "Options follow named source classes except executor time limits and worker count.",
            "Import and binary hashes belong in the separate evidence manifest."],
        "cases": rows}
    args.output.write_text(json.dumps(data, indent=2) + "\n")
    print(json.dumps({"total": len(rows), "counts": counts}, indent=2))


if __name__ == "__main__":
    main()
