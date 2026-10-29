#!/usr/bin/env python3
"""Freeze compatibility inputs and compare structured verifier observations.

The input inventory hashes every .vpr resource under each source checkout, a
conservative superset of imported files (including bundled library resources).
JSON observations must be obtained from verifier error objects, not CLI exit
codes. Missing IDs or positions make failure comparison inconclusive.
"""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess


def digest(path):
    with path.open('rb') as stream:
        return hashlib.file_digest(stream, 'sha256').hexdigest()


def revision(root):
    return subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=root, text=True).strip()


def inventory(root):
    return {str(p.relative_to(root)): digest(p) for p in sorted(root.rglob('*.vpr')) if p.is_file()}


def compare(source, native):
    # A per-case row is usable only if its enclosing process completed normally.
    if any(x.get('session_outcome') != 'completed' or x.get('exit_code') != 0 for x in (source, native)):
        return 'session_inconclusive'
    if source['outcome'] == native['outcome'] == 'verified':
        return 'both_verified' if all(x.get('errors') == [] for x in (source, native)) else 'invalid_success_evidence'
    if source['outcome'] != native['outcome']:
        return 'different_outcome'
    if source['outcome'] != 'failure':
        return 'inconclusive'
    a, b = source.get('errors'), native.get('errors')
    if any(e.get('id') == 'timeout.error' for e in (a or []) + (b or [])):
        return 'inconclusive'
    if not a or not b or any(not e.get('id') or not e.get('position') or e['position'] == '<no position>' for e in a + b):
        return 'failure_evidence_incomplete'
    key = lambda e: (e['id'], e['position'])
    return 'same_ids_positions' if sorted(map(key, a)) == sorted(map(key, b)) else 'different_ids_positions'


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest='action', required=True)
    freeze = sub.add_parser('freeze')
    for name in ('silver', 'silicon', 'jar', 'java', 'z3', 'native', 'output'):
        freeze.add_argument('--' + name, type=Path, required=True)
    freeze.add_argument('--artifact', type=Path, action='append', default=[], help='extra driver, class, native library or external import file; repeat as needed')
    comparison = sub.add_parser('compare')
    comparison.add_argument('observations', type=Path, help='JSON array with source/native observation pairs')
    args = parser.parse_args()
    if args.action == 'compare':
        for row in json.loads(args.observations.read_text()):
            print(json.dumps({'case': row['case'], 'comparison': compare(row['source'], row['native'])}))
        return
    expected = {'silver': 'c4f54b84703a04434b03e97bfea87dbd09870fd2',
                'silicon': 'ff386aec4664231dc6f2cb56d8d35f1623088363'}
    repositories = {}
    for name, expected_rev in expected.items():
        root = getattr(args, name).resolve()
        actual = revision(root)
        if actual != expected_rev:
            parser.error(f'{name} revision {actual} does not match {expected_rev}')
        status = subprocess.check_output(['git', 'status', '--porcelain', '--untracked-files=all'], cwd=root, text=True)
        repositories[name] = {'root': str(root), 'revision': actual, 'git_status': status, 'vpr_files': inventory(root)}
    binaries = {name: {'path': str(getattr(args, name).resolve()), 'sha256': digest(getattr(args, name))}
                for name in ('jar', 'java', 'z3', 'native')}
    if binaries['jar']['sha256'] != 'bcab94591994788e41a62fa673f1001339ac2323ef58e27d428a7ca739c12726':
        parser.error('unexpected source jar hash')
    extra = [{'path': str(p.resolve()), 'sha256': digest(p)} for p in args.artifact]
    args.output.write_text(json.dumps({'repositories': repositories, 'binaries': binaries, 'extra_artifacts': extra}, indent=2) + '\n')


if __name__ == '__main__':
    main()
