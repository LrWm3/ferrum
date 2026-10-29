#!/usr/bin/env python3
"""Recheck historically unparsed paired diagnostics against retained reference output.

The reference results must be from tools/compare_upstream.py. The source fixture
paths are taken from its commands. Raw native output is retained; timeouts, crashes,
missing diagnostics and multiline reference messages are never counted as matches.
"""
import argparse
import collections
import concurrent.futures
import hashlib
import json
import os
from pathlib import Path
import re
import signal
import subprocess

POSITION = re.compile(r'\([^()]*@\d+\.\d+(?:--\d+\.\d+)?\)$')
NUMBERED = re.compile(r'^\s*\[\s*\d+\]\s+(.*)')
NATIVE_ID = re.compile(r'^\[[^]]+\]\s*')


def digest(path):
    with Path(path).open('rb') as stream:
        return hashlib.file_digest(stream, 'sha256').hexdigest()


def classify(output, returncode, timed_out, source, reference_verified=True):
    reference_lines = [match.group(1) for line in source['output'].splitlines()
                       if (match := NUMBERED.match(line))]
    native_lines = []
    for line in output.splitlines():
        line = NATIVE_ID.sub('', line.strip())
        if POSITION.search(line):
            native_lines.append(line)
    unavailable = (timed_out or returncode is None or returncode <= 0
                   or source.get('exit_code') == 0
                   or 'panicked at' in output or 'aborted exceptionally' in output
                   or 'Backend(Execution(' in output or 'Unsupported(' in output
                   or 'not connected' in output or 'timeout.error' in output
                   or 'Verification timed out' in output
                   or source['outcome'] in ('harness_timeout', 'process_crash',
                                            'execution_error', 'verifier_timeout')
                   or not native_lines or not reference_lines)
    if unavailable:
        category = 'unavailable'
    elif any(not POSITION.search(line) for line in reference_lines):
        category = 'multiline_review'
    elif not reference_verified:
        category = 'unverified_reference_review'
    elif native_lines == reference_lines:
        category = 'identical_diagnostic_lines'
    else:
        category = 'different_diagnostic_lines'
    return category, native_lines, reference_lines


def compare_case(row, binary, z3, timeout, reference_verified):
    source = row['silicon']
    # Use the exact reference input validated against the manifest below.
    fixture = source['command'][-1]
    command = [str(binary), '--z3Exe', str(z3), '--disableCaches',
               '--numberOfParallelVerifiers', '1', fixture]
    process = subprocess.Popen(command, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                               start_new_session=True)
    timed_out = False
    try:
        output, _ = process.communicate(timeout=timeout)
    except subprocess.TimeoutExpired:
        timed_out = True
        os.killpg(process.pid, signal.SIGKILL)
        output, _ = process.communicate()
    finally:
        try:
            os.killpg(process.pid, signal.SIGKILL)
        except ProcessLookupError:
            pass
    output = output.decode('utf-8', errors='replace')
    category, native_lines, reference_lines = classify(output, process.returncode, timed_out, source, reference_verified)
    return {'fixture': row['fixture'], 'category': category, 'command': command,
            'native_exit_code': process.returncode, 'timed_out': timed_out,
            'native_lines': native_lines, 'reference_lines': reference_lines,
            'native_output': output, 'reference_output': source['output']}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--results', type=Path, required=True)
    parser.add_argument('--binary', type=Path, required=True)
    parser.add_argument('--z3', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--jobs', type=int, default=4)
    parser.add_argument('--timeout', type=float, default=20)
    parser.add_argument('--limit', type=int)
    parser.add_argument('--reference-manifest', type=Path, help='defaults to manifest.json beside --results')
    parser.add_argument('--allow-unverified-reference', action='store_true', help='review only; never classify matches')
    args = parser.parse_args()
    if args.jobs < 1 or args.timeout <= 0 or (args.limit is not None and args.limit < 1):
        parser.error('jobs, timeout and limit must be positive')
    rows = [json.loads(line) for line in args.results.read_text().splitlines()]
    rows = [row for row in rows if row['comparison'] == 'review_both_failed'
            and (row['ferrum']['outcome'], row['silicon']['outcome']) !=
                ('verification_failure', 'reported_failure')]
    if args.limit is not None:
        rows = rows[:args.limit]
    manifest_path = args.reference_manifest or args.results.with_name('manifest.json')
    try:
        reference_manifest = json.loads(manifest_path.read_text())
        fixtures = {entry['key']: entry for entry in reference_manifest['fixtures']}
        jar = reference_manifest['binaries']['silicon_jar']
        if digest(jar['path']) != jar['sha256']:
            raise ValueError('reference jar hash differs from manifest')
        for row in rows:
            entry = fixtures[row['fixture']]
            if Path(row['silicon']['command'][-1]).resolve() != Path(entry['path']).resolve():
                raise ValueError(f"reference fixture path differs for {row['fixture']}")
            if digest(entry['path']) != entry['sha256']:
                raise ValueError(f"reference fixture hash differs for {row['fixture']}")
        reference_verified = True
        reference_issue = None
    except (OSError, ValueError, KeyError, TypeError) as error:
        reference_verified = False
        reference_issue = str(error)
        if not args.allow_unverified_reference:
            parser.error(f'reference manifest verification failed: {error}')
    with concurrent.futures.ThreadPoolExecutor(max_workers=args.jobs) as pool:
        results = list(pool.map(lambda row: compare_case(row, args.binary, args.z3, args.timeout, reference_verified), rows))
    result = {'manifest': {'kind': 'diagnostic_line_review', 'results': str(args.results),
                           'results_sha256': digest(args.results), 'binary': str(args.binary),
                           'binary_sha256': digest(args.binary), 'z3': str(args.z3),
                           'z3_sha256': digest(args.z3), 'jobs': args.jobs,
                           'timeout_seconds': args.timeout, 'case_count': len(results),
                           'reference_manifest': str(manifest_path),
                           'reference_verified': reference_verified, 'reference_issue': reference_issue,
                           'limitations': ['Reference result authenticity is limited to the supplied manifest and retained output',
                                           'Multiline reference diagnostics require manual review',
                                           'Identical lines do not establish full semantic compatibility']},
              'counts': dict(collections.Counter(row['category'] for row in results)),
              'cases': results}
    with args.output.open('x') as stream:
        json.dump(result, stream, indent=2)
        stream.write('\n')
    print(json.dumps(result['counts'], sort_keys=True))


if __name__ == '__main__':
    main()
