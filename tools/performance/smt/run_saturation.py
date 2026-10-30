#!/usr/bin/env python3
"""Run a frozen serial saturation experiment and retain every observation."""
import argparse
from collections import Counter
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import random
import re
import resource
import subprocess
import sys
import time

from analyze_trace import analyze, expressions


def sha(path):
    digest = hashlib.sha256()
    with Path(path).open('rb') as source:
        for chunk in iter(lambda: source.read(1024 * 1024), b''):
            digest.update(chunk)
    return digest.hexdigest()


def write(path, value):
    path.write_text(json.dumps(value, indent=2) + '\n')


def schedule(spec):
    rng = random.Random(spec['seed'])
    blocks = []
    for case in spec['cases']:
        count = 1 if case['control'] else spec['repetitions']
        for repetition in range(count):
            rows = [{'case': case['name'], 'profile': profile, 'backend': backend,
                     'repetition': repetition, 'control': case['control']}
                    for profile in case['profiles'] for backend in ('ferrum', 'silicon')]
            rng.shuffle(rows)
            blocks.append(rows)
    # Controls are readiness gates; main blocks are randomized only after them.
    controls = [rows for rows in blocks if rows[0]['control']]
    main = [rows for rows in blocks if not rows[0]['control']]
    rng.shuffle(main)
    rows = [row for block in controls + main for row in block]
    return [dict(row, index=index) for index, row in enumerate(rows)]


def check_outcome(session, case):
    if session['outcome'] != 'completed' or session['cleanup_pending'] or session['protocol_errors']:
        return False
    records = session['records']
    if len(records) != 1 or records[0].get('outcome') != case['expect']['outcome']:
        return False
    errors = sorted((e['id'], e['position']) for e in records[0].get('errors', []))
    expected = sorted((e['id'], e['position']) for e in case['expect']['errors'])
    return errors == expected


def offline(spec, folder, report, affinity):
    raw = (folder / 'stdin.bin').read_bytes()
    payload = raw + b'\n(get-info :all-statistics)\n'
    output = folder / 'offline'
    output.mkdir()
    (output / 'input.smt2').write_bytes(payload)
    command = ['taskset', '--cpu-list', affinity, spec['z3'], '-smt2', '-in']
    before = resource.getrusage(resource.RUSAGE_CHILDREN)
    start = time.monotonic()
    timed_out = False
    with (output / 'stdout.bin').open('wb') as stdout, (output / 'stderr.bin').open('wb') as stderr:
        try:
            result = subprocess.run(command, input=payload, stdout=stdout, stderr=stderr,
                                    timeout=spec['offline_timeout'])
            exit_code = result.returncode
        except subprocess.TimeoutExpired:
            timed_out, exit_code = True, None
    after = resource.getrusage(resource.RUSAGE_CHILDREN)
    record = {'command': command, 'exit_code': exit_code, 'timed_out': timed_out,
              'wall_s': time.monotonic() - start,
              'user_cpu_s': after.ru_utime - before.ru_utime,
              'system_cpu_s': after.ru_stime - before.ru_stime,
              'input_sha256': sha(output / 'input.smt2'),
              'stdout_sha256': sha(output / 'stdout.bin'), 'statistics': {},
              'original_response_prefix_equal': False}
    if exit_code == 0 and not timed_out:
        data = (output / 'stdout.bin').read_bytes()
        tokens = [data[a:b] for a, b in expressions(data)]
        original = (folder / 'stdout.bin').read_bytes()
        expected = [original[a:b] for a, b in expressions(original)]
        record['original_response_prefix_equal'] = len(tokens) == len(expected) + 1 and tokens[:-1] == expected
        if record['original_response_prefix_equal']:
            record['statistics'] = dict(re.findall(r':([^\s()]+)\s+([^\s()]+)', tokens[-1].decode()))
            (output / 'statistics.txt').write_bytes(tokens[-1] + b'\n')
    record['stderr'] = (output / 'stderr.bin').read_text(errors='replace')
    write(output / 'result.json', record)
    return record


def trial(spec, row, root):
    case = next(c for c in spec['cases'] if c['name'] == row['case'])
    folder = root / f"{row['index']:03d}-{row['case']}-{row['profile']}-{row['backend']}"
    folder.mkdir()
    weights = spec['profiles'][row['profile']]['weights']
    options = [*spec['options'], '--proverSaturationTimeout', '100',
               '--proverSaturationTimeoutWeights', weights,
               '--proverLogFile', str(folder / 'prover')]
    if row['backend'] == 'ferrum':
        options += ['--parallelizeBranches=false']
    command = ['taskset', '--cpu-list', spec['cpu_affinity'],
               *spec['commands'][row['backend']], spec['proxy'], *options, '--', case['path']]
    env = {**os.environ, 'FERRUM_BENCH_INTERNAL_CACHES': 'on',
           'FERRUM_SMT_REAL_Z3': spec['z3'], 'FERRUM_SMT_TRACE_ROOT': str(folder / 'traces')}
    supervisor = [sys.executable, spec['supervisor'], '--timeout', str(spec['outer_timeout']),
                  '--output', str(folder / 'session.json'), '--', *command]
    print('START', row['index'], row['case'], row['profile'], row['backend'], flush=True)
    started = datetime.now(timezone.utc).isoformat()
    load_before = Path('/proc/loadavg').read_text().strip()
    result = subprocess.run(supervisor, env=env, capture_output=True, text=True)
    (folder / 'supervisor.txt').write_text(result.stdout + result.stderr)
    session = json.loads((folder / 'session.json').read_text())
    record = {**row, 'folder': str(folder), 'command': command, 'supervisor': supervisor,
              'started_utc': started, 'capture_finished_utc': datetime.now(timezone.utc).isoformat(),
              'load_before': load_before, 'load_after_capture': Path('/proc/loadavg').read_text().strip(),
              'supervisor_exit': result.returncode, 'wall_s': session['wall_seconds'],
              'outcome_valid': result.returncode == 0 and check_outcome(session, case),
              'session_outcome': session['outcome'], 'records': session['records'],
              'cleanup_pending': session['cleanup_pending'], 'traces': [], 'issues': []}
    for capture in sorted((folder / 'traces').iterdir()):
        metadata = json.loads((capture / 'metadata.json').read_text())
        if '-in' not in metadata['argv']:
            continue
        try:
            report = analyze(capture)
            write(capture / 'analysis.json', report)
            item = {k: v for k, v in report.items() if k not in ('commands', 'queries')}
            item.update(query_count=len(report['queries']),
                        query_responses=dict(Counter(q.get('response') for q in report['queries'])),
                        query_wait_s=sum(q.get('response_wait_s', 0) for q in report['queries']))
            if report['issues']:
                record['issues'].extend(report['issues'])
            else:
                item['offline'] = offline(spec, capture, report, spec['cpu_affinity'])
                if not item['offline']['original_response_prefix_equal']:
                    record['issues'].append(f'Offline response mismatch/unavailable: {capture.name}')
            record['traces'].append(item)
        except (ValueError, OSError, KeyError) as error:
            record['issues'].append(f'{capture.name}: {error!r}')
    prover_logs = list(folder.glob('prover*.smt2'))
    record['saturation_comments'] = dict(Counter(
        match.group(1).strip() for log in prover_logs
        for match in re.finditer(r'^;\s*State saturation:\s*([^\r\n]+)', log.read_text(), re.M)))
    record['valid'] = record['outcome_valid'] and not record['issues'] and bool(record['traces'])
    record['finished_utc'] = datetime.now(timezone.utc).isoformat()
    record['artifact_sha256'] = {str(p.relative_to(folder)): sha(p) for p in folder.rglob('*')
                                 if p.is_file()}
    write(folder / 'trial.json', record)
    print('FINISH', row['index'], 'valid', record['valid'], 'wall_s', round(record['wall_s'], 3),
          'queries', sum(t['query_count'] for t in record['traces']),
          'instantiations', sum(int(t.get('offline', {}).get('statistics', {}).get('quant-instantiations', 0))
                                for t in record['traces']),
          'saturation', record['saturation_comments'], 'issues', record['issues'], flush=True)
    return record


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--spec', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--prepare-only', action='store_true')
    args = parser.parse_args()
    spec = json.loads(args.spec.read_text())
    for path, expected in spec['artifact_sha256'].items():
        if sha(path) != expected:
            raise SystemExit(f'Frozen artifact changed: {path}')
    rows = schedule(spec)
    if args.prepare_only:
        print(json.dumps({'trials': len(rows), 'schedule': rows}, indent=2))
        return
    args.output.mkdir()
    write(args.output / 'spec.json', spec)
    write(args.output / 'schedule.json', rows)
    records = []
    for row in rows:
        record = trial(spec, row, args.output)
        records.append(record)
        with (args.output / 'trials.jsonl').open('a') as out:
            out.write(json.dumps(record) + '\n')
        if row['control'] and not record['valid']:
            write(args.output / 'stopped.json', {'reason': 'Readiness control did not pass', 'index': row['index']})
            raise SystemExit('Readiness control did not pass; evidence retained')
    postflight = [path for path, expected in spec['artifact_sha256'].items() if sha(path) != expected]
    write(args.output / 'summary.json', {'recorded': len(records),
          'valid': sum(r['valid'] for r in records), 'postflight_errors': postflight,
          'finished_utc': datetime.now(timezone.utc).isoformat()})
    if postflight:
        raise SystemExit('Frozen artifacts changed; inspect postflight')


if __name__ == '__main__':
    main()
