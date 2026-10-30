#!/usr/bin/env python3
"""Run a single verifier session with a wall-clock bound and retain raw output."""
import argparse
import ctypes
import json
import os
import signal
import subprocess
import time
import tempfile
from pathlib import Path

p = argparse.ArgumentParser(description=__doc__)
p.add_argument('--timeout', type=float, default=120)
p.add_argument('--output', type=Path, required=True)
p.add_argument('command', nargs=argparse.REMAINDER)
a = p.parse_args()
if a.timeout <= 0 or not a.command:
    p.error('positive timeout and command are required')
command = a.command[1:] if a.command[0] == '--' else a.command
if not command:
    p.error('command is required after --')
def start_time(pid):
    try:
        return Path(f'/proc/{pid}/stat').read_text().rsplit(')', 1)[1].split()[19]
    except (FileNotFoundError, ProcessLookupError, IndexError):
        return None


def discover(owned):
    for pid, start in list(owned.items()):
        if start is None or start_time(pid) != start:
            continue
        for task in Path(f'/proc/{pid}/task').glob('*'):
            try:
                children = (task / 'children').read_text().split()
            except (FileNotFoundError, ProcessLookupError):
                continue
            for value in children:
                child = int(value)
                born = start_time(child)
                if born is not None:
                    owned.setdefault(child, born)


def stop_owned(owned):
    for pid, start in reversed(list(owned.items())):
        if start is not None and start_time(pid) == start:
            try:
                os.kill(pid, signal.SIGKILL)
            except ProcessLookupError:
                pass


linux = Path('/proc/self/task').exists()
if linux and ctypes.CDLL(None, use_errno=True).prctl(36, 1, 0, 0, 0) != 0:
    raise OSError(ctypes.get_errno(), 'cannot enable child subreaper')
start = time.monotonic()
cleanup_pending = []
with tempfile.TemporaryFile() as capture:
    child = subprocess.Popen(command, stdout=capture, stderr=subprocess.STDOUT, start_new_session=True)
    owned = {child.pid: start_time(child.pid)}
    timed_out = False
    try:
        while child.poll() is None:
            discover(owned)
            if time.monotonic() - start >= a.timeout:
                timed_out = True
                discover(owned)
                # The live session leader anchors its process-group identity.
                try:
                    os.killpg(child.pid, signal.SIGKILL)
                except ProcessLookupError:
                    pass
                break
            time.sleep(0.05)
    finally:
        # Clean observed descendants on timeout, crash, and normal completion.
        # PID start times prevent signalling reused process IDs.
        stop_owned(owned)
        child.wait()
        if linux:
            # Adopted descendants become children of this standalone runner,
            # including those that outlive a fast-exiting leader or call setsid.
            owned.pop(child.pid, None)
            owned[os.getpid()] = start_time(os.getpid())
            deadline = time.monotonic() + 2
            while time.monotonic() < deadline:
                discover(owned)
                descendants = {pid: born for pid, born in owned.items() if pid != os.getpid()}
                stop_owned(descendants)
                for pid, born in list(descendants.items()):
                    if start_time(pid) != born:
                        owned.pop(pid, None)
                        continue
                    try:
                        reaped, _ = os.waitpid(pid, os.WNOHANG)
                    except ChildProcessError:
                        continue
                    if reaped:
                        owned.pop(pid, None)
                if len(owned) == 1:
                    break
                time.sleep(0.01)
            cleanup_pending = [pid for pid in owned if pid != os.getpid()]
    capture.seek(0)
    output = capture.read()
text = output.decode('utf-8', errors='replace')
records = []
protocol_errors = []
infrastructure_error_ids = frozenset({
    "prover.interaction.failed", "external.tool.error",
    "exceptional.error", "dependencynotfound.error",
})
for line in text.splitlines():
    if line.startswith('@@COMPAT@@'):
        try:
            record = json.loads(line[len('@@COMPAT@@'):])
        except json.JSONDecodeError as error:
            protocol_errors.append(str(error))
            continue
        if not isinstance(record, dict) or not isinstance(record.get('outcome'), str):
            protocol_errors.append('record must be an object with a string outcome')
            continue
        errors = record.get('errors', [])
        if not isinstance(errors, list) or any(not isinstance(error, dict) for error in errors):
            protocol_errors.append('errors must be an array of objects')
            continue
        if any(error.get('id') in infrastructure_error_ids for error in errors):
            record['outcome'] = 'prover_error'
        elif any(error.get('id') == 'timeout.error' for error in errors):
            record['outcome'] = 'verifier_timeout'
        records.append(record)
session_fault = any(r.get('outcome') in ('exception', 'unknown_result', 'unknown_failure', 'rendering_error', 'cleanup_error', 'prover_error') for r in records)
a.output.write_text(json.dumps({'command': command, 'exit_code': child.returncode,
    'outcome': 'harness_timeout' if timed_out else ('completed' if child.returncode == 0 and not protocol_errors and not session_fault and not cleanup_pending else 'process_error'),
    'protocol_errors': protocol_errors, 'cleanup_pending': cleanup_pending,
    'wall_seconds': time.monotonic() - start, 'records': records, 'raw_output': text}, indent=2) + '\n')
