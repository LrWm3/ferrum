#!/usr/bin/env python3
"""Relay Z3 bytes unchanged, persisting chunks before exposing acknowledgments.

Set FERRUM_SMT_REAL_Z3 and FERRUM_SMT_TRACE_ROOT. Every invocation gets its own
directory. This is diagnostic instrumentation; its timings include relay costs.
"""
import json
import os
from pathlib import Path
import signal
import subprocess
import sys
import threading
import time


def write_all(fd, data):
    view = memoryview(data)
    while view:
        written = os.write(fd, view)
        view = view[written:]


def main():
    real = Path(os.environ['FERRUM_SMT_REAL_Z3']).resolve()
    root = Path(os.environ['FERRUM_SMT_TRACE_ROOT'])
    folder = root / f'{os.getpid()}-{time.monotonic_ns()}'
    folder.mkdir(parents=True)
    lock = threading.Lock()
    errors = []
    started = time.monotonic_ns()
    child = subprocess.Popen([str(real), *sys.argv[1:]], stdin=subprocess.PIPE,
                             stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                             bufsize=0)
    metadata = {'argv': [str(real), *sys.argv[1:]], 'proxy_pid': os.getpid(),
                'solver_pid': child.pid, 'started_monotonic_ns': started,
                'started_wall_ns': time.time_ns(),
                'capture_format': 'persist-before-forward-v2',
                'forwarded_ns_boundary': 'forwarding start, recorded before write'}
    (folder / 'metadata.json').write_text(json.dumps(metadata, indent=2) + '\n')
    events = (folder / 'chunks.jsonl').open('w', buffering=1)

    def relay(name, source, destination):
        offset = 0
        try:
            with (folder / f'{name}.bin').open('wb', buffering=0) as capture:
                while True:
                    data = os.read(source, 65536)
                    received = time.monotonic_ns()
                    if not data:
                        break
                    # A verifier can kill this relay as soon as it receives
                    # the last response. Persist both directions before making
                    # bytes visible to either peer, so their acknowledgments
                    # cannot outrun the transcript and offset index.
                    capture.write(data)
                    forwarded = time.monotonic_ns()
                    with lock:
                        events.write(json.dumps({'stream': name, 'offset': offset,
                                                 'length': len(data),
                                                 'received_ns': received,
                                                 'forwarded_ns': forwarded}) + '\n')
                    write_all(destination, data)
                    offset += len(data)
        except (BrokenPipeError, OSError) as error:
            errors.append({'stream': name, 'error': repr(error)})
        finally:
            if name == 'stdin':
                try:
                    child.stdin.close()
                except OSError:
                    pass

    def terminate(signum, frame):
        metadata['received_signal'] = signum
        if child.poll() is None:
            child.send_signal(signum)

    signal.signal(signal.SIGTERM, terminate)
    signal.signal(signal.SIGINT, terminate)
    threads = [threading.Thread(target=relay, args=('stdin', 0, child.stdin.fileno()), daemon=True),
               threading.Thread(target=relay, args=('stderr', child.stderr.fileno(), 2), daemon=True)]
    for thread in threads:
        thread.start()
    relay('stdout', child.stdout.fileno(), 1)
    code = child.wait()
    # stdin may remain open in the parent after Z3 exits; it is a daemon relay.
    threads[1].join(timeout=2)
    metadata.update(exit_code=code, ended_monotonic_ns=time.monotonic_ns(),
                    ended_wall_ns=time.time_ns(), relay_errors=errors)
    (folder / 'metadata.json').write_text(json.dumps(metadata, indent=2) + '\n')
    return code if code >= 0 else 128 - code


if __name__ == '__main__':
    raise SystemExit(main())
