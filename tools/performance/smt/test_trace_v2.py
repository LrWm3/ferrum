#!/usr/bin/env python3
"""Check recorder completeness when the verifier immediately kills its solver."""
import ctypes
import importlib.util
import json
import os
from pathlib import Path
import shutil
import signal
import subprocess
import tempfile
import unittest

HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location('analyze_trace', HERE / 'analyze_trace.py')
analysis = importlib.util.module_from_spec(spec)
spec.loader.exec_module(analysis)


class PersistBeforeForwardChecks(unittest.TestCase):
    def setUp(self):
        self.real = os.environ.get('Z3_EXE') or shutil.which('z3')
        if not self.real:
            self.skipTest('Set Z3_EXE for real Z3 controls')

    def test_direct_bytes_and_v2_protocol(self):
        program = (b'(set-option :print-success true)\n(declare-const x Int)\n'
                   b'(assert (> x 1))\n(check-sat)\n(assert false)\n(check-sat)\n(exit)\n')
        with tempfile.TemporaryDirectory() as tmp:
            env = {**os.environ, 'FERRUM_SMT_REAL_Z3': self.real,
                   'FERRUM_SMT_TRACE_ROOT': tmp}
            for args, data in [(['-version'], None), (['-smt2', '-in'], program)]:
                direct = subprocess.run([self.real, *args], input=data, capture_output=True, timeout=10)
                wrapped = subprocess.run([str(HERE / 'trace_z3_v2.py'), *args], input=data,
                                         capture_output=True, timeout=10, env=env)
                self.assertEqual((direct.returncode, direct.stdout, direct.stderr),
                                 (wrapped.returncode, wrapped.stdout, wrapped.stderr))
            folder = next(p for p in Path(tmp).iterdir()
                          if '-in' in json.loads((p / 'metadata.json').read_text())['argv'])
            result = analysis.analyze(folder)
            self.assertEqual(result['issues'], [])
            self.assertEqual([q['response'] for q in result['queries']], ['sat', 'unsat'])

    @unittest.skipUnless(Path('/proc/self/task').exists(), 'Linux ownership control')
    def test_immediate_kill_after_final_acknowledgment(self):
        self.assertEqual(ctypes.CDLL(None, use_errno=True).prctl(36, 1, 0, 0, 0), 0)
        program = b'(set-option :print-success true)\n(push)\n(assert true)\n(pop)\n'
        for attempt in range(20):
            with self.subTest(attempt=attempt), tempfile.TemporaryDirectory() as tmp:
                env = {**os.environ, 'FERRUM_SMT_REAL_Z3': self.real,
                       'FERRUM_SMT_TRACE_ROOT': tmp}
                proc = subprocess.Popen([str(HERE / 'trace_z3_v2.py'), '-smt2', '-in'],
                                        stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                                        stderr=subprocess.PIPE, env=env, start_new_session=True)
                try:
                    proc.stdin.write(program)
                    proc.stdin.flush()
                    for _ in range(4):
                        self.assertEqual(proc.stdout.readline(), b'success\n')
                    folder = next(Path(tmp).iterdir())
                    child = json.loads((folder / 'metadata.json').read_text())['solver_pid']
                    os.killpg(proc.pid, signal.SIGKILL)
                    proc.wait(timeout=5)
                    os.waitpid(child, 0)
                    self.assertEqual((folder / 'stdin.bin').read_bytes(), program)
                    self.assertEqual(analysis.analyze(folder)['issues'], [])
                finally:
                    if proc.poll() is None:
                        os.killpg(proc.pid, signal.SIGKILL)
                        proc.wait(timeout=5)
                    for stream in (proc.stdin, proc.stdout, proc.stderr):
                        stream.close()


if __name__ == '__main__':
    unittest.main()
