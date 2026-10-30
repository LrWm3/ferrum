#!/usr/bin/env python3
"""Check real transport transparency and response alignment used by the report."""
import importlib.util
import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest

HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location('analyze_trace', HERE / 'analyze_trace.py')
analysis = importlib.util.module_from_spec(spec)
spec.loader.exec_module(analysis)


class TraceChecks(unittest.TestCase):
    def test_quoted_delimiters_and_truncation(self):
        data = b'; preface\n(assert (= |x(); y| "a;()""b")) ; tail\n(check-sat)\n'
        self.assertEqual([data[a:b] for a, b in analysis.expressions(data)],
                         [b'(assert (= |x(); y| "a;()""b"))', b'(check-sat)'])
        with self.assertRaises(ValueError):
            list(analysis.expressions(b'(assert (= x "unfinished'))

    def test_real_z3_bytes_and_response_alignment(self):
        real = os.environ.get('Z3_EXE') or shutil.which('z3')
        if not real:
            self.skipTest('Set Z3_EXE to run the real transport control')
        program = (b'(set-option :print-success true)\n(declare-const x Int)\n'
                   b'(push 1)\n(assert (> x 1))\n(check-sat)\n(pop 1)\n'
                   b'(set-option :print-success false)\n(assert false)\n(check-sat)\n'
                   b'(set-option :print-success true)\n(echo "control-marker")\n(exit)\n')
        with tempfile.TemporaryDirectory() as tmp:
            env = {**os.environ, 'FERRUM_SMT_REAL_Z3': real,
                   'FERRUM_SMT_TRACE_ROOT': tmp}
            for args, data in [(['-version'], None), (['-smt2', '-in'], program)]:
                direct = subprocess.run([real, *args], input=data, capture_output=True, timeout=10)
                relayed = subprocess.run([str(HERE / 'trace_z3.py'), *args], input=data,
                                         capture_output=True, timeout=10, env=env)
                self.assertEqual((direct.returncode, direct.stdout, direct.stderr),
                                 (relayed.returncode, relayed.stdout, relayed.stderr))
                self.assertEqual(relayed.returncode, 0)
            folder = next(p for p in Path(tmp).iterdir()
                          if '-in' in json.loads((p / 'metadata.json').read_text())['argv'])
            self.assertEqual((folder / 'stdin.bin').read_bytes(), program)
            result = analysis.analyze(folder)
            self.assertEqual(result['issues'], [])
            self.assertEqual([q['response'] for q in result['queries']], ['sat', 'unsat'])
            chunks = folder / 'chunks.jsonl'
            rows = chunks.read_text().splitlines()
            chunks.write_text('\n'.join(rows[:-1]) + '\n')
            with self.assertRaises(ValueError):
                analysis.analyze(folder)


if __name__ == '__main__':
    unittest.main()
