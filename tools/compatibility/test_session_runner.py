import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

RUNNER = Path(__file__).with_name('run_session.py')

class SessionRunner(unittest.TestCase):
    def run_case(self, code, timeout=3):
        with tempfile.TemporaryDirectory() as directory:
            output = Path(directory) / 'result.json'
            subprocess.run([sys.executable, str(RUNNER), '--timeout', str(timeout), '--output', str(output), '--', sys.executable, '-c', code], check=True)
            return json.loads(output.read_text())

    def test_timeout_and_incomplete_json(self):
        result = self.run_case('import time; print("@@COMPAT@@{", flush=True); time.sleep(5)', .2)
        self.assertEqual(result['outcome'], 'harness_timeout')
        self.assertTrue(result['protocol_errors'])

    def test_exception_and_malformed_result_are_not_completed(self):
        for text in ('@@COMPAT@@{', '@@COMPAT@@[]', '@@COMPAT@@{"outcome":"verified","errors":{}}', '@@COMPAT@@{"outcome":"exception"}', '@@COMPAT@@{"outcome":"unknown_failure"}'):
            result = self.run_case(f'print({text!r})')
            self.assertEqual(result['outcome'], 'process_error')

    def test_empty_command_rejected(self):
        result = subprocess.run([sys.executable, str(RUNNER), '--output', '/tmp/unused-session.json', '--'], capture_output=True)
        self.assertNotEqual(result.returncode, 0)

    @unittest.skipUnless(Path('/proc/self/task').exists(), 'Linux subreaper required')
    def test_fast_parent_exit_with_new_session_is_reaped(self):
        child = 'import os,time; os.setsid(); print(os.getpid(),flush=True); time.sleep(30)'
        parent = ('import subprocess,sys; p=subprocess.Popen([sys.executable,"-c",' + repr(child) + '], stdout=subprocess.PIPE, text=True); '
                  'print(p.stdout.readline().strip(),flush=True)')
        result = self.run_case(parent)
        self.assertEqual(result['outcome'], 'completed')
        pid = int(result['raw_output'].strip())
        self.assertFalse(Path(f'/proc/{pid}').exists(), 'adopted child was not reaped')
        self.assertEqual(result['cleanup_pending'], [])

    @unittest.skipUnless(Path('/proc/self/task').exists(), 'Linux /proc tracking required')
    def test_crash_cleans_observed_child(self):
        code = 'import subprocess,sys,time; p=subprocess.Popen([sys.executable,"-c","import time; time.sleep(30)"]); print(p.pid,flush=True); time.sleep(.3); sys.exit(3)'
        result = self.run_case(code)
        self.assertEqual(result['outcome'], 'process_error')
        pid = int(result['raw_output'].strip())
        stat = Path(f'/proc/{pid}/stat')
        self.assertFalse(stat.exists(), 'observed child was not reaped')

if __name__ == '__main__': unittest.main()
