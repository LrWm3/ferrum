#!/usr/bin/env python3
"""Check schedule completeness and rejection of misleading proof observations."""
from collections import Counter
import unittest

from run_saturation import check_outcome, schedule


class SaturationProtocolChecks(unittest.TestCase):
    def test_complete_schedule_and_readiness_order(self):
        spec = {'seed': 47, 'repetitions': 2, 'cases': [
            {'name': 'positive', 'control': False, 'profiles': ['off', 'on']},
            {'name': 'negative', 'control': True, 'profiles': ['off', 'on']}]}
        rows = schedule(spec)
        self.assertEqual(len(rows), 12)
        self.assertTrue(all(r['control'] for r in rows[:4]))
        self.assertTrue(all(not r['control'] for r in rows[4:]))
        self.assertEqual(len({(r['case'], r['backend'], r['profile'], r['repetition'])
                              for r in rows}), 12)
        self.assertEqual(Counter(r['backend'] for r in rows), {'ferrum': 6, 'silicon': 6})
        self.assertEqual(rows, schedule(spec))

    def test_failure_ids_spans_and_cleanup_remain_required(self):
        case = {'expect': {'outcome': 'failure', 'errors': [
            {'id': 'exhale.failed:assertion.false', 'position': 'case.vpr@8.1'}]}}
        good = {'outcome': 'completed', 'cleanup_pending': [], 'protocol_errors': [],
                'records': [{'outcome': 'failure', 'errors': case['expect']['errors']}]}
        self.assertTrue(check_outcome(good, case))
        self.assertFalse(check_outcome({**good, 'cleanup_pending': [123]}, case))
        self.assertFalse(check_outcome({**good, 'outcome': 'harness_timeout'}, case))
        self.assertFalse(check_outcome({**good, 'records': [{'outcome': 'verified', 'errors': []}]}, case))
        wrong = {'outcome': 'failure', 'errors': [
            {'id': 'exhale.failed:assertion.false', 'position': 'case.vpr@9.1'}]}
        self.assertFalse(check_outcome({**good, 'records': [wrong]}, case))


if __name__ == '__main__':
    unittest.main()
