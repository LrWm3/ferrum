import unittest
import compatibility_evidence as c

class Compare(unittest.TestCase):
    def setUp(self):
        self.old_compare = c.compare
        c.compare = lambda a, b: self.old_compare({'session_outcome':'completed', 'exit_code':0, **a}, {'session_outcome':'completed', 'exit_code':0, **b})
    def tearDown(self): c.compare = self.old_compare
    def test_nonzero_process_cannot_match(self):
        good = {'outcome':'verified', 'session_outcome':'completed', 'exit_code':0}
        bad = {'outcome':'verified', 'session_outcome':'process_error', 'exit_code':1}
        self.assertEqual(self.old_compare(good, bad), 'session_inconclusive')
    def test_failure_requires_explicit_ids_and_positions(self):
        failure = {'outcome': 'failure', 'errors': [{'position': '1.1'}]}
        self.assertEqual(c.compare(failure, failure), 'failure_evidence_incomplete')
        complete = {'outcome': 'failure', 'errors': [{'id': 'assert.failed:assertion.false', 'position': '1.1'}]}
        self.assertEqual(c.compare(complete, complete), 'same_ids_positions')
        other = {'outcome': 'failure', 'errors': [{'id': 'assert.failed:assertion.false', 'position': '1.2'}]}
        self.assertEqual(c.compare(complete, other), 'different_ids_positions')

    def test_timeout_id_is_not_failure_match(self):
        row = {'outcome':'failure', 'errors':[{'id':'timeout.error', 'position':'1.1'}]}
        self.assertEqual(c.compare(row, row), 'inconclusive')
        for other in ({'outcome':'verified', 'errors':[]},
                {'outcome':'failure', 'errors':[{'id':'assert.failed:assertion.false', 'position':'1.1'}]}):
            self.assertEqual(c.compare(row, other), 'inconclusive')
            self.assertEqual(c.compare(other, row), 'inconclusive')

    def test_success_requires_empty_error_list(self):
        success = {'outcome':'verified', 'errors':[]}
        self.assertEqual(c.compare(success, success), 'both_verified')
        self.assertEqual(c.compare({'outcome':'verified'}, success), 'invalid_success_evidence')
        self.assertEqual(c.compare({'outcome':'verified'}, {'outcome':'verifier_timeout'}),
            'invalid_success_evidence')

    def test_infrastructure_errors_never_become_proof_failures(self):
        success = {'outcome': 'verified', 'errors': []}
        for error_id in c.INFRASTRUCTURE_ERROR_IDS:
            row = {'outcome': 'failure', 'errors': [{'id': error_id, 'position': '1.1'}]}
            for other in (row, success):
                self.assertEqual(c.compare(row, other), 'inconclusive')
                self.assertEqual(c.compare(other, row), 'inconclusive')
        self.assertEqual(c.compare({'outcome':'prover_error'}, success), 'inconclusive')

    def test_timeouts_are_inconclusive(self):
        success = {'outcome': 'verified', 'errors': []}
        for outcome in ('timeout', 'verifier_timeout'):
            timeout = {'outcome': outcome}
            self.assertEqual(c.compare(timeout, timeout), 'inconclusive')
            self.assertEqual(c.compare(timeout, success), 'inconclusive')
            self.assertEqual(c.compare(success, timeout), 'inconclusive')

if __name__ == '__main__': unittest.main()
