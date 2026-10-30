#!/usr/bin/env python3
"""Fake-runner-only tests: no verifier, solver, or compilation."""
import importlib.util,json,pathlib,sys,tempfile,types,unittest
from unittest.mock import patch
P=pathlib.Path(__file__).resolve().parent
spec=importlib.util.spec_from_file_location('harness',P/'run.py');h=importlib.util.module_from_spec(spec);spec.loader.exec_module(h)
class HarnessTest(unittest.TestCase):
 def test_schedule_reproducible_complete_and_options(self):
  cases=[{'name':'a'},{'name':'b'}];x=h.make_schedule(cases,2,42,3);self.assertEqual(x,h.make_schedule(cases,2,42,3));self.assertNotEqual(x,h.make_schedule(cases,2,43,3));self.assertEqual(len(x),48)
  keys={(v['case'],v['workers'],v['parallel_branches'],v['mode'],v['pair']) for v in x};self.assertEqual(len(keys),48);self.assertTrue(all(sorted(v['order'])==['native','source'] for v in x));self.assertNotIn('--disableCaches',h.verifier_options(30,2,True))
 def test_cache_policy_requires_matching_frozen_driver_markers(self):
  with tempfile.TemporaryDirectory() as tmp:
   p=pathlib.Path(tmp);classes=p/'classes';classes.mkdir();src=classes/'SourceSession.class';src.write_bytes(b'fake source');native=p/'native';native.write_bytes(b'fake native');frozen={str(src):h.sha(src),str(native):h.sha(native)}
   def marker(path):return {'kind':'ferrum-bench-cache-policy-v1','variant':'plain','environment':'FERRUM_BENCH_INTERNAL_CACHES','artifact':str(path),'sha256':h.sha(path)}
   settings={'source':['java','-cp',str(classes)+':x.jar','SourceSession'],'native':[str(native)],'environment':{'FERRUM_BENCH_INTERNAL_CACHES':'on'},'driver_capabilities':{'source':marker(src),'native':marker(native)}}
   h.validate_cache_policy(settings,frozen,'on')
   with self.assertRaises(ValueError):h.validate_cache_policy(settings,frozen,'off')
   old=settings.pop('driver_capabilities')
   with self.assertRaises(ValueError):h.validate_cache_policy(settings,frozen,'on')
   settings['driver_capabilities']=old;settings['native'].append('--disableCaches')
   with self.assertRaises(ValueError):h.validate_cache_policy(settings,frozen,'on')
   settings['native'].pop();settings['driver_capabilities']['native']['sha256']='wrong'
   with self.assertRaises(ValueError):h.validate_cache_policy(settings,frozen,'on')
 def test_timer_rejects_incomplete_signalled_or_bad_data(self):
  with tempfile.TemporaryDirectory() as tmp:
   p=pathlib.Path(tmp)/'time';self.assertFalse(h.parse_timer(p)['complete'])
   p.write_text('wall_s=0.01\nuser_s=0.00\nsystem_s=0.00\nmax_rss_kib=10\nexit_status=0\n');self.assertTrue(h.parse_timer(p)['complete'])
   for text in ['Command terminated by signal 9\nwall_s=0.01\nuser_s=0.00\nsystem_s=0.00\nmax_rss_kib=10\nexit_status=0\n','wall_s=NaN\nuser_s=0.00\nsystem_s=0.00\nmax_rss_kib=10\nexit_status=0\n','wall_s=0.01\nuser_s=0.00\nsystem_s=0.00\nmax_rss_kib=10\nexit_status=2\n','wall_s=0.01\nwall_s=0.02\nuser_s=0.00\nsystem_s=0.00\nmax_rss_kib=10\nexit_status=0\n']:
    p.write_text(text);self.assertFalse(h.parse_timer(p)['complete'])
 def test_artifact_mutation_in_final_fake_trial_is_reported(self):
  with tempfile.TemporaryDirectory() as tmp:
   p=pathlib.Path(tmp);inputs=p/'inputs';root=p/'root';inputs.mkdir();(root/'tools/compatibility').mkdir(parents=True)
   for x in [inputs/'source-manifest.json',inputs/'settings-stdio.json',inputs/'evidence-stdio.json',root/'tools/compatibility/run_session.py']:x.write_text('{}')
   fixture=p/'fixture.vpr';fixture.write_text('ok');fixture_spec=p/'fixtures.json';fixture_spec.write_text('{}')
   case={'name':'one','path':str(fixture),'sha256':h.sha(fixture),'expect':{'outcome':'verified','errors':[]}}
   source={'runtime_revision':'test','checked_source_files':{},'compiled_source_snapshot':str(root)};settings={'source':['source-fake'],'native':['native-fake'],'environment':{'FERRUM_BENCH_INTERNAL_CACHES':'on'}};frozen={};evidence={};runner=root/'tools/compatibility/run_session.py';calls=[]
   def preflight(*args):return source,settings,evidence,frozen,[case],runner
   def fake_run(cmd,**kwargs):
    self.assertEqual(kwargs['env']['FERRUM_BENCH_INTERNAL_CACHES'],'on');calls.append(cmd);out=pathlib.Path(cmd[cmd.index('--output')+1]); sep=len(cmd)-1-cmd[::-1].index('--'); paths=cmd[sep+1:];timer=pathlib.Path(cmd[cmd.index('-o')+1]);timer.write_text('wall_s=0.01\nuser_s=0.00\nsystem_s=0.00\nmax_rss_kib=10\nexit_status=0\n');out.write_text(json.dumps({'outcome':'completed','exit_code':0,'protocol_errors':[],'cleanup_pending':[],'records':[{'case':x,'outcome':'verified','errors':[]} for x in paths]}))
    if len(calls)==48:fixture.write_text('changed')
    return types.SimpleNamespace(returncode=0,stdout=b'')
   argv=['run.py','--inputs',str(inputs),'--tools-root',str(root),'--fixtures',str(fixture_spec),'--output',str(p/'out'),'--pairs','2','--seed','7','--verifier-timeout','30','--outer-per-case','40','--internal-caches','on']
   with patch.object(h,'preflight',side_effect=preflight),patch.object(h,'host_metadata',return_value={}),patch.object(h,'load_snapshot',return_value={}),patch.object(h.subprocess,'run',side_effect=fake_run),patch.object(sys,'argv',argv):
    self.assertEqual(h.main(),1)
   summary=json.loads((p/'out/summary.json').read_text());rows=[json.loads(x) for x in (p/'out/trials.jsonl').read_text().splitlines()];self.assertEqual(len(calls),48);self.assertEqual(rows[-1]['classification'],'invalid_artifact_change');self.assertIsNone(rows[-1]['verifier_wall_s']);self.assertEqual(rows[0]['verifier_wall_s'],'0.01');self.assertEqual(rows[0]['internal_caches'],'on');self.assertEqual(json.loads((p/'out/manifest.json').read_text())['internal_caches'],'on');self.assertTrue(summary['postflight_errors']);self.assertEqual(summary['trials'],48)
if __name__=='__main__':unittest.main()
