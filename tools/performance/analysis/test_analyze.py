#!/usr/bin/env python3
"""Synthetic records only; no verifier, solver or performance trials."""
import hashlib,importlib.util,json,pathlib,tempfile,unittest
P=pathlib.Path(__file__).resolve().parent;spec=importlib.util.spec_from_file_location('analysis',P/'analyze.py');a=importlib.util.module_from_spec(spec);spec.loader.exec_module(a)
class SyntheticAudit(unittest.TestCase):
 def test_missing_and_invalid_pair_are_excluded(self):
  with tempfile.TemporaryDirectory() as tmp:
   p=pathlib.Path(tmp);cases=[{'name':f'case{i}','path':f'/fixture/{i}.vpr','sha256':str(i),'expect':{'outcome':'verified','errors':[]}} for i in range(4)];blocks=[]
   for c in cases:
    for w in [1,2,4]:
     for branch in [False,True]:
      for mode in ['fresh','reused']:
       for pair in range(5):blocks.append({'case':c['name'],'workers':w,'parallel_branches':branch,'mode':mode,'pair':pair,'block':len(blocks),'case_count':1 if mode=='fresh' else 3,'order':['source','native']})
   settings={'source':['fake-source'],'native':['fake-native'],'environment':{'FERRUM_BENCH_INTERNAL_CACHES':'on'}};schedule={'seed':42,'blocks':blocks};(p/'schedule.json').write_text(json.dumps(schedule));m={'fixtures':cases,'pairs':5,'seed':42,'internal_caches':'on','settings':settings,'artifacts':{},'schedule_sha256':a.sha(p/'schedule.json'),'verifier_timeout_seconds':120,'reuse_cases':3};(p/'manifest.json').write_text(json.dumps(m));rows=[]
   for block in blocks:
    c=next(x for x in cases if x['name']==block['case'])
    for off,backend in enumerate(block['order']):
     n=block['block']*2+off
     if n==0:continue
     session=p/f's{n}.json';timer=p/f't{n}.txt';session.write_text(json.dumps({'outcome':'completed','exit_code':0,'protocol_errors':[],'cleanup_pending':[],'records':[{'case':c['path'],'outcome':'verified','errors':[]} for _ in range(block['case_count'])]}));raw='wall_s=1.00\nuser_s=0.10\nsystem_s=0.10\nmax_rss_kib=100\nexit_status=0\n';timer.write_text(raw);values={'wall_s':'1.00','user_s':'0.10','system_s':'0.10','max_rss_kib':'100','exit_status':'0'};bad=n==3;options=['--timeout','120','--numberOfParallelVerifiers',str(block['workers'])]+(['--parallelizeBranches'] if block['parallel_branches'] else []);row={**block,'trial':n,'backend':backend,'internal_caches':'on','case_sha256':c['sha256'],'environment_overrides':settings['environment'],'verifier_command':[*settings[backend],*options,'--',*([c['path']]*block['case_count'])],'artifact_errors_before':[],'artifact_errors_after':[],'classification':'runner_error' if bad else 'valid','verifier_wall_s':None if bad else '1.00','runner_exit':1 if bad else 0,'session':str(session),'session_sha256':a.sha(session),'timer_path':str(timer),'timer_sha256':a.sha(timer),'timer':{'complete':True,'values':values,'raw':raw}};rows.append(row)
   (p/'trials.jsonl').write_text(''.join(json.dumps(x)+'\n' for x in rows));(p/'summary.json').write_text(json.dumps({'postflight_errors':[],'stopped_early':False,'scheduled_trials':480,'trials':len(rows),'counts':{'valid':len(rows)-1,'runner_error':1}}));r=a.analyze(p);self.assertFalse(r['integrity_ok']);group=next(x for x in r['paired_ratios'] if x['case']=='case0' and x['workers']==1 and not x['parallel_branches'] and x['mode']=='fresh');self.assertEqual(group['complete_pairs'],3);self.assertEqual(group['excluded_pairs'],2);self.assertEqual(group['source_over_native']['median'],'1');self.assertEqual(r['classification_counts']['missing_or_duplicate'],1);self.assertEqual(r['classification_counts']['runner_error'],1)
if __name__=='__main__':unittest.main()
