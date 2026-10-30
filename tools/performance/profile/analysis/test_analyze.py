import importlib.util,pathlib,copy
p=pathlib.Path(__file__).resolve().parent;s=importlib.util.spec_from_file_location('analysis',p/'analyze.py');m=importlib.util.module_from_spec(s);s.loader.exec_module(m)
timer={'complete':True,'errors':[],'values':{'wall_s':'1.0','user_s':'0.5','system_s':'0.1','exit_status':'0'}}
base={'classification':'valid','timer':timer,'phase_errors':[]};a={**base,'variant':'plain'};b={**base,'variant':'timed'};c={**base,'variant':'timed_accounting','accounting':{'complete':True,'processes':[{'method':'adopted_wait4','cpu':{'user_s':.1,'system_s':.1}}]},'cpu':{'total_s':'0.7','identified_solver_s':'0.2','frontend_runtime_wrapper_other_residual_s':'0.5'}};comparison={'complete':True,'exact_diagnostics_match':True};assert m.classify_block([a,b,c],comparison)==(True,'valid')
x=copy.deepcopy(c);x['accounting']['complete']=False;assert not m.classify_block([a,b,x],comparison)[0]
x=copy.deepcopy(c);x['accounting']['processes'][0]['method']='incomplete_or_ambiguous';assert not m.classify_block([a,b,x],comparison)[0]
x=copy.deepcopy(b);x['classification']='censored_timeout';assert not m.classify_block([a,x,c],comparison)[0]
assert not m.classify_block([a,b],comparison)[0] and not m.classify_block([a,b,c],{'complete':True,'exact_diagnostics_match':False})[0]
assert m.summarize([1,2,3])['mean']==2
print('synthetic invalid/incomplete/ambiguous accounting, timeout, missing block and raw diagnostics exclusion passed')
import tempfile,json
with tempfile.TemporaryDirectory() as t:
 root=pathlib.Path(t);results=root/'results';results.mkdir();spec=root/'spec.json';spec.write_text(json.dumps({'cases':[],'artifact_sha256':{},'verifier_timeout':120,'outer_timeout':480,'environment':{'FERRUM_BENCH_INTERNAL_CACHES':'on'}}))
 for name,data in [('manifest.json',{'spec_sha256':'wrong','schedule_sha256':'wrong','seed':43,'planned_sessions':144,'frozen_artifacts':{}}),('schedule.json',[]),('summary.json',{}),('block-comparisons.json',[])]: (results/name).write_text(json.dumps(data))
 (results/'trials.jsonl').write_text('');out=root/'out'
 assert m.analyze(results,spec,out,'/tmp/ferrum-stage5-profiling-preparation/run.py')==1
 report=json.loads((out/'report.json').read_text());assert report['aggregate_status']=='suppressed_integrity_failure' and report['aggregates']==[] and report['integrity_issues']
print('synthetic global integrity failure suppresses aggregates')
