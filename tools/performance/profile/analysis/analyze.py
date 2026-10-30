#!/usr/bin/env python3
"""Analyze completed independent instrumentation study; no verifier execution."""
import argparse,collections,decimal,hashlib,importlib.util,json,pathlib,statistics,subprocess,sys
P=pathlib.Path
D=decimal.Decimal
VARIANTS={'plain','timed','timed_accounting'}
def sha(p):
 with open(p,'rb') as f:return hashlib.file_digest(f,'sha256').hexdigest()
def read(p):return json.loads(P(p).read_text())
def row_valid(row):
 if row.get('classification')!='valid':return False
 timer=row.get('timer') or {}
 if not timer.get('complete') or timer.get('errors') or set(timer.get('values',{}))!={'wall_s','user_s','system_s','exit_status'}:return False
 try:
  if timer['values']['exit_status']!='0' or any(not D(timer['values'][k]).is_finite() or D(timer['values'][k])<0 for k in ('wall_s','user_s','system_s')):return False
 except (ValueError,decimal.InvalidOperation,KeyError):return False
 if row.get('phase_errors'):return False
 if row.get('variant')=='timed_accounting':
  ac=row.get('accounting');cpu=row.get('cpu')
  if not ac or ac.get('complete') is not True or not ac.get('processes') or any(x.get('method') not in ('wrapper_wait4','adopted_wait4') or x.get('cpu') is None for x in ac['processes']) or not cpu:return False
  try:
   if any(not D(cpu[k]).is_finite() for k in ('total_s','identified_solver_s','frontend_runtime_wrapper_other_residual_s')) or D(cpu['total_s'])<=0 or D(cpu['identified_solver_s'])<0:return False
  except (KeyError,ValueError,decimal.InvalidOperation):return False
 return True

def classify_block(rows,comparison):
 if len(rows)!=3 or {r.get('variant') for r in rows}!=VARIANTS:return False,'missing_or_duplicate_variant'
 if not all(row_valid(r) for r in rows):return False,'invalid_or_incomplete_trial'
 if not comparison or comparison.get('complete') is not True or comparison.get('exact_diagnostics_match') is not True:return False,'diagnostics_mismatch_or_unchecked'
 return True,'valid'

def phase_extract(row):
 by=collections.defaultdict(dict)
 for x in row['phase_records']:
  req=x.get('request');name=x.get('phase')
  if req is None:continue
  if req not in (0,1,2) or name in by[req] or not isinstance(x.get('elapsed_ns'),str) or not x['elapsed_ns'].isdigit():raise ValueError('invalid or duplicate phase')
  by[req][name]=int(x['elapsed_ns'])
 if not all('request_total' in by[i] for i in (0,1,2)):raise ValueError('missing request total')
 return by

def summarize(nums):
 vals=[float(v) for v in nums]
 return {'n':len(vals),'values':vals,'mean':statistics.fmean(vals) if vals else None,'median':statistics.median(vals) if vals else None}

def analyze(root,spec_path,out,runner_path):
 root=P(root);out=P(out);spec=read(spec_path);module_spec=importlib.util.spec_from_file_location('profiling_runner',runner_path);runner=importlib.util.module_from_spec(module_spec);module_spec.loader.exec_module(runner);manifest=read(root/'manifest.json');schedule=read(root/'schedule.json');summary=read(root/'summary.json');comparisons=read(root/'block-comparisons.json');rows=[json.loads(x) for x in (root/'trials.jsonl').read_text().splitlines() if x];issues=[]
 if manifest.get('spec_sha256')!=sha(spec_path) or manifest.get('schedule_sha256')!=sha(root/'schedule.json'):issues.append('spec or schedule hash mismatch')
 if manifest.get('seed')!=43 or len(schedule)!=48 or manifest.get('planned_sessions')!=144:issues.append('invalid planned schedule')
 if spec.get('verifier_timeout')!=120 or spec.get('outer_timeout')!=480 or spec.get('environment',{}).get('FERRUM_BENCH_INTERNAL_CACHES')!='on':issues.append('invalid protocol settings')
 expected={(c['name'],w,b,backend,rep) for c in spec['cases'] for w,b in ((1,False),(4,True)) for backend in ('native','source') for rep in range(3)}
 observed={(b['case'],b['workers'],b['parallel_branches'],b['backend'],b['repetition']) for b in schedule}
 if schedule!=runner.schedule(spec['cases']):issues.append('schedule does not match seed-43 generator')
 if any(manifest.get('frozen_artifacts',{}).get(path)!=h for path,h in spec['artifact_sha256'].items()):issues.append('spec artifacts not bound')
 if len(expected)!=48 or expected!=observed or len({b['block'] for b in schedule})!=48 or any(set(b.get('variant_order',[]))!=VARIANTS or len(b['variant_order'])!=3 for b in schedule):issues.append('invalid schedule coverage')
 if len(rows)!=144 or summary.get('sessions')!=144 or summary.get('expected')!=144 or summary.get('stopped') or summary.get('postflight_errors'):issues.append('incomplete or invalid execution summary')
 if len({r.get('trial') for r in rows})!=len(rows):issues.append('duplicate trial identifiers')
 for path,h in manifest.get('frozen_artifacts',{}).items():
  try:
   if sha(path)!=h:issues.append('artifact mismatch: '+path)
  except OSError:issues.append('missing artifact: '+path)
 lookup={x['block']:x for x in comparisons};groups=collections.defaultdict(list)
 for r in rows:groups[r.get('block')].append(r)
 if len(comparisons)!=48 or len(lookup)!=48 or set(lookup)!={b['block'] for b in schedule}:issues.append('invalid block comparisons coverage')
 buckets=collections.defaultdict(lambda: {'overhead_timed_plain':[],'overhead_accounting_timed':[],'cpu_total_s':[],'cpu_solver_s':[],'cpu_probe_s':[],'cpu_residual_s':[],'solver_share':[],'phases':collections.defaultdict(list),'blocks':[]});audits=[]
 for block in schedule:
  members=groups[block['block']];checks=[];eligible,reason=classify_block(members,lookup.get(block['block']))
  for row in members:
   for k in ('case','workers','parallel_branches','backend','repetition'):
    if row.get(k)!=block[k]:checks.append('block metadata mismatch')
   try:
    if sha(row['session'])!=row['session_sha256']:checks.append('session hash mismatch')
    session=read(row['session']);case=next(c for c in spec['cases'] if c['name']==block['case'])
    if session.get('outcome')!='completed' or session.get('exit_code')!=0 or session.get('cleanup_pending')!=[] or session.get('protocol_errors')!=[]:checks.append('session invalid')
    records=session.get('records',[])
    if len(records)!=3 or any(r.get('case')!=case['path'] or r.get('outcome')!=case['expect']['outcome'] or collections.Counter((e.get('id'),e.get('position')) for e in r.get('errors',[]))!=collections.Counter((e['id'],e['position']) for e in case['expect']['errors']) for r in records):checks.append('proof mismatch')
    phases,phase_errors=runner.phase_records(session.get('raw_output',''),case['path'],row['variant'])
    if phase_errors or phases!=row['phase_records']:checks.append('phase record mismatch')
    if row['variant']!='plain':phase_extract(row)
    elif row['phase_records']:checks.append('plain phases')
    timerpath=root/'timers'/f"{row['trial']:03d}.time"
    if row.get('timer_sha256') is None or sha(timerpath)!=row['timer_sha256'] or runner.parse_timer(timerpath)!=row['timer']:checks.append('timer hash or fields mismatch')
    if row['variant']=='timed_accounting':
     accountdir=root/'accounting'/f"{row['trial']:03d}"
     actual_hashes={str(f):sha(f) for f in accountdir.rglob('*') if f.is_file()}
     if actual_hashes!=row.get('accounting_hashes'):checks.append('accounting inventory mismatch')
     recalculated=json.loads(subprocess.check_output([sys.executable,spec['assessor'],str(accountdir),row['session']],text=True))
     if recalculated!=row.get('accounting') or not recalculated.get('complete') or any(x.get('kind') not in ('solver','version_probe') for x in recalculated['processes']):checks.append('accounting mismatch, incomplete or unclassified')
     else:
      foreground=sum(D(row['timer']['values'][k]) for k in ('user_s','system_s'));adopted=sum(D(str(x[k])) for x in session['adopted_wait4'] for k in ('user_s','system_s'));solver=sum(D(str(x['cpu'][k])) for x in recalculated['processes'] if x['kind']=='solver' for k in ('user_s','system_s'));probe=sum(D(str(x['cpu'][k])) for x in recalculated['processes'] if x['kind']=='version_probe' for k in ('user_s','system_s'));cpu=row['cpu'];expected_cpu={'foreground_s':foreground,'adopted_all_s':adopted,'total_s':foreground+adopted,'identified_solver_s':solver,'identified_probe_s':probe,'frontend_runtime_wrapper_other_residual_s':foreground+adopted-solver-probe}
      if any(D(cpu[k])!=v for k,v in expected_cpu.items()):checks.append('CPU arithmetic mismatch')
    for path,expected_hash in row.get('accounting_hashes',{}).items():
     if sha(path)!=expected_hash:checks.append('accounting hash mismatch')
   except (OSError,KeyError,ValueError,StopIteration,TypeError,decimal.InvalidOperation,subprocess.CalledProcessError) as exc:checks.append(repr(exc))
  if len(members)==3:
   try:
    records=[read(r['session'])['records'] for r in members]
    if not records[0]==records[1]==records[2]:checks.append('raw diagnostics mismatch')
   except (OSError,ValueError,KeyError):checks.append('raw diagnostics unavailable')
  if checks:eligible=False;reason='audit_failure'
  audits.append({'block':block['block'],'eligible':eligible,'reason':reason,'issues':checks})
  if not eligible:continue
  variants={r['variant']:r for r in members};plain=D(variants['plain']['timer']['values']['wall_s']);timed=D(variants['timed']['timer']['values']['wall_s']);wrapped=D(variants['timed_accounting']['timer']['values']['wall_s'])
  if not plain or not timed:audits[-1]['eligible']=False;audits[-1]['reason']='timer_zero_resolution';continue
  key=(block['backend'],block['case'],block['workers'],block['parallel_branches']);bucket=buckets[key];bucket['blocks'].append(block['block']);bucket['overhead_timed_plain'].append(timed/plain);bucket['overhead_accounting_timed'].append(wrapped/timed)
  cpu=variants['timed_accounting']['cpu'];total=D(cpu['total_s']);solver=D(cpu['identified_solver_s']);bucket['cpu_total_s'].append(total);bucket['cpu_solver_s'].append(solver);bucket['cpu_probe_s'].append(D(cpu['identified_probe_s']));bucket['cpu_residual_s'].append(D(cpu['frontend_runtime_wrapper_other_residual_s']));bucket['solver_share'].append(solver/total)
  phases=phase_extract(variants['timed'])
  for event in variants['timed']['phase_records']:
   if event['request'] is None:bucket['phases']['session:'+event['phase']+'_ns'].append(int(event['elapsed_ns']))
  for name in phases[0].keys() & phases[1].keys() & phases[2].keys():
   bucket['phases'][name+':first_ns'].append(phases[0][name]);bucket['phases'][name+':later_mean_ns'].append((phases[1][name]+phases[2][name])/2)
 result=[]
 for (backend,case,workers,branch),data in sorted(buckets.items()):
  result.append({'backend':backend,'case':case,'workers':workers,'parallel_branches':branch,'blocks':data['blocks'],'metrics':{k:summarize(v) for k,v in data.items() if k not in ('blocks','phases')},'phases':{k:summarize(v) for k,v in sorted(data['phases'].items())}})
 if issues:result=[]
 out.mkdir(parents=True,exist_ok=False);report={'aggregate_status':'suppressed_integrity_failure' if issues else 'eligible_blocks_only','integrity_issues':issues,'expected_sessions':144,'observed_sessions':len(rows),'expected_blocks':48,'eligible_blocks':sum(x['eligible'] for x in audits),'blocks':audits,'aggregates':result,'input_hashes':{str(p):sha(p) for p in [spec_path,root/'manifest.json',root/'schedule.json',root/'summary.json',root/'block-comparisons.json',root/'trials.jsonl']},'limitations':['Instrumentation study, separate from uninstrumented primary timing.','Ratios use rounded GNU time command wall and complete valid blocks only.','Phases are nested; do not sum or compare different source/native phase names.','Solver share is accounted process CPU, not exclusive symbolic execution; residual includes frontend/runtime/wrappers/other.','Incomplete attribution, timeout, invalid proof or missing block are excluded.']};(out/'report.json').write_text(json.dumps(report,indent=2)+'\n')
 lines=['# Instrumentation study audit','',f"Observed {len(rows)}/144 sessions; eligible blocks {report['eligible_blocks']}/48; integrity issues {len(issues)}.",'','| Backend | Case | Workers / branch | Valid blocks | Timed/plain mean | Accounting/timed mean | Solver CPU share mean |','| --- | --- | --- | ---: | ---: | ---: | ---: |']
 for x in result:
  m=x['metrics'];fmt=lambda k:f"{m[k]['mean']:.3f}" if m[k]['mean'] is not None else '—';lines.append(f"| {x['backend']} | {x['case']} | {x['workers']} / {x['parallel_branches']} | {len(x['blocks'])} | {fmt('overhead_timed_plain')} | {fmt('overhead_accounting_timed')} | {fmt('solver_share')} |")
 lines+=['','Detailed first/later request phases, backend-specific session phases, raw block ratios, solver/probe CPU, exclusions and hashes are in report.json. Session phase boundaries do not measure whole-process JVM startup. Phase spans nest and are backend-specific. Invalid and incomplete observations are excluded. Aggregate tables are suppressed on global integrity failure.'];(out/'README.md').write_text('\n'.join(lines)+'\n')
 return 0 if not issues and len(rows)==144 else 1
if __name__=='__main__':
 ap=argparse.ArgumentParser();ap.add_argument('--results',required=True);ap.add_argument('--spec',required=True);ap.add_argument('--output',required=True);ap.add_argument('--runner',default=str(P(__file__).resolve().parent.parent/'run.py'));a=ap.parse_args();sys.exit(analyze(a.results,a.spec,a.output,a.runner))
