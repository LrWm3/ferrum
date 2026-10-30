#!/usr/bin/env python3
"""Independent offline audit of completed saturation captures, no solver runs."""
import argparse,collections,hashlib,importlib.util,json,pathlib,re,statistics,sys
P=pathlib.Path

def sha(p):
 with P(p).open('rb') as f:return hashlib.file_digest(f,'sha256').hexdigest()
def read(p):return json.loads(P(p).read_text())
def metrics(values):
 return {'n':len(values),'values':values,'median':statistics.median(values) if values else None,'min':min(values) if values else None,'max':max(values) if values else None}
def check_session(s,case):
 if s.get('outcome')!='completed' or s.get('exit_code')!=0 or s.get('cleanup_pending')!=[] or s.get('protocol_errors')!=[]:return False
 records=s.get('records',[])
 if len(records)!=1 or records[0].get('case')!=case['path'] or records[0].get('outcome')!=case['expect']['outcome']:return False
 return collections.Counter((e.get('id'),e.get('position')) for e in records[0].get('errors',[]))==collections.Counter((e['id'],e['position']) for e in case['expect']['errors'])
def option_audit(report):
 state={};budgets=collections.Counter();bad=[];sequence=[]
 required={'print-success':'true','global-decls':'true','auto_config':'false','smt.case_split':'3','smt.delay_units':'true','type_check':'true','smt.mbqi':'false','pp.bv_literals':'false','smt.qi.eager_threshold':'1000','smt.arith.solver':'6','model.v2':'true','model.partial':'false','smt.qi.max_multi_patterns':'1000'}
 for c in report['commands']:
  if c['name']=='set-option':
   m=re.fullmatch(r'\(\s*set-option\s+:([^\s]+)\s+([^\s()]+)\s*\)',c['preview'])
   if not m:bad.append('unparsed option: '+c['preview']);continue
   k,v=m.groups();state[k]=v
   if c.get('response')!='success':bad.append('unacknowledged: '+c['preview'])
   sequence.append([k,v])
  elif c['name']=='check-sat':
   budgets[(state.get('timeout','unset'),state.get('rlimit','unset'))]+=1
   if any(state.get(k)!=v for k,v in required.items()):bad.append('global options not effective before check '+str(c['index']))
 if any(state.get(k)!=v for k,v in required.items()):bad.append('global options mismatch')
 if any(t!='unset' or r=='unset' for (t,r) in budgets):bad.append('missing resource budget or wall timeout emitted')
 return {'final_options':state,'option_sequence':sequence,'budgets':[{'timeout':k[0],'rlimit':k[1],'checks':v} for k,v in sorted(budgets.items())],'issues':bad}
def ratio_pairs(table,numerator,denominator,metric):
 result=[];excluded=[]
 for rep in (0,1,2):
  a=table.get((numerator,rep));b=table.get((denominator,rep))
  if a is None or b is None or not a['eligible'] or not b['eligible'] or a['metrics'].get(metric) is None or not b['metrics'].get(metric):excluded.append(rep);continue
  result.append(a['metrics'][metric]/b['metrics'][metric])
 return {**metrics(result),'excluded_repetitions':excluded}
def run(results,specfile,preview,tool,out):
 root=P(results);spec=read(specfile);schedule=read(preview)['schedule'];issues=[]
 module=importlib.util.spec_from_file_location('trace_audit',tool);tr=importlib.util.module_from_spec(module);module.loader.exec_module(tr)
 if spec['seed']!=20261030 or spec['repetitions']!=3 or spec['cpu_affinity'] not in ('0-3','0,1,2,3') or spec['outer_timeout']!=300:issues.append('protocol settings mismatch')
 expected_weights={'modern':'[1,0.5,0.4,0,0]','repeat_only':'[1,0.5,0.4,0,0.02]','legacy':'[1,0.5,0.4,0.2,0.02]','common_off':'[1,0,0.4,0,0]','common_on':'[1,0,0.4,0,0.02]'}
 if {k:v['weights'] for k,v in spec['profiles'].items()}!=expected_weights:issues.append('profile weights mismatch')
 if spec['offline_timeout']!=180:issues.append('offline replay budget mismatch')
 if spec.get('capture_format')!='persist-before-forward-v2' or not spec.get('prior_readiness_attempt'):issues.append('v2 capture format or prior attempt missing')
 if len(schedule)!=58 or [x['index'] for x in schedule]!=list(range(58)) or sum(x['control'] for x in schedule)!=10 or any(not x['control'] for x in schedule[:10]) or any(x['control'] for x in schedule[10:]):issues.append('schedule control coverage/order mismatch')
 expected={(c['name'],p,b,r) for c in spec['cases'] for p in c['profiles'] for b in ('ferrum','silicon') for r in range(1 if c['control'] else 3)}
 if len(expected)!=58 or {(r['case'],r['profile'],r['backend'],r['repetition']) for r in schedule}!=expected:issues.append('schedule unique coverage mismatch')
 try:
  if read(root/'spec.json')!=spec or read(root/'schedule.json')!=schedule:issues.append('result spec or schedule differs from frozen preview')
  summary=read(root/'summary.json')
  if summary.get('recorded')!=58 or summary.get('postflight_errors'):issues.append('run incomplete or postflight failure')
 except (OSError,ValueError):issues.append('missing or invalid run summary')
 for f,h in spec['artifact_sha256'].items():
  try:
   if sha(f)!=h:issues.append('artifact mismatch: '+f)
  except OSError:issues.append('missing artifact: '+f)
 try:rows=[json.loads(x) for x in (root/'trials.jsonl').read_text().splitlines() if x]
 except (OSError,ValueError):rows=[];issues.append('trial records unavailable')
 if len(rows)!=58 or [r.get('index') for r in rows]!=list(range(58)):issues.append('trial count/order mismatch')
 cases={c['name']:c for c in spec['cases']};audits=[];tables=collections.defaultdict(dict)
 for i,plan in enumerate(schedule):
  if i>=len(rows):audits.append({'index':i,'eligible':False,'issues':['missing trial']});continue
  row=rows[i];faults=[]
  if any(row.get(k)!=v for k,v in plan.items()):faults.append('schedule row mismatch')
  folder=P(row['folder']);expected_folder=root/f"{i:03d}-{plan['case']}-{plan['profile']}-{plan['backend']}"
  if folder!=expected_folder:faults.append('unexpected trial folder')
  trace_audits=[];totals=collections.Counter();responses=collections.Counter();work=collections.Counter();missing_work=set();cpu=0.0;wait=0.0
  try:
   if read(folder/'trial.json')!=row:faults.append('trial JSON differs from JSONL')
   session=read(folder/'session.json')
   if not check_session(session,cases[plan['case']]) or row['records']!=session['records'] or not row.get('outcome_valid') or row.get('supervisor_exit')!=0:faults.append('outcome/protocol/cleanup mismatch')
   if row.get('issues') or not row.get('valid'):faults.append('runner recorded invalid trial')
   if row.get('wall_s')!=session.get('wall_seconds'):faults.append('wall time does not match session')
   observed={str(p.relative_to(folder)):sha(p) for p in folder.rglob('*') if p.is_file() and p.name!='trial.json'}
   if observed!=row['artifact_sha256']:faults.append('artifact inventory/hash mismatch')
   expected_traces=sorted(p for p in (folder/'traces').iterdir() if p.is_dir() and '-in' in read(p/'metadata.json')['argv'])
   if not expected_traces or len(expected_traces)!=len(row['traces']):faults.append('solver trace coverage mismatch')
   for trace in expected_traces:
    data=tr.analyze(trace);oa=option_audit(data);stored=read(trace/'analysis.json');
    if data['metadata'].get('capture_format')!='persist-before-forward-v2' or data['metadata'].get('forwarded_ns_boundary')!='forwarding start, recorded before write':faults.append('wrong v2 capture metadata: '+trace.name)
    entry=next((x for x in row['traces'] if x.get('folder')==str(trace)),None);raw=(trace/'stdout.bin').read_bytes();replay=(trace/'offline/stdout.bin').read_bytes();original=[raw[a:b] for a,b in tr.expressions(raw)];output=[replay[a:b] for a,b in tr.expressions(replay)];off=read(trace/'offline/result.json');equal=len(output)==len(original)+1 and output[:-1]==original
    stats=dict(re.findall(r':([^\s()]+)\s+([^\s()]+)',output[-1].decode())) if equal else {}
    if entry is None or entry.get('query_count')!=len(data['queries']) or entry.get('offline')!=off or data!=stored or data['issues'] or oa['issues'] or not equal or not off.get('original_response_prefix_equal') or off.get('exit_code')!=0 or off.get('timed_out') or stats!=off.get('statistics'):faults.append('trace/protocol/options/offline mismatch: '+trace.name)
    if off['input_sha256']!=sha(trace/'offline/input.smt2') or off['stdout_sha256']!=sha(trace/'offline/stdout.bin') or (trace/'offline/input.smt2').read_bytes()!=(trace/'stdin.bin').read_bytes()+b'\n(get-info :all-statistics)\n':faults.append('offline input/output hash mismatch: '+trace.name)
    if off.get('command')!=['taskset','--cpu-list',spec['cpu_affinity'],spec['z3'],'-smt2','-in']:faults.append('offline command/affinity mismatch')
    counts=collections.Counter(q.get('response') for q in data['queries']);responses.update(counts);totals['queries']+=len(data['queries']);wait+=sum(q.get('response_wait_s',0) for q in data['queries']);cpu+=off['user_cpu_s']+off['system_cpu_s']
    for k in ('quant-instantiations','decisions','added-eqs','rlimit-count'):
     if k in stats:work[k]+=int(stats[k])
     else:missing_work.add(k)
    canonical=hashlib.sha256('\n'.join(c['canonical_sha256'] for c in data['commands']).encode()).hexdigest()
    trace_audits.append({'path':str(trace),'input_sha256':data['input_sha256'],'canonical_command_sequence_sha256':canonical,'issues':data['issues']+oa['issues'],'global_options':oa['final_options'],'resource_budget_histogram':oa['budgets'],'query_responses':dict(counts),'query_wait_s':sum(q.get('response_wait_s',0) for q in data['queries']),'offline_cpu_s':off['user_cpu_s']+off['system_cpu_s'],'offline_statistics':stats,'original_response_prefix_equal':equal})
   weights=spec['profiles'][plan['profile']]['weights'];cmd=row['command']
   if cmd[:3]!=['taskset','--cpu-list',spec['cpu_affinity']] or '--proverSaturationTimeoutWeights' not in cmd or cmd[cmd.index('--proverSaturationTimeoutWeights')+1]!=weights or cmd[-1]!=cases[plan['case']]['path']:faults.append('capture command policy/affinity mismatch')
   comments=collections.Counter(m.group(1).strip() for p in folder.glob('prover*.smt2') for m in re.finditer(r'^;\s*State saturation:\s*([^\r\n]+)',p.read_text(),re.M))
   if dict(comments)!=row['saturation_comments']:faults.append('saturation comment mismatch')
  except (OSError,KeyError,TypeError,ValueError,IndexError) as e:faults.append('audit exception: '+repr(e))
  values={'capture_wall_s':row.get('wall_s'),'check_wait_s':wait,'offline_solver_cpu_s':cpu,'queries':totals['queries'],**{k:None if k in missing_work else work[k] for k in ('quant-instantiations','decisions','added-eqs','rlimit-count')}}
  item={'index':i,**plan,'eligible':not faults,'issues':faults,'metrics':values,'query_responses':dict(responses),'saturation_comments':row.get('saturation_comments'),'repetition_related_sum':sum((row.get('saturation_comments') or {}).get(k,0) for k in ('before repetition','before iteration')),'missing_counter_fields':sorted(missing_work), 'traces':trace_audits};audits.append(item)
  if not plan['control']:tables[(plan['case'],plan['backend'])][(plan['profile'],plan['repetition'])]=item
 aggregates=[]
 for (case,backend),table in sorted(tables.items()):
  profiles=cases[case]['profiles'];groups={}
  for profile in profiles:
   good=[table[(profile,r)] for r in range(3) if (profile,r) in table and table[(profile,r)]['eligible']];groups[profile]={'stream_signatures_by_repetition':[{'repetition':x['repetition'],'streams':[{'input_sha256':t['input_sha256'],'canonical_command_sequence_sha256':t['canonical_command_sequence_sha256']} for t in x['traces']]} for x in good],'eligible_repetitions':[x['repetition'] for x in good],'excluded_repetitions':[r for r in range(3) if not any(x['repetition']==r for x in good)],'metrics':{k:metrics([x['metrics'][k] for x in good if x['metrics'][k] is not None]) for k in ('capture_wall_s','check_wait_s','offline_solver_cpu_s','queries','quant-instantiations','decisions','added-eqs','rlimit-count')}}
  comparisons={}
  for a,b in [('repeat_only','modern'),('legacy','modern'),('common_on','common_off')]:
   if a in profiles and b in profiles:comparisons[a+'_vs_'+b]={k:ratio_pairs(table,a,b,k) for k in ('capture_wall_s','offline_solver_cpu_s','quant-instantiations','decisions','added-eqs','rlimit-count')}
  aggregates.append({'case':case,'backend':backend,'profiles':groups,'matched_ratios':comparisons})
 if issues:aggregates=[]
 out=P(out);out.mkdir(parents=True,exist_ok=False);data={'status':'invalid_global_integrity' if issues else 'audited','global_issues':issues,'capture_format':spec.get('capture_format'),'prior_readiness_attempt':spec.get('prior_readiness_attempt'),'expected':58,'observed':len(rows),'valid':sum(x['eligible'] for x in audits),'invalid':sum(not x['eligible'] for x in audits),'trials':audits,'aggregates':aggregates,'input_hashes':{str(p):sha(p) for p in [specfile,preview,tool,root/'trials.jsonl',root/'schedule.json',root/'summary.json'] if P(p).exists()},'limitations':['Fixed-path replay statistics do not rerun verifier decisions.','Source solver CPU and counters are sums of its streams within a trial; relay waits are not exclusive solver CPU.','Equal weight vectors do not imply identical saturation call sites; common controls disable both moved slots.','Three repetitions are descriptive; missing, invalid or censored trials are excluded from matched ratios. Absent Z3 statistics are unavailable, not zero.','Raw saturation labels are retained; before repetition plus before iteration is an additional combined count, not an exact call-origin equivalence.','Process accounting and process-tree observation cannot prove no unobserved descendants.','Fixed-stream replay reproducibility does not imply stable fresh-capture counters; differing fresh-stream signatures may reflect naming, ordering or context and confound profile effects.']};(out/'report.json').write_text(json.dumps(data,indent=2)+'\n');(out/'README.md').write_text('# Saturation experiment audit\n\n'+f"Status: {data['status']}; eligible {data['valid']}/58; global issues {len(issues)}. Full group summaries, matched ratios, exclusions, raw budget histograms and trace audit are in report.json.\n")
 return 0 if not issues and all(x['eligible'] for x in audits) else 1
if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('--results',required=True);p.add_argument('--spec',required=True);p.add_argument('--preview',required=True);p.add_argument('--trace-tool',required=True);p.add_argument('--output',required=True);a=p.parse_args();sys.exit(run(a.results,a.spec,a.preview,a.trace_tool,a.output))
