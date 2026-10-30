#!/usr/bin/env python3
"""Audit a completed stage-5 paired run and report only independently validated trials."""
import argparse,collections,decimal,hashlib,json,pathlib,re,statistics,sys
P=pathlib.Path;D=decimal.Decimal

def sha(path):return hashlib.sha256(P(path).read_bytes()).hexdigest()
def read(path):return json.loads(P(path).read_text())
def timer_data(path):
 raw=P(path).read_text(errors='replace');out={};names={'wall_s','user_s','system_s','max_rss_kib','exit_status'}
 for line in raw.splitlines():
  k,sep,v=line.partition('=')
  if not sep or k not in names or k in out:raise ValueError('unexpected/duplicate timer line '+line)
  out[k]=v
 if set(out)!=names:raise ValueError('missing timer fields')
 for k in ('wall_s','user_s','system_s'):
  if not re.fullmatch(r'[0-9]+(?:\.[0-9]+)?',out[k]):raise ValueError('bad '+k)
 for k in ('max_rss_kib','exit_status'):
  if not re.fullmatch(r'[0-9]+',out[k]):raise ValueError('bad '+k)
 if out['exit_status']!='0':raise ValueError('nonzero verifier exit')
 return out

def exact_result(session,case,count):
 if session.get('outcome')!='completed' or session.get('exit_code')!=0 or session.get('protocol_errors')!=[] or session.get('cleanup_pending')!=[]:return False
 rows=session.get('records')
 if not isinstance(rows,list) or len(rows)!=count:return False
 want=case['expect'];errors=collections.Counter((x['id'],x['position']) for x in want['errors'])
 return all(r.get('case')==case['path'] and r.get('outcome')==want['outcome'] and collections.Counter((e.get('id'),e.get('position')) for e in r.get('errors',[]))==errors for r in rows)

def metrics(values):
 if not values:return {'n':0,'median':None,'min':None,'max':None}
 return {'n':len(values),'median':str(statistics.median(values)),'min':str(min(values)),'max':str(max(values))}

def analyze(root):
 root=P(root);m=read(root/'manifest.json');schedule=read(root/'schedule.json');summary=read(root/'summary.json');issues=[]
 cases={x['name']:x for x in m['fixtures']};blocks=schedule.get('blocks',[]); expected_blocks={(name,w,b,mode,pair) for name in cases for w in (1,2,4) for b in (False,True) for mode in ('fresh','reused') for pair in range(m['pairs'])}
 actual_blocks=[(x.get('case'),x.get('workers'),x.get('parallel_branches'),x.get('mode'),x.get('pair')) for x in blocks]
 if len(cases)!=4 or len(m['fixtures'])!=4 or m['pairs']!=5 or len(blocks)!=240 or set(actual_blocks)!=expected_blocks or len(set(actual_blocks))!=len(actual_blocks):issues.append('schedule is not the expected 240 distinct blocks')
 if m.get('internal_caches')!='on' or schedule.get('seed')!=m.get('seed') or m.get('reuse_cases')!=3:issues.append('cache policy, seed or reuse count mismatch')
 if sha(root/'schedule.json')!=m.get('schedule_sha256'):issues.append('schedule hash mismatch')
 if summary.get('postflight_errors')!=[] or summary.get('stopped_early') is not False or summary.get('scheduled_trials')!=480:issues.append('postflight or scheduling summary failure')
 for path,h in m.get('artifacts',{}).items():
  try:
   if sha(path)!=h:issues.append('artifact hash mismatch: '+path)
  except OSError:issues.append('missing artifact: '+path)
 raw=[]
 for no,line in enumerate((root/'trials.jsonl').read_text().splitlines(),1):
  try:raw.append(json.loads(line))
  except json.JSONDecodeError:issues.append('malformed trial line '+str(no))
 expected_rows=[]
 for idx,block in enumerate(blocks):
  if block.get('block')!=idx or sorted(block.get('order',[]))!=['native','source'] or block.get('case_count')!=(1 if block.get('mode')=='fresh' else 3):issues.append('invalid block index/order/count '+str(idx));continue
  expected_rows.extend((block,backend) for backend in block['order'])
 if len(raw)!=480 or summary.get('trials')!=len(raw):issues.append('trial count or summary count mismatch')
 if dict(collections.Counter(x.get('classification') for x in raw))!=summary.get('counts'):issues.append('classification summary mismatch')
 for field in ('session','timer_path'):
  paths=[x.get(field) for x in raw]
  if None in paths or len(set(paths))!=len(paths):issues.append('missing or duplicate '+field+' paths')
 bytrial=collections.Counter(x.get('trial') for x in raw)
 if any(n!=1 for n in bytrial.values()) or set(bytrial)!=set(range(len(expected_rows))):issues.append('missing, duplicate or unexpected trial keys')
 groups=collections.defaultdict(list);pair_rows={};invalid=[]
 for index,(block,backend) in enumerate(expected_rows):
  matches=[x for x in raw if x.get('trial')==index];case=cases.get(block.get('case'));mode=block.get('mode');group=(block.get('case'),block.get('workers'),block.get('parallel_branches'),mode,backend)
  if len(matches)!=1 or case is None:
   groups[group].append({'classification':'missing_or_duplicate','wall':None});continue
  x=matches[0];problems=[]
  for k in ('case','workers','parallel_branches','mode','pair','block','order','case_count'):
   if x.get(k)!=block.get(k):problems.append('schedule mismatch '+k)
  if x.get('backend')!=backend or x.get('internal_caches')!='on' or x.get('case_sha256')!=case['sha256']:problems.append('backend/policy/input mismatch')
  if x.get('environment_overrides')!=m['settings'].get('environment',{}) or x.get('environment_overrides',{}).get('FERRUM_BENCH_INTERNAL_CACHES')!='on':problems.append('environment mismatch')
  options=['--timeout',str(m['verifier_timeout_seconds']),'--numberOfParallelVerifiers',str(block['workers'])]+(['--parallelizeBranches'] if block['parallel_branches'] else [])
  wanted_command=[*m['settings'][backend],*options,'--',*([case['path']]*block['case_count'])]
  if x.get('verifier_command')!=wanted_command:problems.append('verifier command mismatch')
  if x.get('artifact_errors_before')!=[] or x.get('artifact_errors_after')!=[]:problems.append('trial artifact failure')
  classification=x.get('classification','missing_classification');wall=None
  try:
   session=P(x['session']);timer=P(x['timer_path'])
   if sha(session)!=x.get('session_sha256'):problems.append('session hash mismatch')
   if timer.is_file() and sha(timer)!=x.get('timer_sha256'):problems.append('timer hash mismatch')
   if classification=='valid':
    if x.get('runner_exit')!=0 or not exact_result(read(session),case,block['case_count']):problems.append('proof or session check failed')
    values=timer_data(timer)
    if x.get('timer',{}).get('values')!=values or not x.get('timer',{}).get('complete') or x.get('timer',{}).get('raw')!=timer.read_text(errors='replace'):problems.append('timer record mismatch')
    if x.get('verifier_wall_s')!=values['wall_s']:problems.append('primary wall mismatch')
    wall=D(values['wall_s'])
   elif classification=='censored_timeout':
    if x.get('verifier_wall_s') is not None:problems.append('censored trial has primary wall')
   else:
    if x.get('verifier_wall_s') is not None:problems.append('invalid trial has primary wall')
  except (OSError,KeyError,TypeError,ValueError,json.JSONDecodeError) as e:problems.append('malformed/missing evidence: '+repr(e))
  if problems:
   invalid.append({'trial':index,'problems':problems});classification='invalid_audit';wall=None
  item={'classification':classification,'wall':wall};groups[group].append(item);pair_rows[(block['block'],backend)]=item
 if invalid:issues.append('one or more trial evidence checks failed')
 output=[]
 for key,items in sorted(groups.items()):
  name,workers,branch,mode,backend=key;walls=[x['wall'] for x in items if x['classification']=='valid' and x['wall'] is not None];counts=collections.Counter(x['classification'] for x in items)
  output.append({'case':name,'workers':workers,'parallel_branches':branch,'mode':mode,'backend':backend,'counts':dict(counts),'expected_trials':m['pairs'],'verifier_wall_seconds':metrics(walls)})
 pairs=collections.defaultdict(list);excluded=collections.Counter()
 for block in blocks:
  key=(block['case'],block['workers'],block['parallel_branches'],block['mode']);a=pair_rows.get((block['block'],'source'));b=pair_rows.get((block['block'],'native'))
  if not a or not b or a['classification']!='valid' or b['classification']!='valid' or a['wall'] is None or b['wall'] is None or a['wall']==0 or b['wall']==0:
   excluded[key]+=1;continue
  pairs[key].append({'pair':block['pair'],'block':block['block'],'source_seconds':str(a['wall']),'native_seconds':str(b['wall']),'source_over_native':str(a['wall']/b['wall'])})
 ratios=[{'case':k[0],'workers':k[1],'parallel_branches':k[2],'mode':k[3],'complete_pairs':len(pairs[k]),'excluded_pairs':excluded[k],'source_over_native':metrics([D(x['source_over_native']) for x in pairs[k]]),'pairs':pairs[k]} for k in sorted(set(pairs)|set(excluded))]
 lookup={(x['case'],x['mode'],x['backend'],x['workers'],x['parallel_branches']):x for x in output};effects=[]
 for x in output:
  base=lookup.get((x['case'],x['mode'],x['backend'],1,False));v=x['verifier_wall_seconds']['median'];b=base['verifier_wall_seconds']['median'] if base else None
  effects.append({'case':x['case'],'mode':x['mode'],'backend':x['backend'],'workers':x['workers'],'parallel_branches':x['parallel_branches'],'baseline_workers':1,'baseline_parallel_branches':False,'ratio_of_group_medians':str(D(v)/D(b)) if v is not None and b is not None and D(b)!=0 else None,'samples':x['verifier_wall_seconds']['n'],'baseline_samples':base['verifier_wall_seconds']['n'] if base else 0})
 return {'integrity_ok':not issues,'integrity_issues':issues,'invalid_trial_details':invalid,'input_hashes':{str(root/x):sha(root/x) for x in ['manifest.json','schedule.json','summary.json','trials.jsonl']},'planned_blocks':len(blocks),'recorded_trials':len(raw),'classification_counts':dict(collections.Counter(x['classification'] for v in groups.values() for x in v)),'per_configuration':output,'paired_ratios':ratios,'worker_branch_effects':effects,'limitations':['wall seconds are GNU time rounded decimals; zero-valued pairs excluded from ratios','reused timings are whole three-request sessions, not per-request estimates','worker/branch effects are ratios of group medians, not paired effects','no cross-workload unweighted aggregate','timeouts and invalid/missing evidence do not contribute timings']}

def main():
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('results',type=P);p.add_argument('--output',type=P,required=True);a=p.parse_args()
 try:report=analyze(a.results)
 except Exception as e:report={'integrity_ok':False,'integrity_issues':['analysis could not read required run evidence: '+repr(e)]}
 a.output.parent.mkdir(parents=True,exist_ok=True)
 if a.output.exists():raise FileExistsError(a.output)
 a.output.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps({'integrity_ok':report['integrity_ok'],'output':str(a.output),'sha256':sha(a.output)},indent=2));return 0 if report['integrity_ok'] else 1
if __name__=='__main__':sys.exit(main())
