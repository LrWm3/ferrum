#!/usr/bin/env python3
"""Audit and analyze a completed predeclared 576-request direct-Prusti run."""
import argparse,collections,hashlib,json,math,pathlib,re,statistics,sys
P=pathlib.Path
EXPECTED={'observation_pass','mut_element_array_pass','mut_element_option_pass','mut_element_array_wrong'}
PHASES=('Rust to VIR encoding','VIR conversion','backend verification')
PHASE_RE=re.compile(r'\[benchmark-phase\] (Rust to VIR encoding|VIR conversion|backend verification) (\d+) ns')
ERR_RE=re.compile(r'^error(?:\[[^\]]+\])?: (.+)$',re.MULTILINE)
EVENT_RE=re.compile(r'^[ \t]*(Checking|Compiling)[ \t]+([A-Za-z0-9_-]+)[ \t]+v[^ \t\r\n]+(?:[ \t]|$)[^\n]*',re.MULTILINE)
def read(p):return json.loads(P(p).read_text())
def sha(p):
 with open(p,'rb') as f:return hashlib.file_digest(f,'sha256').hexdigest()
def tree_hash(root):
 h=hashlib.sha256()
 for p in sorted(P(root).rglob('*')):
  if p.is_symlink():raise ValueError(f'seed symlink: {p}')
  if p.is_file():h.update(str(p.relative_to(root)).encode()+b'\0'+bytes.fromhex(sha(p)))
 return h.hexdigest()
def stats(values):
 if not values:return {'count':0,'median':None,'min':None,'max':None,'values':[]}
 return {'count':len(values),'median':statistics.median(values),'min':min(values),'max':max(values),'values':values}
def valid_timer(row):
 t=row.get('timer') or {}; vals=t.get('values') or {}; raw=t.get('raw');expected={'wall_s','user_s','system_s','max_rss_kib','exit_status'}
 if not t.get('complete') or not isinstance(raw,str):return False
 lines=raw.splitlines();seen={}
 for line in lines:
  k,sep,v=line.partition('=')
  if not sep or k not in expected or k in seen:return False
  seen[k]=v
 if set(seen)!=expected or seen!=vals:return False
 if any(not re.fullmatch(r'[0-9]+(?:\.[0-9]+)?',seen[k]) for k in ('wall_s','user_s','system_s')):return False
 if any(not math.isfinite(float(seen[k])) or float(seen[k])<0 for k in ('wall_s','user_s','system_s')):return False
 if any(not re.fullmatch(r'[0-9]+',seen[k]) for k in ('max_rss_kib','exit_status')):return False
 return row.get('command_wall_s')==float(seen['wall_s']) and row.get('exit_code')==int(seen['exit_status'])
def apply_block_invalidations(rows):
 bad={r['block_id'] for r in rows if r.get('classification')=='invalid_service_cleanup'}
 result=[]
 for row in rows:
  if row.get('classification')=='invalid_service_cleanup':continue
  e=dict(row)
  if row.get('block_id') in bad:e['original_classification']=row['classification'];e['classification']='invalid_service_cleanup'
  result.append(e)
 return result,bad

def collapse_requests(rows):
 # One result per service block; None makes the entire block unavailable.
 if not rows or any(r is None for r in rows):return None
 result={'wall_s':statistics.mean(r['command_wall_s'] for r in rows),'client_user_s':statistics.mean(r['child_user_s'] for r in rows),'client_system_s':statistics.mean(r['child_system_s'] for r in rows)}
 for ph in PHASES:result[ph+'_ns']=statistics.mean(r['phase_ns'][ph][0] for r in rows)
 if rows[0]['mode']=='service':result['service_startup_s']=rows[0]['service_startup_to_socket_ns']/1e9
 return result

def main():
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--run',type=P,required=True);ap.add_argument('--output',type=P,required=True);a=ap.parse_args();run=a.run.resolve();out=a.output.resolve()
 if out.exists():raise FileExistsError(out)
 meta=read(run/'manifest.json');schedule_doc=read(run/'schedule.json');summary=read(run/'summary.json');cases={c['name']:c for c in meta['cases']};errors=[]
 def require(cond,msg):
  if not cond:errors.append(msg)
 require(not meta.get('pilot'),'pilot data cannot be primary')
 require(meta.get('pairs')==3 and meta.get('seed')==42 and meta.get('requests')==3,'primary pairing/seed/request settings differ')
 require(set(cases)==EXPECTED,'unexpected workload set')
 require(meta.get('verifier_timeout')==180 and meta.get('outer_timeout')==300,'primary timeouts differ')
 require(sha(run/'schedule.json')==meta.get('schedule_sha256'),'schedule hash mismatch')
 require(sha(meta['prepared']['dump_parity_evidence'])==meta.get('dump_parity_sha256'),'calibration evidence hash mismatch')
 require(sha(meta['prepared']['source_manifest'])==meta.get('source_manifest_sha256'),'source manifest hash mismatch')
 for path,h in meta['frozen_artifacts'].items():
  try:require(sha(path)==h,'artifact changed: '+path)
  except OSError as e:errors.append('artifact unavailable: '+path+' '+str(e))
 for b in ('native','jvm'):
  for suite in ('sequence','iterator'):
   seed=meta['prepared']['backends'][b]['target_seeds'][suite]
   try:require(tree_hash(seed['path'])==seed['tree_sha256'],'seed changed: '+seed['path'])
   except (OSError,ValueError) as e:errors.append('seed error: '+str(e))
 blocks=schedule_doc['blocks']; require(len(blocks)==144 and schedule_doc.get('seed')==42,'schedule block count or seed mismatch')
 require([b.get('block') for b in blocks]==list(range(len(blocks))),'block indices are not sequential')
 require(all(isinstance(b.get('order'),list) and sorted(b['order'])==['jvm','native'] for b in blocks),'backend order must contain each backend exactly once')
 expected_blocks={(name,w,b,mode,pair) for name in EXPECTED for w in (1,2,4) for b in (False,True) for mode in ('fresh','service') for pair in range(3)}
 actual=[(b['case'],b['workers'],b['parallel_branches'],b['mode'],b['pair']) for b in blocks]
 require(len(set(actual))==144 and set(actual)==expected_blocks,'schedule combinations duplicate, missing or unexpected')
 rows=[json.loads(line) for line in (run/'trials.jsonl').read_text().splitlines()];effective=[json.loads(line) for line in (run/'effective-trials.jsonl').read_text().splitlines()]
 actual_effective,invalid_blocks=apply_block_invalidations(rows);requests=[r for r in rows if r.get('request') is not None];require(len(requests)==576,'expected 576 request records')
 require(not summary.get('final_artifact_errors'),'runner postflight artifacts failed');require(set(summary.get('invalid_service_blocks',[]))==invalid_blocks,'cleanup invalidation mismatch')
 require(actual_effective==effective,'effective rows do not implement complete block invalidation')
 case_counts=collections.Counter();individual=[];usable={};service_audits=[]
 for block in blocks:
  for ordinal,backend in enumerate(block['order']):
   bid=2*block['block']+ordinal;matches=[r for r in requests if r.get('block_id')==bid];n=1 if block['mode']=='fresh' else 3
   require(len(matches)==n and {r.get('request') for r in matches}==set(range(n)),f'block {bid}: request coverage')
   if block['mode']=='service':
    d=run/'logs'/f'{bid:06d}-{backend}';apath=d/'service-cleanup.json';spath=d/'server-summary.json'
    try:
     audit=read(apath);ss=read(spath);log=P(ss['server_log']);okay=audit.get('stopped') is True and audit.get('cleanup_pending')==[] and not audit.get('error') and ss.get('socket_ready') is True and sha(log)==ss.get('server_log_sha256') and ss.get('endpoint')==block['endpoints'][backend]
     require(okay,f'block {bid}: service audit');service_audits.append({'block_id':bid,'audit_sha256':sha(apath),'server_summary_sha256':sha(spath),'server_log_sha256':sha(log),'valid':okay})
    except (OSError,KeyError,ValueError) as e:errors.append(f'block {bid}: missing service evidence {e}')
   for row in matches:
    k=block['case'];case=cases[k];case_counts[(k,backend,block['mode'])]+=1;reasons=[]
    if any(row.get(q)!=v for q,v in [('case',k),('backend',backend),('workers',block['workers']),('parallel_branches',block['parallel_branches']),('mode',block['mode']),('pair',block['pair']),('backend_order',block['order'])]):reasons.append('schedule mismatch')
    if row.get('classification')!='valid':reasons.append('runner '+str(row.get('classification')))
    if bid in invalid_blocks:reasons.append('invalid service cleanup')
    if not row.get('cleanup_ok') or not row.get('timer_complete') or not valid_timer(row):reasons.append('timer or client cleanup')
    if row.get('outer_timeout'):reasons.append('censored timeout')
    if not row.get('host_before') or not row.get('host_after'):reasons.append('host load missing')
    try:
     client=P(row['client_log']);text=client.read_text(errors='replace')
     if sha(client)!=row['client_log_sha256']:reasons.append('client log hash')
     if client.with_suffix('.time').read_text(errors='replace')!=(row.get('timer') or {}).get('raw'):reasons.append('raw timer file mismatch')
     events=[(m.group(1),m.group(2)) for m in EVENT_RE.finditer(text)]
     if events!=[('Checking',case['package'])]:reasons.append('unexpected dependency rebuild')
     if row.get('dependency_check',{}).get('valid') is not True:reasons.append('runner dependency audit')
     found=[x for x in ERR_RE.findall(text) if not x.startswith(('could not compile','aborting due to'))];expect=case['expect']
     if row.get('exit_code')!=expect['exit'] or found!=expect['errors'] or (expect.get('location') and expect['location'] not in text):reasons.append('outcome or diagnostic mismatch')
     combined=text
     if block['mode']=='service':
      seg=client.parent/f"server-segment-{row['request']}.log"
      if sha(seg)!=row.get('server_segment_sha256'):reasons.append('server segment hash')
      combined+='\n'+seg.read_text(errors='replace')
      if row.get('endpoint')!=block['endpoints'][backend]:reasons.append('endpoint mismatch')
     phases=collections.defaultdict(list)
     for name,num in PHASE_RE.findall(combined):phases[name].append(int(num))
     if any(len(phases[name])!=1 or phases[name]!=row.get('phase_ns',{}).get(name) for name in PHASES):reasons.append('phase record mismatch')
     session=client.with_suffix('.session.json');sd=read(session)
     if sd.get('raw_output')!=text:reasons.append('session raw output mismatch')
     if sd.get('cleanup_pending')!=[] or sd.get('protocol_errors')!=[]:reasons.append('owned cleanup/protocol')
     if sd.get('exit_code')!=row.get('exit_code'):reasons.append('session exit mismatch')
    except (OSError,KeyError,ValueError) as e:reasons.append('missing evidence: '+str(e))
    info={'block_id':bid,'case':k,'backend':backend,'workers':block['workers'],'parallel_branches':block['parallel_branches'],'mode':block['mode'],'pair':block['pair'],'request':row.get('request'),'valid':not reasons,'reasons':reasons,'classification':row.get('classification')};individual.append(info)
    if not reasons:usable[(k,backend,block['workers'],block['parallel_branches'],block['mode'],block['pair'],row['request'])]=row
 require(len(service_audits)==144,'expected 144 complete service audits')
 require(len(effective)==576,'expected 576 effective request rows')
 require(not summary.get('invalid_service_blocks') or bool(invalid_blocks),'invalid blocks missing from raw evidence')
 # The two later requests are averaged within each independent service block.
 measures={}
 for name in EXPECTED:
  for w in (1,2,4):
   for branch in (False,True):
    for pair in range(3):
     for backend in ('native','jvm'):
      for kind,mode,indices in [('fresh','fresh',(0,)),('service_first','service',(0,)),('service_later_mean','service',(1,2))]:
       rs=[usable.get((name,backend,w,branch,mode,pair,i)) for i in indices]
       metrics=collapse_requests(rs)
       if metrics is not None:measures[(name,backend,w,branch,kind,pair)]=metrics
 groups=[]
 for name in sorted(EXPECTED):
  for w in (1,2,4):
   for branch in (False,True):
    for kind in ('fresh','service_first','service_later_mean'):
     for backend in ('native','jvm'):
      samples=[measures[(name,backend,w,branch,kind,p)] for p in range(3) if (name,backend,w,branch,kind,p) in measures]
      keys=('wall_s','client_user_s','client_system_s',*(ph+'_ns' for ph in PHASES))
      groups.append({'case':name,'backend':backend,'workers':w,'parallel_branches':branch,'mode':kind,'metrics':{k:stats([s[k] for s in samples]) for k in keys}})
 paired=[];worker_effects=[]
 for name in sorted(EXPECTED):
  for w in (1,2,4):
   for branch in (False,True):
    for kind in ('fresh','service_first','service_later_mean'):
     ratios=[];excluded=[]
     for pair in range(3):
      n=measures.get((name,'native',w,branch,kind,pair));j=measures.get((name,'jvm',w,branch,kind,pair))
      if n is None or j is None or n['wall_s']<=0:excluded.append(pair)
      else:ratios.append({'pair':pair,'jvm_over_native':j['wall_s']/n['wall_s']})
     paired.append({'case':name,'workers':w,'parallel_branches':branch,'mode':kind,'pairs':ratios,'excluded_pair_indices':excluded,'ratio':stats([x['jvm_over_native'] for x in ratios])})
     if w!=1:
      for backend in ('native','jvm'):
       effects=[];excluded=[]
       for pair in range(3):
        ref=measures.get((name,backend,1,branch,kind,pair));cur=measures.get((name,backend,w,branch,kind,pair))
        if ref is None or cur is None or ref['wall_s']<=0:excluded.append(pair)
        else:effects.append({'pair':pair,'worker_over_one':cur['wall_s']/ref['wall_s']})
       worker_effects.append({'case':name,'backend':backend,'workers':w,'parallel_branches':branch,'mode':kind,'pairs':effects,'excluded_pair_indices':excluded,'ratio':stats([x['worker_over_one'] for x in effects])})
 branch_effects=[]
 for name in sorted(EXPECTED):
  for backend in ('native','jvm'):
   for w in (1,2,4):
    for kind in ('fresh','service_first','service_later_mean'):
     ratios=[];excluded=[]
     for pair in range(3):
      off=measures.get((name,backend,w,False,kind,pair));on=measures.get((name,backend,w,True,kind,pair))
      if off is None or on is None or off['wall_s']<=0:excluded.append(pair)
      else:ratios.append({'pair':pair,'branch_on_over_off':on['wall_s']/off['wall_s']})
     branch_effects.append({'case':name,'backend':backend,'workers':w,'mode':kind,'pairs':ratios,'excluded_pair_indices':excluded,'ratio':stats([x['branch_on_over_off'] for x in ratios])})
 # Startup appears once per service backend block, not once per request.
 startups=[]
 for bid in sorted({r['block_id'] for r in requests if r.get('mode')=='service'}):
  rr=[r for r in requests if r.get('block_id')==bid];valid=all(usable.get((r['case'],r['backend'],r['workers'],r['parallel_branches'],r['mode'],r['pair'],r['request'])) is not None for r in rr)
  if len(rr)==3 and valid and len({r.get('service_startup_to_socket_ns') for r in rr})==1:startups.append({'block_id':bid,'case':rr[0]['case'],'backend':rr[0]['backend'],'workers':rr[0]['workers'],'parallel_branches':rr[0]['parallel_branches'],'pair':rr[0]['pair'],'startup_ns':rr[0]['service_startup_to_socket_ns']})
 startup_groups=[]
 for name in sorted(EXPECTED):
  for backend in ('native','jvm'):
   for w in (1,2,4):
    for branch in (False,True):
     selected=[x['startup_ns'] for x in startups if (x['case'],x['backend'],x['workers'],x['parallel_branches'])==(name,backend,w,branch)]
     startup_groups.append({'case':name,'backend':backend,'workers':w,'parallel_branches':branch,'startup_ns':stats(selected)})
 result={'kind':'direct-prusti-primary-analysis','run':str(run),'integrity_errors':errors,'primary_valid':not errors,'request_counts':dict(collections.Counter(r['classification'] for r in effective)),'request_audit':individual,'service_audits':service_audits,'groups':groups,'paired_jvm_over_native':paired,'worker_over_one':worker_effects,'branch_on_over_off':branch_effects,'service_startup_blocks':startups,'service_startup_groups':startup_groups,'limitations':['Service later mean averages two requests within one block; blocks are the independent replicas.','Worker and branch effects match by predeclared pair index across separate randomized blocks, not the same process.','Client CPU in service mode excludes the live server and its Z3 children.','Timers have hundredth-second resolution and zero denominators are excluded.','Phase spans differ by backend and are inclusive; no exclusive Z3/symbolic claim.','JVM service retains a process-level OnceLock Viper/JVM; native constructs a frontend per request.','Process cleanup tracks observed descendants and cannot prove all escapes.','Three pairs give limited variability evidence; timeouts and invalid observations are retained.']}
 if errors:result['groups']=[];result['paired_jvm_over_native']=[];result['worker_over_one']=[];result['branch_on_over_off']=[];result['service_startup_blocks']=[];result['service_startup_groups']=[]
 out.mkdir(parents=True,exist_ok=False);(out/'analysis.json').write_text(json.dumps(result,indent=2)+'\n');(out/'README.md').write_text('# Direct Prusti primary analysis\n\n'+('Integrity checks failed; no performance aggregates are emitted.' if errors else f"Audited {len(requests)} requests and {len(service_audits)} service blocks; see analysis.json for per-trial audit, paired ratios and exclusions.")+'\n')
 print(json.dumps({'primary_valid':not errors,'integrity_errors':errors,'requests':len(requests),'service_audits':len(service_audits),'counts':result['request_counts']},indent=2));return 0 if not errors else 1
if __name__=='__main__':sys.exit(main())
