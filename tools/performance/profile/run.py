#!/usr/bin/env python3
"""Separate randomized phase/accounting experiment; never primary timings."""
import argparse,collections,decimal,hashlib,importlib.util,json,os,pathlib,platform,random,subprocess,sys,time
P=pathlib.Path
TIMER=P('/usr/bin/time');HERE=P(__file__).resolve().parent

def sha(p):
 with open(p,'rb') as f:return hashlib.file_digest(f,'sha256').hexdigest()
def read(p):return json.loads(P(p).read_text())
def schedule(cases):
 rng=random.Random(43);blocks=[{'case':case['name'],'workers':w,'parallel_branches':branch,'backend':b,'repetition':rep} for case in cases for w,branch in ((1,False),(4,True)) for b in ('native','source') for rep in range(3)];rng.shuffle(blocks)
 for i,x in enumerate(blocks):
  x['block']=i;x['variant_order']=['plain','timed','timed_accounting'];rng.shuffle(x['variant_order'])
 return blocks

def phase_records(text,case,variant):
 phases=[];faults=[]
 for line in text.splitlines():
  if not line.startswith('@@PERF@@'):continue
  try:
   x=json.loads(line[8:]); req=x['request'];n=x['elapsed_ns'];assert x['clock']=='monotonic' and x['unit']=='ns' and isinstance(n,str) and n.isdigit() and isinstance(x['phase'],str)
   assert (req is None and x['case'] is None) or (type(req)==int and 0<=req<3 and x['case']==case)
   phases.append(x)
  except (ValueError,KeyError,TypeError,AssertionError) as e:faults.append(repr(e))
 if variant=='plain' and phases:faults.append('plain emitted phase records')
 if variant!='plain' and collections.Counter(x['request'] for x in phases if x['phase']=='request_total')!=collections.Counter({0:1,1:1,2:1}):faults.append('missing or duplicate per-request total')
 return phases,faults

def parse_timer(path):
 try:raw=P(path).read_text()
 except OSError as e:return {'complete':False,'raw':None,'values':{},'errors':[repr(e)]}
 expected={'wall_s','user_s','system_s','exit_status'};values={};errors=[]
 for line in raw.splitlines():
  k,sep,v=line.partition('=')
  if not sep or k not in expected or k in values:errors.append('unexpected or duplicate timer line: '+line);continue
  values[k]=v
 if set(values)!=expected:errors.append('missing timer fields')
 for k in ('wall_s','user_s','system_s'):
  try:
   v=values[k]
   if not v or any(c not in '0123456789.' for c in v) or not decimal.Decimal(v).is_finite() or decimal.Decimal(v)<0:raise ValueError()
  except (KeyError,ValueError,decimal.InvalidOperation):errors.append('invalid '+k)
 if values.get('exit_status')!='0':errors.append('nonzero or invalid exit status')
 return {'complete':not errors,'raw':raw,'values':values,'errors':errors}
def load_snapshot():
 try:load=os.getloadavg()
 except OSError:load=None
 try:mem=next((x for x in P('/proc/meminfo').read_text().splitlines() if x.startswith('MemAvailable:')),None)
 except OSError:mem=None
 return {'wall_time_unix_ns':time.time_ns(),'monotonic_ns':time.monotonic_ns(),'load_average':load,'memory_available':mem}
def host_metadata():
 return {'uname':platform.uname()._asdict(),'cpu_count':os.cpu_count(),'python_version':sys.version,'python_executable':str(P(sys.executable).resolve()),'environment':{k:os.environ.get(k) for k in ('PATH','LD_LIBRARY_PATH','JAVA_HOME','RUSTUP_TOOLCHAIN','RUSTFLAGS','CARGO_BUILD_JOBS')}}

def assess(session,case):
 if session.get('cleanup_pending')!=[] or session.get('protocol_errors')!=[]:return 'invalid_session'
 if session.get('outcome')=='harness_timeout':return 'censored_timeout'
 if session.get('outcome')!='completed' or session.get('exit_code')!=0:return 'invalid_session'
 records=session.get('records',[])
 if len(records)!=3 or any(x.get('case')!=case['path'] for x in records):return 'invalid_coverage'
 for r in records:
  if r.get('outcome') in ('timeout','verifier_timeout') or any(e.get('id')=='timeout.error' for e in r.get('errors',[])):return 'censored_timeout'
  if r.get('outcome')!=case['expect']['outcome'] or collections.Counter((e.get('id'),e.get('position')) for e in r.get('errors',[]))!=collections.Counter((e['id'],e['position']) for e in case['expect']['errors']):return 'unexpected_proof'
 return 'valid'

def main():
 p=argparse.ArgumentParser();p.add_argument('--spec',type=P,required=True);p.add_argument('--output',type=P,required=True);a=p.parse_args();spec=read(a.spec);out=a.output.resolve()
 if out.exists():raise FileExistsError(out)
 cases=spec['cases'];assert len(cases)==4 and len({x['name'] for x in cases})==4
 if spec['verifier_timeout']!=120 or spec['outer_timeout']!=480:raise ValueError('requires protocol budgets 120s and 3*150s+30s')
 artifacts=dict(spec['artifact_sha256']);artifacts[str(a.spec.resolve())]=sha(a.spec);artifacts[str(P(__file__).resolve())]=sha(__file__);artifacts[str(TIMER.resolve())]=sha(TIMER);artifacts[str(P(sys.executable).resolve())]=sha(sys.executable)
 for case in cases:
  if artifacts.get(str(P(case['path']).resolve()))!=case['sha256']:raise ValueError('fixture not bound')
  if case['expect']['outcome'] not in ('verified','failure') or not isinstance(case['expect']['errors'],list) or (case['expect']['outcome']=='verified' and case['expect']['errors']) or (case['expect']['outcome']=='failure' and (not case['expect']['errors'] or any(not x.get('id') or not x.get('position') or x['position']=='<no position>' for x in case['expect']['errors']))):raise ValueError('invalid oracle')
 for backend in ('native','source'):
  for variant in ('plain','timed'):
   prefix=spec['commands'][backend][variant];required=[]
   for tok in prefix:
    for v in tok.split(os.pathsep):
     f=P(v)
     if f.is_file():required.append(str(f.resolve()))
     if f.is_dir():required.extend(str(q.resolve()) for q in f.rglob('*.class') if q.is_file())
   if any(x not in artifacts for x in required):raise ValueError('command artifact not bound')
 if not P(spec['runner']).is_file() or str(P(spec['runner']).resolve()) not in artifacts or str(P(spec['wrapper']).resolve()) not in artifacts or str(P(spec['assessor']).resolve()) not in artifacts:raise ValueError('unbound accounting tools')
 def checks():
  bad=[]
  for f,h in artifacts.items():
   try:
    if sha(f)!=h:bad.append(f)
   except OSError:bad.append(f)
  return bad
 if checks():raise ValueError('preflight artifact mismatch')
 blocks=schedule(cases);assert len(blocks)==48;out.mkdir();(out/'sessions').mkdir();(out/'timers').mkdir();(out/'accounting').mkdir();(out/'schedule.json').write_text(json.dumps(blocks,indent=2)+'\n')
 meta={'spec':spec,'spec_sha256':sha(a.spec),'frozen_artifacts':artifacts,'schedule_sha256':sha(out/'schedule.json'),'planned_sessions':144,'seed':43,'host_toolchain':host_metadata(),'host_before':load_snapshot(),'limitations':['primary timings are separate uninstrumented runs','phase spans nest; do not sum','instrumentation and accounting may perturb results','GNU time CPU is rounded; residual is not exclusively frontend','accounting covers tracked processes only; missing is not zero','no elapsed-wall subtraction']};(out/'manifest.json').write_text(json.dumps(meta,indent=2)+'\n')
 byname={c['name']:c for c in cases};counts=collections.Counter();idx=0;stopped=False;trial_rows=[]
 with (out/'trials.jsonl').open('x') as log:
  for block in blocks:
   for variant in block['variant_order']:
    bad=checks()
    if bad:stopped=True;break
    case=byname[block['case']];backend=block['backend'];base='plain' if variant=='plain' else 'timed';command=list(spec['commands'][backend][base]);account_dir=out/'accounting'/f'{idx:03d}';account_dir.mkdir();command[spec['z3_arg_index'][backend]]=spec['wrapper'] if variant=='timed_accounting' else spec['z3'];command+=['--timeout','120','--numberOfParallelVerifiers',str(block['workers'])]+(['--parallelizeBranches'] if block['parallel_branches'] else [])+['--']+[case['path']]*3
    session=out/'sessions'/f'{idx:03d}.json';timer=out/'timers'/f'{idx:03d}.time';cmd=[sys.executable,spec['runner'],'--timeout','480','--output',str(session),'--',str(TIMER),'-q','-f','wall_s=%e\nuser_s=%U\nsystem_s=%S\nexit_status=%x','-o',str(timer),'--',*command];env={**os.environ,**spec['environment'],'FERRUM_BENCH_INTERNAL_CACHES':'on','FERRUM_Z3_REAL':spec['z3'],'FERRUM_Z3_RECORD_DIR':str(account_dir)}
    host_before=load_snapshot()
    try:r=subprocess.run(cmd,env=env,capture_output=True,text=True,timeout=495);d=read(session);valid=assess(d,case);phases,phase_errors=phase_records(d.get('raw_output',''),case['path'],variant)
    except (OSError,ValueError,subprocess.TimeoutExpired) as e:r=None;d={};valid='runner_error';phases=[];phase_errors=[repr(e)]
    if r is not None and r.returncode!=0:valid='runner_error'
    if valid=='valid' and phase_errors:valid='invalid_phases'
    host_after=load_snapshot();timer_data=parse_timer(timer);timer_fields=timer_data['values']
    if not timer_data['complete'] and valid=='valid':valid='invalid_timer'
    accounting=None;cpu=None
    if variant=='timed_accounting' and session.exists():
     try:
      accounting=json.loads(subprocess.check_output([sys.executable,spec['assessor'],str(account_dir),str(session)],text=True))
      if not accounting['complete']:raise ValueError('incomplete identity accounting')
      fg=sum(decimal.Decimal(timer_fields[k]) for k in ('user_s','system_s'));adopt=sum(decimal.Decimal(str(x[k])) for x in d['adopted_wait4'] for k in ('user_s','system_s'));solver=sum(decimal.Decimal(str(x['cpu'][k])) for x in accounting['processes'] for k in ('user_s','system_s'));cpu={'foreground_s':str(fg),'adopted_all_s':str(adopt),'total_s':str(fg+adopt),'identified_solver_s':str(solver),'frontend_runtime_wrapper_other_residual_s':str(fg+adopt-solver)}
     except (ValueError,KeyError,TypeError,decimal.InvalidOperation,subprocess.CalledProcessError):
      if valid=='valid':valid='invalid_accounting'
    bad=checks()
    if bad:valid='invalid_artifact_change';stopped=True
    row={'trial':idx,**block,'variant':variant,'classification':valid,'command':cmd,'env_overrides':{k:env[k] for k in ('FERRUM_BENCH_INTERNAL_CACHES','FERRUM_Z3_REAL','FERRUM_Z3_RECORD_DIR')},'runner_exit':r.returncode if r else None,'runner_stdout':r.stdout if r else None,'runner_stderr':r.stderr if r else None,'session':str(session),'session_sha256':sha(session) if session.exists() else None,'timer':timer_data,'host_before':host_before,'host_after':host_after,'timer_sha256':sha(timer) if timer.exists() else None,'phase_records':phases,'phase_errors':phase_errors,'accounting':accounting,'accounting_hashes':{str(f):sha(f) for f in account_dir.rglob('*') if f.is_file()},'cpu':cpu,'artifact_errors':bad};log.write(json.dumps(row)+'\n');log.flush();trial_rows.append(row);counts[valid]+=1;idx+=1
    print(json.dumps({'trial':idx,'case':case['name'],'backend':backend,'variant':variant,'classification':valid}),flush=True)
    if stopped:break
   if stopped:break
 comparisons=[]
 for block in blocks:
  group=[r for r in trial_rows if r['block']==block['block']];item={'block':block['block'],'complete':len(group)==3 and all(r['classification']=='valid' for r in group),'exact_diagnostics_match':None}
  if item['complete']:
   observations={r['variant']:read(r['session'])['records'] for r in group};item['exact_diagnostics_match']=observations['plain']==observations['timed']==observations['timed_accounting']
  comparisons.append(item)
 (out/'block-comparisons.json').write_text(json.dumps(comparisons,indent=2)+'\n')
 post=checks()
 try:
  if sha(out/'schedule.json')!=meta['schedule_sha256']:post.append('schedule changed')
 except OSError as e:post.append('schedule unavailable: '+repr(e))
 (out/'summary.json').write_text(json.dumps({'counts':dict(counts),'sessions':idx,'expected':144,'stopped':stopped,'postflight_errors':post,'host_after':load_snapshot(),'exact_diagnostic_mismatch_blocks':[x['block'] for x in comparisons if x['exact_diagnostics_match'] is False]},indent=2)+'\n');return 0 if idx==144 and not post and not stopped and all(k in ('valid','censored_timeout') for k in counts) and not any(x['exact_diagnostics_match'] is False for x in comparisons) else 1
if __name__=='__main__':sys.exit(main())
