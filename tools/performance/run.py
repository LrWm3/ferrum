#!/usr/bin/env python3
"""Serial paired process/session measurements from frozen compatibility inputs."""
import argparse, collections, decimal, hashlib, json, os, pathlib, platform, random, re, resource, shutil, subprocess, sys, time
P=pathlib.Path
TIMER=P('/usr/bin/time')
TIMER_FORMAT='wall_s=%e\nuser_s=%U\nsystem_s=%S\nmax_rss_kib=%M\nexit_status=%x' 

def sha(p):
    with open(p,'rb') as f: return hashlib.file_digest(f,'sha256').hexdigest()
def read(p): return json.loads(P(p).read_text())
def check(p,h):
    if sha(p)!=h: raise ValueError(f'hash mismatch: {p}')
def validate_cache_policy(settings, frozen, policy):
    env=settings.get('environment')
    if not isinstance(env,dict) or env.get('FERRUM_BENCH_INTERNAL_CACHES')!=policy:
        raise ValueError('frozen settings.environment.FERRUM_BENCH_INTERNAL_CACHES must match --internal-caches')
    capabilities=settings.get('driver_capabilities')
    if not isinstance(capabilities,dict):raise ValueError('missing frozen driver capability markers')
    for backend in ('source','native'):
        marker=capabilities.get(backend)
        if not isinstance(marker,dict) or marker.get('kind')!='ferrum-bench-cache-policy-v1' or marker.get('variant')!='plain' or marker.get('environment')!='FERRUM_BENCH_INTERNAL_CACHES':
            raise ValueError(f'missing plain cache-policy capability marker for {backend}')
        artifact=marker.get('artifact');expected=marker.get('sha256')
        if not isinstance(artifact,str) or not isinstance(expected,str):raise ValueError(f'missing marked driver artifact for {backend}')
        artifact=str(P(artifact).resolve())
        if frozen.get(artifact)!=expected:raise ValueError(f'driver capability artifact not bound to frozen evidence for {backend}')
        prefix=settings[backend]
        if any(arg=='--disableCaches' or arg.startswith('--disableCaches=') for arg in prefix):raise ValueError(f'cache option belongs to driver, not {backend} prefix')
        if backend=='native':
            exe=shutil.which(prefix[0],path=env.get('PATH',os.environ.get('PATH'))) or prefix[0]
            if str(P(exe).resolve())!=artifact:raise ValueError('native capability artifact is not executed driver')
        else:
            classpaths=[prefix[i+1] for i,arg in enumerate(prefix[:-1]) if arg in ('-cp','-classpath','--class-path')]
            if 'SourceSession' not in prefix or len(classpaths)!=1 or str((P(classpaths[0].split(os.pathsep)[0])/'SourceSession.class').resolve())!=artifact:
                raise ValueError('source capability artifact is not executed SourceSession class')

def preflight(inputs,root,fixtures,policy):
    source=read(inputs/'source-manifest.json'); snap=P(source['compiled_source_snapshot'])
    if source['runtime_revision']!=source['tooling_revision']: raise ValueError('revision mismatch')
    for name,h in source['checked_source_files'].items(): check(snap/name,h);check(root/name,h)
    ev=read(inputs/'evidence-stdio.json'); frozen={}
    for a in list(ev['binaries'].values())+ev.get('extra_artifacts',[]):
        p=str(P(a['path']).resolve());check(p,a['sha256']);frozen[p]=a['sha256']
    for repo in ev['repositories'].values():
        path=P(repo['root']); rev=subprocess.check_output(['git','rev-parse','HEAD'],cwd=path,text=True).strip(); status=subprocess.check_output(['git','status','--porcelain','--untracked-files=all'],cwd=path,text=True)
        if (rev,status)!=(repo['revision'],repo['git_status']): raise ValueError(f'changed repository: {path}')
        inventory={str(p.relative_to(path)):sha(p) for p in sorted(path.rglob('*.vpr')) if p.is_file()}
        if inventory!=repo['vpr_files']: raise ValueError(f'changed Viper inventory: {path}')
    settings=read(inputs/'settings-stdio.json')
    for backend in ('source','native'):
        prefix=settings[backend];exe=shutil.which(prefix[0],path=settings.get('environment',{}).get('PATH',os.environ.get('PATH'))) or prefix[0];required={str(P(exe).resolve())}
        for token in prefix[1:]:
            for part in token.split(os.pathsep):
                if P(part).is_file():required.add(str(P(part).resolve()))
        for i,token in enumerate(prefix[:-1]):
            if token in ('-cp','-classpath','--class-path'):
                for entry in prefix[i+1].split(os.pathsep):
                    if P(entry).is_dir():required.update(str(p.resolve()) for p in P(entry).rglob('*.class') if p.is_file())
        declared=settings.get('command_artifacts',{}).get(backend)
        if not isinstance(declared,list):raise ValueError(f'missing {backend} command artifacts')
        required.update(str(P(p).resolve()) for p in declared)
        if required-frozen.keys():raise ValueError(f'unfrozen command artifacts: {sorted(required-frozen.keys())}')
    validate_cache_policy(settings,frozen,policy)
    shared=settings['shared_options']
    if shared!=['--timeout','30']:raise ValueError('expected baseline stdio settings with only --timeout 30')
    cases=read(fixtures)['cases']
    if not cases or len({x['name'] for x in cases})!=len(cases):raise ValueError('empty or duplicate cases')
    for case in cases:
        check(case['path'],case['sha256']);e=case['expect']
        if e.get('outcome') not in ('verified','failure') or not isinstance(e.get('errors'),list):raise ValueError('case requires explicit proof outcome and error ID/position multiset')
        if e['outcome']=='verified' and e['errors']:raise ValueError('verified expectation requires empty errors')
        if e['outcome']=='failure' and (not e['errors'] or any(not x.get('id') or not x.get('position') or x['position']=='<no position>' for x in e['errors'])):raise ValueError('failure requires exact error IDs and positions')
    runner=root/'tools/compatibility/run_session.py'
    if not runner.is_file():raise ValueError('missing runner')
    return source,settings,ev,frozen,cases,runner

def assess(session,case,repeats):
    records=session.get('records',[]);expected=case['expect'];infra={'prover.interaction.failed','external.tool.error','exceptional.error','dependencynotfound.error'}
    if any(any(e.get('id') in infra for e in r.get('errors',[])) for r in records):return 'invalid_infrastructure'
    if session.get('protocol_errors')!=[] or session.get('cleanup_pending')!=[]:return 'invalid_session'
    if session.get('outcome')=='harness_timeout':return 'censored_timeout'
    if session.get('outcome')!='completed' or session.get('exit_code')!=0:return 'invalid_session'
    if any(r.get('outcome') in ('timeout','verifier_timeout') or any(e.get('id')=='timeout.error' for e in r.get('errors',[])) for r in records):return 'censored_timeout'
    if len(records)!=repeats or any(r.get('case')!=case['path'] for r in records):return 'invalid_coverage'
    for r in records:
        errs=r.get('errors',[])
        if any(e.get('id') in infra for e in errs):return 'invalid_infrastructure'
        if r.get('outcome')!=expected['outcome']:return 'unexpected_outcome'
        if collections.Counter((e.get('id'),e.get('position')) for e in errs)!=collections.Counter((e['id'],e['position']) for e in expected['errors']):return 'unexpected_diagnostics'
    return 'valid'

def make_schedule(cases, pairs, seed, reuse_cases):
    rng=random.Random(seed)
    blocks=[{'case':case['name'], 'workers':workers, 'parallel_branches':branch, 'mode':mode, 'pair':pair, 'case_count':1 if mode=='fresh' else reuse_cases}
            for case in cases for workers in (1,2,4) for branch in (False,True)
            for mode in ('fresh','reused') for pair in range(pairs)]
    rng.shuffle(blocks)
    for index,block in enumerate(blocks):
        order=['source','native'];rng.shuffle(order);block['block']=index;block['order']=order
    return blocks

def verifier_options(timeout, workers, branch):
    # The benchmark drivers apply their explicitly frozen cache policy.
    return ['--timeout',str(timeout),'--numberOfParallelVerifiers',str(workers)]+(['--parallelizeBranches'] if branch else [])

def parse_timer(path):
    try: raw=P(path).read_text(errors='replace')
    except OSError as e:return {'complete':False,'error':repr(e),'raw':None,'values':None}
    lines=raw.splitlines();expected=['wall_s','user_s','system_s','max_rss_kib','exit_status'];values={};errors=[]
    for line in lines:
        key,sep,value=line.partition('=')
        if not sep or key not in expected or key in values: errors.append('unexpected or duplicate timer line: '+line);continue
        values[key]=value
    if set(values)!=set(expected):errors.append('missing timer fields')
    for key in ('wall_s','user_s','system_s'):
        if key in values:
            try:
                if not re.fullmatch(r'[0-9]+(?:\.[0-9]+)?',values[key]) or decimal.Decimal(values[key])<0:raise ValueError('invalid decimal')
            except (decimal.InvalidOperation,ValueError):errors.append('invalid '+key)
    for key in ('max_rss_kib','exit_status'):
        if key in values and not re.fullmatch(r'[0-9]+',values[key]):errors.append('invalid '+key)
    if values.get('exit_status')!='0':errors.append('verifier command did not exit zero')
    return {'complete':not errors,'errors':errors,'raw':raw,'values':values}

def host_metadata():
    def read_optional(path):
        try:return P(path).read_text().strip()
        except OSError:return None
    def version(tool):
        exe=shutil.which(tool)
        if not exe:return None
        try:
            p=subprocess.run([exe,'--version'],stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True,timeout=10,check=False)
            return {'path':str(P(exe).resolve()),'sha256':sha(exe),'exit':p.returncode,'output':p.stdout.strip()}
        except (OSError,subprocess.TimeoutExpired) as e:return {'path':exe,'error':str(e)}
    return {'uname':platform.uname()._asdict(),'python':sys.version,'python_executable':str(P(sys.executable).resolve()),
            'cpu_count':os.cpu_count(),'cpu_info':read_optional('/proc/cpuinfo'),'meminfo':read_optional('/proc/meminfo'),
            'governors':{str(p):read_optional(p) for p in sorted(P('/sys/devices/system/cpu').glob('cpu[0-9]*/cpufreq/scaling_governor'))},
            'rustc':version('rustc'),'cargo':version('cargo'),
            'environment':{k:os.environ.get(k) for k in ('PATH','LD_LIBRARY_PATH','JAVA_HOME','RUSTUP_TOOLCHAIN','RUSTFLAGS','CARGO_BUILD_JOBS')}}

def load_snapshot():
    try:load=os.getloadavg()
    except OSError:load=None
    return {'wall_time_unix_ns':time.time_ns(),'monotonic_ns':time.monotonic_ns(),'load_average':load,
            'memory_available':next((line for line in (P('/proc/meminfo').read_text().splitlines() if P('/proc/meminfo').exists() else []) if line.startswith('MemAvailable:')),None)}

def verify_artifacts(artifacts):
    errors=[]
    for path,h in artifacts.items():
        try:check(path,h)
        except (OSError,ValueError) as e:errors.append(str(e))
    return errors

def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--inputs',type=P,required=True);p.add_argument('--tools-root',type=P,required=True);p.add_argument('--fixtures',type=P,required=True);p.add_argument('--output',type=P,required=True);p.add_argument('--pairs',type=int,required=True);p.add_argument('--seed',type=int,required=True);p.add_argument('--verifier-timeout',type=int,required=True);p.add_argument('--outer-per-case',type=int,required=True);p.add_argument('--reuse-cases',type=int,default=3);p.add_argument('--internal-caches',choices=('on','off'),required=True)
    a=p.parse_args()
    if a.pairs < 2 or a.reuse_cases < 2 or min(a.verifier_timeout, a.outer_per_case) <= 0:p.error('pairs and reuse-cases >=2; timeouts >0 required')
    inputs,root,fixtures,out=a.inputs.resolve(),a.tools_root.resolve(),a.fixtures.resolve(),a.output.resolve()
    if out.exists():raise FileExistsError(f'output exists: {out}')
    source,settings,ev,frozen,cases,runner=preflight(inputs,root,fixtures,a.internal_caches)
    artifacts={str(p):sha(p) for p in [inputs/'source-manifest.json',inputs/'settings-stdio.json',inputs/'evidence-stdio.json',fixtures,P(__file__).resolve(),P(sys.executable).resolve(),runner,TIMER.resolve()]+[P(c['path']) for c in cases]};artifacts.update(frozen)
    for name,h in source['checked_source_files'].items():
        artifacts[str(P(source['compiled_source_snapshot'])/name)]=h;artifacts[str(root/name)]=h
    out.mkdir(parents=True,exist_ok=False);(out/'sessions').mkdir();(out/'timers').mkdir()
    meta={'runtime_revision':source['runtime_revision'],'internal_caches':a.internal_caches,'source_manifest':source,'evidence':ev,'settings':settings,'fixtures':cases,'artifacts':artifacts,'pairs':a.pairs,'seed':a.seed,'verifier_timeout_seconds':a.verifier_timeout,'outer_seconds_per_case':a.outer_per_case,'reuse_cases':a.reuse_cases,'measurements':'primary wall is GNU time verifier-command elapsed; supervisor wall includes Python startup, polling and cleanup; verifier user/system CPU and max RSS are timer-reported process accounting, not solver or symbolic-only attribution','timer':{'path':str(TIMER),'sha256':sha(TIMER),'format':TIMER_FORMAT,'resolution_limit':'GNU time decimal seconds typically hundredths; not nanoseconds','placement':'inside owned-process runner around verifier command only'},'host_toolchain':host_metadata(),'host_before':load_snapshot(),'schedule_file':'schedule.json','limitations':['fresh process does not clear OS caches','reused session is one batch wall and CPU, not individual request timings','worker and solver execution overlap; aggregate CPU is not wall','timed-out results are censored','artifact hashing outside timed spans warms filesystem caches','GNU time can alter signal exit representation; timeout or abnormal termination remains censored or invalid','baseline inputs do not establish direct-Prusti AST equivalence']}
    schedule=make_schedule(cases,a.pairs,a.seed,a.reuse_cases)
    (out/'schedule.json').write_text(json.dumps({'seed':a.seed,'blocks':schedule},indent=2)+'\n')
    meta['schedule_sha256']=sha(out/'schedule.json')
    (out/'manifest.json').write_text(json.dumps(meta,indent=2)+'\n')
    trial=0; outcomes=collections.Counter(); case_by_name={c['name']:c for c in cases}; stopped=False
    with (out/'trials.jsonl').open('x') as log:
        for block in schedule:
            case=case_by_name[block['case']]; workers=block['workers'];branch=block['parallel_branches'];mode=block['mode'];pair=block['pair'];count=block['case_count'];order=block['order']
            for backend in order:
                before_errors=verify_artifacts(artifacts)
                if before_errors:
                    (out/'artifact-failure.json').write_text(json.dumps({'trial':trial,'boundary':'before','errors':before_errors},indent=2)+'\n');stopped=True;break
                session=out/'sessions'/f'{trial:06d}-{backend}.json';timer_path=out/'timers'/f'{trial:06d}-{backend}.time';casepath=case['path'];opts=verifier_options(a.verifier_timeout,workers,branch)
                verifier_command=[*settings[backend],*opts,'--',*([casepath]*count)]
                command=[sys.executable,str(runner),'--timeout',str(a.outer_per_case*count+30),'--output',str(session),'--',str(TIMER),'-f',TIMER_FORMAT,'-o',str(timer_path),'--',*verifier_command]
                host_before=load_snapshot();before=resource.getrusage(resource.RUSAGE_CHILDREN);start=time.monotonic_ns()
                try:
                    proc=subprocess.run(command,env={**os.environ,**settings.get('environment',{})},stdout=subprocess.PIPE,stderr=subprocess.STDOUT,check=False)
                    runner_exit=proc.returncode;runner_output=proc.stdout.decode(errors='replace')
                except OSError as exc:
                    runner_exit=None;runner_output=repr(exc)
                wall=time.monotonic_ns()-start;after=resource.getrusage(resource.RUSAGE_CHILDREN);host_after=load_snapshot()
                try:data=read(session);valid=assess(data,case,count)
                except Exception as exc:data={};valid='invalid_result:'+repr(exc)
                if runner_exit != 0:valid='runner_error'
                timer=parse_timer(timer_path)
                if valid=='valid' and not timer['complete']:valid='invalid_timer'
                after_errors=verify_artifacts(artifacts)
                if after_errors:valid='invalid_artifact_change';stopped=True
                row={'trial':trial,'internal_caches':a.internal_caches,'block':block['block'],'case':case['name'],'case_sha256':case['sha256'],'pair':pair,'order':order,'backend':backend,'workers':workers,'parallel_branches':branch,'mode':mode,'case_count':count,'supervisor_wall_ns':wall,'verifier_wall_s':timer['values']['wall_s'] if valid=='valid' and timer['complete'] else None,'timer':timer,'timer_path':str(timer_path),'timer_sha256':sha(timer_path) if timer_path.is_file() else None,'verifier_command':verifier_command,'child_user_s':after.ru_utime-before.ru_utime,'child_system_s':after.ru_stime-before.ru_stime,'classification':valid,'runner_exit':runner_exit,'runner_output':runner_output,'session':str(session),'session_sha256':sha(session) if session.is_file() else None,'command':command,'environment_overrides':settings.get('environment',{}),'host_before':host_before,'host_after':host_after,'artifact_errors_before':before_errors,'artifact_errors_after':after_errors}
                outcomes[valid]+=1;log.write(json.dumps(row)+'\n');log.flush();print(json.dumps({k:row[k] for k in ('trial','case','backend','mode','classification')}),flush=True);trial+=1
                if stopped:break
            if stopped:break
    postflight_errors=verify_artifacts(artifacts)
    try:preflight(inputs,root,fixtures,a.internal_caches)
    except Exception as e:postflight_errors.append('full postflight: '+repr(e))
    try:
        if sha(out/'schedule.json')!=meta['schedule_sha256']:postflight_errors.append('schedule changed')
    except OSError as e:postflight_errors.append('schedule unavailable: '+repr(e))
    (out/'summary.json').write_text(json.dumps({'counts':dict(outcomes),'trials':trial,'scheduled_trials':len(schedule)*2,'stopped_early':stopped,'postflight_errors':postflight_errors,'host_after':load_snapshot()},indent=2)+'\n')
    return 0 if not stopped and not postflight_errors and trial==len(schedule)*2 and all(k in ('valid','censored_timeout') for k in outcomes) else 1

if __name__=='__main__':sys.exit(main())
