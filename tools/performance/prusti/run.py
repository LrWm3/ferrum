#!/usr/bin/env python3
"""Direct-Prusti paired benchmark; requires independently prepared inputs."""
import argparse,collections,decimal,hashlib,json,os,pathlib,platform,random,re,resource,shutil,signal,socket,subprocess,sys,tempfile,time
P=pathlib.Path
TIMER=P("/usr/bin/time")
SESSION=P(__file__).resolve().with_name("session_supervisor.py")
SERVICE=P(__file__).resolve().with_name("service_supervisor.py")
PHASES=('Rust to VIR encoding','VIR conversion','backend verification')
PHASE_RE=re.compile(r'\[benchmark-phase\] (Rust to VIR encoding|VIR conversion|backend verification) (\d+) ns')
FAIL_RE=re.compile(r'^error(?:\[[^\]]+\])?: (.+)$',re.MULTILINE)

def sha(p):
    with open(p,'rb') as f:return hashlib.file_digest(f,'sha256').hexdigest()
def read(p):return json.loads(P(p).read_text())
def checked(p,h):
    if sha(p)!=h:raise ValueError(f'hash changed: {p}')
def tree_hash(root):
    h=hashlib.sha256()
    for p in sorted(root.rglob('*')):
        if p.is_symlink():raise ValueError(f'seed contains symlink: {p}')
        if p.is_file():h.update(str(p.relative_to(root)).encode()+b'\0'+bytes.fromhex(sha(p)))
    return h.hexdigest()
CARGO_CACHE_SIGNATURE=b'Signature: 8a477f597d28d172789f06886806bc55\n'
def ensure_scratch_cache_marker(scratch, scratch_root):
    scratch=P(scratch);scratch_root=P(scratch_root)
    if scratch.is_symlink() or scratch.parent.is_symlink() or scratch.parent.resolve()!=scratch_root.resolve() or not scratch.is_dir():
        raise ValueError('scratch must be a direct owned directory')
    verify=scratch/'verify'
    if verify.is_symlink() or not verify.is_dir() or verify.resolve().parent!=scratch.resolve():
        raise ValueError('verify target must be an owned directory')
    marker=verify/'CACHEDIR.TAG'
    try:
        fd=os.open(marker,os.O_WRONLY|os.O_CREAT|os.O_EXCL|os.O_NOFOLLOW,0o644)
    except FileExistsError:
        if marker.is_symlink() or not marker.is_file() or not marker.read_bytes().startswith(CARGO_CACHE_SIGNATURE):raise ValueError('invalid existing cache marker')
    else:
        with os.fdopen(fd,'wb') as f:f.write(CARGO_CACHE_SIGNATURE)
def status(code,timed,text,case):
    if timed or 'Verification timed out' in text:return 'censored_timeout'
    if re.search(r'\[Prusti: internal error\]|internal compiler error|thread .* panicked|\[Prusti: unsupported feature\]',text):return 'invalid_backend'
    errors=[e for e in FAIL_RE.findall(text) if not e.startswith(('could not compile','aborting due to'))]
    exp=case['expect']
    if code!=exp['exit'] or errors!=exp['errors'] or (exp.get('location') and exp['location'] not in text):return 'unexpected_result'
    return 'valid'
def parse_timer(path):
    try: raw=P(path).read_text(errors='replace')
    except OSError as e:return {'complete':False,'errors':[repr(e)],'raw':None,'values':{}}
    expected=('wall_s','user_s','system_s','max_rss_kib','exit_status');values={};errors=[]
    for line in raw.splitlines():
        key,sep,value=line.partition('=')
        if not sep or key not in expected or key in values:errors.append('unexpected or duplicate timer line: '+line);continue
        values[key]=value
    if set(values)!=set(expected):errors.append('missing timer fields')
    for key in ('wall_s','user_s','system_s'):
        if key in values:
            try:
                if not re.fullmatch(r'[0-9]+(?:\.[0-9]+)?',values[key]) or not decimal.Decimal(values[key]).is_finite() or decimal.Decimal(values[key])<0:raise ValueError('invalid decimal')
            except (ValueError,decimal.InvalidOperation):errors.append('invalid '+key)
    for key in ('max_rss_kib','exit_status'):
        if key in values and not re.fullmatch(r'[0-9]+',values[key]):errors.append('invalid '+key)
    return {'complete':not errors,'errors':errors,'raw':raw,'values':values}

def host_metadata():
    def optional(path):
        try:return P(path).read_text().strip()
        except OSError:return None
    return {'uname':platform.uname()._asdict(),'python':sys.version,'python_executable':str(P(sys.executable).resolve()),'cpu_count':os.cpu_count(),'cpu_info':optional('/proc/cpuinfo'),'meminfo':optional('/proc/meminfo'),'governors':{str(p):optional(p) for p in sorted(P('/sys/devices/system/cpu').glob('cpu[0-9]*/cpufreq/scaling_governor'))},'environment':{k:os.environ.get(k) for k in ('PATH','LD_LIBRARY_PATH','JAVA_HOME','RUSTUP_TOOLCHAIN','RUSTFLAGS','CARGO_BUILD_JOBS')}}

def load_snapshot():
    try:load=os.getloadavg()
    except OSError:load=None
    try:mem=next((line for line in P('/proc/meminfo').read_text().splitlines() if line.startswith('MemAvailable:')),None)
    except OSError:mem=None
    return {'wall_time_unix_ns':time.time_ns(),'monotonic_ns':time.monotonic_ns(),'load_average':load,'memory_available':mem}

def dependency_events(text,package):
    events=[{'action':m.group(1),'package':m.group(2),'line':m.group(0).strip()} for m in re.finditer(r'^[ \t]*(Checking|Compiling)[ \t]+([A-Za-z0-9_-]+)[ \t]+v[^ \t\r\n]+(?:[ \t]|$)[^\n]*',text,re.MULTILINE)]
    valid=len(events)==1 and events[0]['action']=='Checking' and events[0]['package']==package
    return {'valid':valid,'events':events}

def phase_records(text):
    found=collections.defaultdict(list)
    for name,value in PHASE_RE.findall(text):found[name].append(int(value))
    return {n:found[n] for n in PHASES}
def make_schedule(cases,workers,branch,mode,pairs,seed):
    rng=random.Random(seed)
    blocks=[{'case':case['name'],'workers':w,'parallel_branches':b,'mode':m,'pair':p} for case in cases for w in workers for b in branch for m in mode for p in range(pairs)]
    rng.shuffle(blocks)
    for index,block in enumerate(blocks):
        order=['native','jvm'];rng.shuffle(order);block['block']=index;block['order']=order
    return blocks

def assign_endpoints(schedule,base):
    if base+len(schedule)*2-1>65535:raise ValueError('base port plus scheduled blocks exceeds 65535')
    for block in schedule:
        block['endpoints']={b:f"127.0.0.1:{base+2*block['block']+i}" for i,b in enumerate(block['order'])} if block['mode']=='service' else {}
    return schedule

def effective_records(rows):
    bad={r['block_id'] for r in rows if r['classification']=='invalid_service_cleanup'}
    result=[]
    for row in rows:
        if row['classification']=='invalid_service_cleanup':continue
        revised=dict(row)
        if row.get('block_id') in bad:
            revised['original_classification']=row['classification'];revised['classification']='invalid_service_cleanup'
        result.append(revised)
    return result,bad
def terminate(p):
    if p.poll() is None:
        p.terminate()
        try:p.wait(timeout=8)
        except subprocess.TimeoutExpired:
            p.kill();p.wait()

def run_process(cmd,cwd,env,timeout,logpath):
    session=logpath.with_suffix('.session.json'); timer=logpath.with_suffix('.time')
    command=[sys.executable,str(SESSION),'--timeout',str(timeout),'--output',str(session),'--',str(TIMER),'-q','-f','wall_s=%e\nuser_s=%U\nsystem_s=%S\nmax_rss_kib=%M\nexit_status=%x','-o',str(timer),'--',*cmd]
    r=subprocess.run(command,cwd=cwd,env=env,stdout=subprocess.PIPE,stderr=subprocess.PIPE,timeout=timeout+15)
    d=read(session) if session.exists() else {};logpath.write_text(d.get('raw_output',''))
    parsed=parse_timer(timer);values=parsed['values'];complete=parsed['complete']
    try:
        wall=float(values['wall_s']);user=float(values['user_s']);system=float(values['system_s']);code=int(values['exit_status'])
    except (KeyError,ValueError):wall=user=system=None;code=None;complete=False
    cleanup_ok=r.returncode==0 and d.get('cleanup_pending')==[] and d.get('protocol_errors')==[]
    timed=d.get('outcome')=='harness_timeout'
    if d.get('exit_code') != code and not timed:complete=False
    return code,timed,wall,user,system,complete,cleanup_ok

def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--prepared',type=P,required=True,help='frozen snapshot, seeds, server drivers, dump parity evidence');ap.add_argument('--cases',type=P,required=True);ap.add_argument('--output',type=P,required=True);ap.add_argument('--pairs',type=int,required=True);ap.add_argument('--seed',type=int,required=True);ap.add_argument('--verifier-timeout',type=int,required=True);ap.add_argument('--outer-timeout',type=int,required=True);ap.add_argument('--requests',type=int,default=3);ap.add_argument('--port',type=int,default=59861);ap.add_argument('--pilot',action='store_true');ap.add_argument('--workers',type=int,nargs='+',choices=(1,2,4));ap.add_argument('--branch',nargs='+',choices=('off','on'));ap.add_argument('--mode',nargs='+',choices=('fresh','service'))
    a=ap.parse_args()
    if a.pairs<(1 if a.pilot else 2) or a.requests<2 or min(a.verifier_timeout,a.outer_timeout)<=0 or not 1024<=a.port<=65535:ap.error('positive budgets, >=2 requests, >=2 pairs (or 1 in pilot), and valid unprivileged port required')
    prepared=read(a.prepared);cases=read(a.cases)['cases'];root=P(prepared['source_snapshot']).resolve();out=a.output.resolve()
    policy={'outer_result_cache':'off','silicon_internal_caches':'production_default_on'}
    if prepared.get('cache_policy')!=policy:raise ValueError('primary run requires outer result cache off and Silicon internal caches at production default on')
    if any('--disableCaches' in str(v) for v in prepared.get('environment',{}).values()):raise ValueError('primary run rejects --disableCaches')
    if prepared.get('environment',{}).get('FERRUM_BENCH_INTERNAL_CACHES','on')!='on':raise ValueError('primary run rejects internal-caches-off setting')
    if out.exists():raise FileExistsError(out)
    if root==P('/tmp/prusti-stage4-compatibility').resolve() or root==P('/home/will/wk/exp/prusti-stdlib').resolve():raise ValueError('use an isolated, frozen source copy')
    manifest=read(prepared['source_manifest'])
    for rel,h in manifest['files'].items():checked(root/rel,h)
    for rel,h in manifest['pcg_files'].items():checked(root/'pcg'/rel,h)
    if manifest['ferrum_revision']!='afdf10cf59106c38d09df32939f1aa9c77d0b989':raise ValueError('unexpected Ferrum pin')
    for name,info in prepared['artifacts'].items():checked(info['path'],info['sha256'])
    for k in ('JAVA_HOME','VIPER_HOME','Z3_EXE','LD_LIBRARY_PATH'):
        if not prepared['environment'].get(k):raise ValueError(f'missing environment: {k}')
    if P(prepared['environment']['Z3_EXE']).resolve()!=P(prepared['artifacts']['z3']['path']).resolve():raise ValueError('Z3_EXE differs from frozen Z3')
    if (P(prepared['environment']['JAVA_HOME'])/'bin/java').resolve()!=P(prepared['artifacts']['java']['path']).resolve():raise ValueError('JAVA_HOME differs from frozen Java')
    if (P(prepared['environment']['VIPER_HOME'])/'viperserver.jar').resolve()!=P(prepared['artifacts']['jvm_bundle']['path']).resolve():raise ValueError('VIPER_HOME differs from frozen bundle')
    required_artifacts=('z3','java','jvm_bundle','cargo','rustc')
    if any(k not in prepared['artifacts'] for k in required_artifacts):raise ValueError('missing required tool or JVM bundle hashes')
    for backend in ('native','jvm'):
        for name in ('cargo_prusti','prusti_driver','prusti_rustc','server_driver'):
            if name not in prepared['backends'][backend]:raise ValueError(f'missing {backend} {name}')
            artifact=prepared['backends'][backend][name]
            if not any(str(P(v['path']).resolve())==str(P(artifact).resolve()) for v in prepared['artifacts'].values()):raise ValueError(f'unfrozen {artifact}')
        if any(P(prepared['backends'][backend][x]).resolve().parent != P(prepared['backends'][backend]['cargo_prusti']).resolve().parent for x in ('prusti_driver','prusti_rustc')):raise ValueError('cargo-prusti must sit beside the frozen driver and prusti-rustc')
        for suite in ('sequence','iterator'):
            seed=prepared['backends'][backend]['target_seeds'][suite]
            if tree_hash(P(seed['path']))!=seed['tree_sha256']:raise ValueError('seed hash mismatch')
    parity=read(prepared['dump_parity_evidence'])
    for case in cases:
        fixture=root/'prusti-tests/tests/cargo_verify'/f"stdlib_{case['suite']}_spec";source=fixture/'src/bin'/f"{case['name']}.rs";checked(source,case['source_sha256'])
        if not (fixture/'Cargo.lock').is_file():raise ValueError(f'prepare and freeze fixture lockfile first: {fixture}')
        lock=prepared['fixture_locks'][case['suite']];checked(fixture/'Cargo.lock',lock)
        proof=parity[case['name']]
        if proof.get('cache_policy')!=policy or proof.get('source_sha256')!=case['source_sha256'] or proof.get('prusti_pin')!=manifest['prusti_revision'] or proof.get('outcomes_checked') is not True:raise ValueError('unvalidated calibration')
        for b in ('native','jvm'):
            checked(proof[b]['path'],proof[b]['sha256']);checked(proof[b]['log'],proof[b]['log_sha256'])
            if status(proof[b]['exit_code'],False,P(proof[b]['log']).read_text(errors='replace'),case)!='valid':raise ValueError(f'calibration proof failed: {case["name"]}/{b}')
        if proof['native']['sha256']!=proof['jvm']['sha256']:raise ValueError(f'dump bytes differ: {case["name"]}')
    frozen={str(a.prepared):sha(a.prepared),str(a.cases):sha(a.cases),str(P(prepared['source_manifest'])):sha(prepared['source_manifest']),str(P(prepared['dump_parity_evidence'])):sha(prepared['dump_parity_evidence']),str(P(__file__).resolve()):sha(__file__),str(SESSION):sha(SESSION),str(SERVICE):sha(SERVICE),str(TIMER):sha(TIMER),str(P(sys.executable).resolve()):sha(sys.executable)}
    for v in prepared['artifacts'].values():frozen[v['path']]=v['sha256']
    for rel,h in manifest['files'].items():frozen[str(root/rel)]=h
    for rel,h in manifest['pcg_files'].items():frozen[str(root/'pcg'/rel)]=h
    for case in cases:
        proof=parity[case['name']]
        for b in ('native','jvm'):
            frozen[proof[b]['path']]=proof[b]['sha256'];frozen[proof[b]['log']]=proof[b]['log_sha256']
    for case in cases:
        fixture=root/'prusti-tests/tests/cargo_verify'/f"stdlib_{case['suite']}_spec"
        frozen[str(fixture/'src/bin'/f"{case['name']}.rs")]=case['source_sha256']
        frozen[str(fixture/'Cargo.lock')]=prepared['fixture_locks'][case['suite']]
    def verify_frozen():
        errors=[]
        for path,h in frozen.items():
            try:checked(path,h)
            except (OSError,ValueError) as e:errors.append(str(e))
        for backend in ('native','jvm'):
            for suite in ('sequence','iterator'):
                seed=prepared['backends'][backend]['target_seeds'][suite]
                try:
                    if tree_hash(P(seed['path']))!=seed['tree_sha256']:errors.append('seed changed: '+seed['path'])
                except (OSError,ValueError) as e:errors.append(str(e))
        return errors
    if verify_frozen():raise ValueError('initial frozen artifact check failed')
    out.mkdir(parents=True,exist_ok=False);(out/'logs').mkdir();(out/'scratch').mkdir()
    metadata={'prepared':prepared,'prepared_sha256':sha(a.prepared),'cases':cases,'cases_sha256':sha(a.cases),'source_manifest_sha256':sha(prepared['source_manifest']),'dump_parity_sha256':sha(prepared['dump_parity_evidence']),'dump_parity':parity,'runner_sha256':sha(__file__),'frozen_artifacts':frozen,'timer_format':'wall_s=%e, user_s=%U, system_s=%S, max_rss_kib=%M, exit_status=%x; GNU time -q; wall resolution typically 0.01 s','pilot':a.pilot,'selected_workers':a.workers or [1,2,4],'selected_branch':a.branch or ['off','on'],'selected_modes':a.mode or ['fresh','service'],'pairs':a.pairs,'seed':a.seed,'verifier_timeout':a.verifier_timeout,'outer_timeout':a.outer_timeout,'requests':a.requests,'host_toolchain':host_metadata(),'host_before':load_snapshot(),'limitations':['GNU time wall resolution is typically hundredths of a second','fresh process does not clear OS cache','service socket readiness is not warmed verifier','service CPU is not included in per-client child CPU','no exclusive solver/symbolic timing','cleanup cannot prove discovery of all escaped descendants']}
    counts=collections.Counter();trial=0
    schedule=make_schedule(cases,a.workers or [1,2,4],[x=='on' for x in (a.branch or ['off','on'])],a.mode or ['fresh','service'],a.pairs,a.seed)
    assign_endpoints(schedule,a.port)
    metadata['service_port_base']=a.port
    (out/'schedule.json').write_text(json.dumps({'seed':a.seed,'blocks':schedule},indent=2)+'\n');metadata['schedule_sha256']=sha(out/'schedule.json')
    (out/'manifest.json').write_text(json.dumps(metadata,indent=2)+'\n')
    by_name={c['name']:c for c in cases}
    with (out/'trials.jsonl').open('x') as records:
      for scheduled in schedule:
           case=by_name[scheduled['case']];workers=scheduled['workers'];branch=scheduled['parallel_branches'];mode=scheduled['mode'];pair=scheduled['pair'];order=scheduled['order']
           fixture=root/'prusti-tests/tests/cargo_verify'/f"stdlib_{case['suite']}_spec"
           for backend in order:
            cfg=prepared['backends'][backend];env={k:v for k,v in os.environ.items() if not k.startswith(('PRUSTI_','DEFAULT_PRUSTI_')) and k not in ('RUSTC','RUSTC_WRAPPER','RUSTC_WORKSPACE_WRAPPER','RUSTFLAGS','CARGO_ENCODED_RUSTFLAGS')};env.update(prepared['environment']);env.update({'RUSTUP_TOOLCHAIN':'nightly-2026-08-15','PRUSTI_VERIFY_MODE':'verify','PRUSTI_VIPER_BACKEND':'Ferrum' if backend=='native' else 'Silicon','PRUSTI_CHECK_OVERFLOWS':'true','PRUSTI_CHECK_PANICS':'true','PRUSTI_NO_VERIFY_DEPS':'true','PRUSTI_ENABLE_CACHE':'false','FERRUM_BENCH_PHASES':'1','FERRUM_BENCH_INTERNAL_CACHES':'on','PRUSTI_LOG':'info','CARGO_TERM_COLOR':'never','PRUSTI_CARGO_PATH':prepared['artifacts']['cargo']['path'],'PRUSTI_EXTRA_VERIFIER_ARGS':f'--timeout={a.verifier_timeout} --numberOfParallelVerifiers {workers}'+(' --parallelizeBranches' if branch else '')})
            env.update({'PRUSTI_VIPER_HOME':prepared['environment']['VIPER_HOME'],'PRUSTI_JAVA_HOME':prepared['environment']['JAVA_HOME'],'PRUSTI_SMT_SOLVER_PATH':prepared['environment']['Z3_EXE']})
            block_id=trial;trial+=1;endpoint=scheduled['endpoints'].get(backend);service_port=a.port+block_id;block=out/'logs'/f'{block_id:06d}-{backend}';block.mkdir();server=None;server_log=None;startup=None;ready=False
            try:
             if mode=='service':
              with socket.socket() as probe:
               probe.setsockopt(socket.SOL_SOCKET,socket.SO_REUSEADDR,1)
               try:probe.bind(('127.0.0.1',service_port))
               except OSError as e:raise RuntimeError('requested service port is not free') from e
              env['PRUSTI_SERVER_ADDRESS']=endpoint;env['PRUSTI_LOG_DIR']=str(block/'server-verifier');server_log=block/'server.log';f=server_log.open('xb');start=time.monotonic_ns();server=subprocess.Popen([sys.executable,str(SERVICE),str(block/'service-cleanup.json'),cfg['server_driver'],'--port',str(service_port)],cwd=root,env=env,stdout=f,stderr=subprocess.STDOUT,start_new_session=True)
              deadline=time.monotonic()+30
              while time.monotonic()<deadline and server.poll() is None:
               try:
                with socket.create_connection(('127.0.0.1',service_port),timeout=.25):ready=True
                break
               except OSError:time.sleep(.05)
              startup=time.monotonic_ns()-start
              if not ready:
               row={'block_id':block_id,'case':case['name'],'backend':backend,'mode':mode,'pair':pair,'workers':workers,'parallel_branches':branch,'endpoint':endpoint,'classification':'server_startup_failure','startup_ns':startup,'server_log':str(server_log)};records.write(json.dumps(row)+'\n');records.flush();counts[row['classification']]+=1;continue
             for request in range(1 if mode=='fresh' else a.requests):
              scratch=out/'scratch'/f'{block_id:06d}-{request}';seed_info=cfg['target_seeds'][case['suite']];seed=P(seed_info['path']);
              if tree_hash(seed)!=seed_info['tree_sha256']:raise RuntimeError('seed changed during run')
              if verify_frozen():raise RuntimeError('frozen artifact changed before trial')
              subprocess.run(['cp','-a','--reflink=auto',str(seed),str(scratch)],check=True)
              try:
               ensure_scratch_cache_marker(scratch,out/'scratch')
               env['CARGO_TARGET_DIR']=str(scratch);env['PRUSTI_LOG_DIR']=str(block/f'verifier-{request}');env['PRUSTI_DUMP_VIPER_PROGRAM']='false'
               clean=[prepared['artifacts']['cargo']['path'],'clean','--locked','-p',case['package'],'--target-dir',str(scratch/'verify')];cleanlog=block/f'clean-{request}.log';cc,ct,_,_,_,ccomplete,ccleanup=run_process(clean,fixture,env,120,cleanlog)
               if cc!=0 or ct or not ccomplete or not ccleanup:
                row={'block_id':block_id,'case':case['name'],'backend':backend,'mode':mode,'pair':pair,'request':request,'workers':workers,'parallel_branches':branch,'classification':'clean_failure','clean_log':str(cleanlog),'exit_code':cc};records.write(json.dumps(row)+'\n');records.flush();counts[row['classification']]+=1;continue
               offset=server_log.stat().st_size if server_log else 0
               cmd=[cfg['cargo_prusti'],'--locked','--bin',case['name']];log=block/f'client-{request}.log';host_before=load_snapshot();code,timed,wall,user,system,timer_complete,cleanup_ok=run_process(cmd,fixture,env,a.outer_timeout,log);host_after=load_snapshot();client=log.read_text(errors='replace');server_text=''
               if server_log:
                with server_log.open('rb') as sf:sf.seek(offset);server_bytes=sf.read();server_text=server_bytes.decode(errors='replace')
                (block/f'server-segment-{request}.log').write_bytes(server_bytes)
               phases=phase_records(client+'\n'+server_text);build=dependency_events(client,case['package']);timer_detail=parse_timer(log.with_suffix('.time'));result=status(code,timed,client,case)
               if verify_frozen():result='invalid_artifact_change'
               if not cleanup_ok:result='invalid_cleanup'
               elif not timer_complete and not timed:result='invalid_timer'
               if server is not None and server.poll() is not None:result='invalid_server_exit'
               if result=='valid' and not build['valid']:result='invalid_dependency_rebuild'
               if result=='valid' and any(len(phases[n])!=1 for n in PHASES):result='invalid_missing_or_ambiguous_phase'
               row={'block_id':block_id,'case':case['name'],'backend':backend,'mode':mode,'request':request,'first_request':request==0,'pair':pair,'backend_order':order,'workers':workers,'parallel_branches':branch,'classification':result,'exit_code':code,'outer_timeout':timed,'command_wall_s':wall,'timer_complete':timer_complete,'cleanup_ok':cleanup_ok,'child_user_s':user,'child_system_s':system,'endpoint':endpoint,'phase_ns':phases,'dependency_check':build,'timer':timer_detail,'host_before':host_before,'host_after':host_after,'service_startup_to_socket_ns':startup,'client_log':str(log),'client_log_sha256':sha(log),'server_log':str(server_log) if server_log else None,'server_log_offset':offset,'server_segment_sha256':sha(block/f'server-segment-{request}.log') if server_log else None,'command':cmd,'clean_command':clean}
               records.write(json.dumps(row)+'\n');records.flush();counts[result]+=1;print(json.dumps({k:row[k] for k in ('case','backend','mode','request','classification')}),flush=True)
              finally:shutil.rmtree(scratch)
            finally:
             if server is not None:
              terminate(server);f.close();audit=read(block/'service-cleanup.json') if (block/'service-cleanup.json').exists() else None
              if server.returncode!=0 or not audit or audit.get('cleanup_pending')!=[] or audit.get('error'):
               records.write(json.dumps({'classification':'invalid_service_cleanup','block_id':block_id,'case':case['name'],'backend':backend,'mode':mode,'pair':pair,'workers':workers,'parallel_branches':branch,'audit':audit})+'\n');records.flush();counts['invalid_service_cleanup']+=1
              (block/'server-summary.json').write_text(json.dumps({'server_log':str(server_log),'server_log_sha256':sha(server_log),'exit_code':server.returncode,'startup_ns':startup,'socket_ready':ready,'endpoint':endpoint},indent=2)+'\n')
    for rel,h in manifest['files'].items():checked(root/rel,h)
    for rel,h in manifest['pcg_files'].items():checked(root/'pcg'/rel,h)
    final_artifact_errors=verify_frozen()
    if sha(out/'schedule.json')!=metadata['schedule_sha256']:final_artifact_errors.append('schedule changed')
    rows=[json.loads(line) for line in (out/'trials.jsonl').read_text().splitlines()]
    effective,bad_blocks=effective_records(rows)
    effective_counts=collections.Counter(r['classification'] for r in effective)
    (out/'effective-trials.jsonl').write_text(''.join(json.dumps(r)+'\n' for r in effective))
    (out/'summary.json').write_text(json.dumps({'raw_counts':dict(counts),'effective_counts':dict(effective_counts),'invalid_service_blocks':sorted(bad_blocks),'final_artifact_errors':final_artifact_errors,'host_after':load_snapshot()},indent=2)+'\n');return 0 if not final_artifact_errors and not bad_blocks and all(k in ('valid','censored_timeout') for k in effective_counts) else 1
if __name__=='__main__':sys.exit(main())
