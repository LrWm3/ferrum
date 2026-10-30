import importlib.util,json,pathlib,collections,tempfile
p=pathlib.Path(__file__).resolve().parent;mod=importlib.util.spec_from_file_location('profile',p/'run.py');m=importlib.util.module_from_spec(mod);mod.loader.exec_module(m);spec=json.loads((p/'spec.json').read_text());blocks=m.schedule(spec['cases']);assert blocks==m.schedule(spec['cases']) and len(blocks)==48
keys=[(b['case'],b['workers'],b['parallel_branches'],b['backend'],b['repetition']) for b in blocks];assert len(set(keys))==48 and sum(len(b['variant_order']) for b in blocks)==144 and all(set(b['variant_order'])=={'plain','timed','timed_accounting'} for b in blocks)
c=spec['cases'][0];record={'case':c['path'],'outcome':'verified','errors':[]};session={'records':[record]*3,'outcome':'completed','exit_code':0,'cleanup_pending':[],'protocol_errors':[]};assert m.assess(session,c)=='valid';session['cleanup_pending']=[123];assert m.assess(session,c)=='invalid_session'
session['cleanup_pending']=[];session['records']=[{'case':c['path'],'outcome':'failure','errors':[{'id':'timeout.error'}]}]*3;assert m.assess(session,c)=='censored_timeout'
session['records']=[{'case':c['path'],'outcome':'timeout','errors':[]}]*3;assert m.assess(session,c)=='censored_timeout'
lines=[]
for i in range(3):lines.append('@@PERF@@'+json.dumps({'request':i,'case':c['path'],'clock':'monotonic','unit':'ns','phase':'request_total','elapsed_ns':'123'}))
phases,errors=m.phase_records('\n'.join(lines),c['path'],'timed');assert len(phases)==3 and errors==[]
assert m.phase_records('\n'.join(lines),c['path'],'plain')[1] and m.phase_records('\n'.join(lines[:2]),c['path'],'timed')[1]
with tempfile.TemporaryDirectory() as t:
 f=pathlib.Path(t)/'timer';f.write_text('wall_s=1.0\nuser_s=0.1\nsystem_s=0.2\nexit_status=0\n');assert m.parse_timer(f)['complete']
 f.write_text(f.read_text()+'wall_s=2\n');assert not m.parse_timer(f)['complete'] and 'wall_s=2' in m.parse_timer(f)['raw']
 f.write_text('wall_s=1\nuser_s=0\nsystem_s=0\nexit_status=0\nnoise\n');assert not m.parse_timer(f)['complete']
assert m.load_snapshot()['monotonic_ns']>0 and m.host_metadata()['cpu_count']
print('fake schedule 48 blocks/144 sessions, exact oracles, timeout cleanup and phase validation passed')
