import importlib.util,pathlib,tempfile,os,subprocess,sys,time,json,signal
p=pathlib.Path(__file__).parent;s=importlib.util.spec_from_file_location('bench',p/'run.py');m=importlib.util.module_from_spec(s);s.loader.exec_module(m)
rows=[{'block_id':3,'request':0,'classification':'valid'},{'block_id':3,'request':1,'classification':'censored_timeout'},{'block_id':3,'classification':'invalid_service_cleanup'},{'block_id':4,'classification':'valid'}]
effective,bad=m.effective_records(rows);assert bad=={3} and [r['classification'] for r in effective]==['invalid_service_cleanup','invalid_service_cleanup','valid'] and effective[1]['original_classification']=='censored_timeout'
case={'expect':{'exit':101,'errors':['expected failure'],'location':'line42'}}
assert m.status(101,False,'error: expected failure\nline42',case)=='valid'
assert m.status(0,False,'error: expected failure\nline42',case)=='unexpected_result'
blocks=m.make_schedule([{'name':'a'},{'name':'b'}],[1],[False],['fresh','service'],1,42);assert len(blocks)==4 and all(sorted(b['order'])==['jvm','native'] for b in blocks) and blocks==m.make_schedule([{'name':'a'},{'name':'b'}],[1],[False],['fresh','service'],1,42)
m.assign_endpoints(blocks,60861);endpoints=[p for b in blocks for p in b['endpoints'].values()];assert len(endpoints)==4 and len(set(endpoints))==4
try:m.assign_endpoints(blocks,65534);raise AssertionError('port overflow accepted')
except ValueError:pass
assert m.dependency_events('    Checking foo v0.1.0 (/tmp/foo)\n', 'foo')['valid']
assert not m.dependency_events('    Checking foo v0.1.0 (/tmp/foo)\n    Checking dep v0.1.0 (/tmp/dep)\n', 'foo')['valid']
assert not m.dependency_events('warning: Checking dep v0.1.0\n', 'foo')['valid']
with tempfile.TemporaryDirectory() as d:
 d=pathlib.Path(d);env=os.environ.copy()
 timer=d/'test-time';valid='wall_s=1.20\nuser_s=0.01\nsystem_s=0.00\nmax_rss_kib=42\nexit_status=101\n';timer.write_text(valid);assert m.parse_timer(timer)['complete']
 for malformed in (valid+'wall_s=1\n',valid+'extra=1\n',valid.replace('wall_s=1.20','wall_s=NaN'),valid.replace('user_s=0.01','user_s=-1'),valid.replace('max_rss_kib=42','max_rss_kib=4.2'),valid.replace('exit_status=101','exit_status=inf')):
  timer.write_text(malformed);assert not m.parse_timer(timer)['complete'],malformed
 result=m.run_process([sys.executable,'-c','import sys;sys.exit(101)'],d,env,5,d/'test.log')
 assert result[0]==101 and not result[1] and result[5] and result[6],result
 assert m.run_process([sys.executable,'-c','import time;time.sleep(3)'],d,env,.1,d/'timeout.log')[1]
 a=d/'service.json'; child=subprocess.Popen([sys.executable,str(p/'service_supervisor.py'),str(a),sys.executable,'-c','import subprocess,time;subprocess.Popen(["sleep","30"]);time.sleep(30)'])
 time.sleep(.3);child.terminate();child.wait(timeout=8);record=json.loads(a.read_text());assert child.returncode==0 and record['cleanup_pending']==[] and record['stopped'],record
 scratchroot=d/'scratch';scratchroot.mkdir();scratch=scratchroot/'copy';scratch.mkdir();(scratch/'verify').mkdir()
 m.ensure_scratch_cache_marker(scratch,scratchroot)
 assert (scratch/'verify'/'CACHEDIR.TAG').read_bytes()==m.CARGO_CACHE_SIGNATURE
 m.ensure_scratch_cache_marker(scratch,scratchroot)
 marker=scratch/'verify'/'CACHEDIR.TAG';marker.unlink();outside=d/'outside';outside.write_text('unchanged');marker.symlink_to(outside)
 try:m.ensure_scratch_cache_marker(scratch,scratchroot);raise AssertionError('symlink marker accepted')
 except ValueError:pass
 assert outside.read_text()=='unchanged'
 marker.unlink();(scratch/'verify').rmdir();(scratch/'verify').symlink_to(d,target_is_directory=True)
 try:m.ensure_scratch_cache_marker(scratch,scratchroot);raise AssertionError('symlink directory accepted')
 except ValueError:pass
 f=d/'artifact';f.write_text('one');h=m.sha(f);m.checked(f,h);f.write_text('two')
 try:m.checked(f,h);raise AssertionError('mutation accepted')
 except ValueError:pass
print('fake timing, expected 101, timeout, service descendant cleanup mutation and scratch marker safety checks passed')
