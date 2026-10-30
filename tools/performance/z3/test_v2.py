import json,pathlib,tempfile,subprocess,sys,os
p=pathlib.Path(__file__).resolve().parent
with tempfile.TemporaryDirectory() as tmp:
 root=pathlib.Path(tmp); env={**os.environ,'FERRUM_Z3_REAL':str(p/'fake-z3.py'),'FERRUM_Z3_RECORD_DIR':str(root)}
 def run(kill):
  out=root/('killed.json' if kill else 'normal.json'); parent=root/'parent.py'
  parent.write_text('import subprocess,time,os,signal,sys\np=subprocess.Popen([sys.argv[1],"wait"],stdout=subprocess.PIPE)\np.stdout.readline()\n'+('os.kill(p.pid,signal.SIGKILL)\n' if kill else 'os.kill(p.pid,signal.SIGTERM)\n')+'p.wait()\n')
  r=subprocess.run([sys.executable,str(p/'run_session.py'),'--timeout','10','--output',str(out),'--',sys.executable,str(parent),str(p/'z3-wait4-wrapper')],env=env,capture_output=True,timeout=15);assert r.returncode==0,(r.stdout,r.stderr)
  a=subprocess.check_output([sys.executable,str(p/'assess.py'),str(root),str(out)],text=True);return json.loads(a),json.loads(out.read_text())
 # Keep each identity inventory distinct.
 normal,session=run(False);assert normal['complete'] and normal['processes'][0]['method']=='wrapper_wait4',(normal,session)
 for x in root.glob('z3-*'):
  import shutil;shutil.rmtree(x)
 killed,session=run(True);assert killed['complete'] and killed['processes'][0]['method']=='adopted_wait4',(killed,session)
 assert session['cleanup_pending']==[] and killed['processes'][0]['cpu']['user_s']>=0
 identity=killed['processes'][0]['identity']; first=next(root.glob('z3-*')); duplicate=root/'z3-duplicate';duplicate.mkdir()
 (duplicate/'start.json').write_text((first/'start.json').read_text());(duplicate/'identity.json').write_text(json.dumps(identity))
 a=json.loads(subprocess.check_output([sys.executable,str(p/'assess.py'),str(root),str(root/'killed.json')],text=True))
 assert not a['complete'] and all(x['method']=='incomplete_or_ambiguous' for x in a['processes'])
 (duplicate/'identity.json').unlink();a=json.loads(subprocess.check_output([sys.executable,str(p/'assess.py'),str(root),str(root/'killed.json')],text=True))
 assert not a['complete'] and any(x['identity'] is None and x['cpu'] is None for x in a['processes'])
 print('normal wrapper wait4 and killed-wrapper adopted wait4 identity match passed')
