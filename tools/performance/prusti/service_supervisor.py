#!/usr/bin/env python3
"""Subreaper for one owned service tree. Writes cleanup audit on every catchable exit."""
import ctypes,json,os,pathlib,signal,subprocess,sys,time
P=pathlib.Path
out=P(sys.argv[1]); cmd=sys.argv[2:]; stopping=False
def stop(sig, frame):
 global stopping
 stopping=True
def born(pid):
 try:return P(f'/proc/{pid}/stat').read_text().rsplit(')',1)[1].split()[19]
 except (OSError,IndexError):return None
def discover(owned):
 for pid,start in list(owned.items()):
  if start is None or born(pid)!=start:continue
  for task in P(f'/proc/{pid}/task').glob('*'):
   try: children=(task/'children').read_text().split()
   except OSError:continue
   for c in children:
    c=int(c); b=born(c)
    if b is not None:owned.setdefault(c,b)
def kill_owned(owned,sig):
 for pid,start in reversed(list(owned.items())):
  if start is not None and born(pid)==start:
   try:os.kill(pid,sig)
   except ProcessLookupError:pass
if ctypes.CDLL(None,use_errno=True).prctl(36,1,0,0,0)!=0:raise OSError(ctypes.get_errno(),'subreaper')
for sig in (signal.SIGTERM,signal.SIGINT):signal.signal(sig,stop)
p=None;owned={};error=None
try:
 p=subprocess.Popen(cmd,start_new_session=True);owned[p.pid]=born(p.pid)
 while not stopping and p.poll() is None:
  discover(owned);time.sleep(.02)
except BaseException as e:error=repr(e)
finally:
 discover(owned)
 if p and p.poll() is None:
  try:os.killpg(p.pid,signal.SIGTERM)
  except ProcessLookupError:pass
  kill_owned(owned,signal.SIGTERM)
  deadline=time.monotonic()+2
  while p.poll() is None and time.monotonic()<deadline:discover(owned);time.sleep(.02)
  if p.poll() is None:
   try:os.killpg(p.pid,signal.SIGKILL)
   except ProcessLookupError:pass
 if p:kill_owned(owned,signal.SIGKILL);p.wait();owned.pop(p.pid,None)
 owned[os.getpid()]=born(os.getpid());deadline=time.monotonic()+2
 while time.monotonic()<deadline:
  discover(owned);desc={k:v for k,v in owned.items() if k!=os.getpid()};kill_owned(desc,signal.SIGKILL)
  for pid,b in desc.items():
   if born(pid)!=b:owned.pop(pid,None);continue
   try:r,_=os.waitpid(pid,os.WNOHANG)
   except ChildProcessError:continue
   if r:owned.pop(pid,None)
  if len(owned)==1:break
  time.sleep(.01)
 pending=[k for k in owned if k!=os.getpid()]
 out.write_text(json.dumps({'command':cmd,'leader_exit':p.returncode if p else None,'stopped':stopping,'cleanup_pending':pending,'error':error})+'\n')
sys.exit(0 if not error and not pending else 1)
