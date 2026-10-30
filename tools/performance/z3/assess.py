"""Join wrapper identities to mutually exclusive wrapper or adopted wait4 records."""
import json,pathlib,sys,collections
p=pathlib.Path(sys.argv[1]);session=json.loads(pathlib.Path(sys.argv[2]).read_text());adopted=session['adopted_wait4'];used=set();items=[]
def ident(d):
 try:
  v=json.loads((d/'identity.json').read_text());return (v['child_pid'],str(v['child_start_ticks']))
 except (OSError,ValueError,KeyError):return None
identities=collections.Counter(ident(d) for d in p.glob('z3-*'))
for d in sorted(p.glob('z3-*')):
 def load(name):
  try:return json.loads((d/name).read_text())
  except (OSError,ValueError):return None
 start=load('start.json');identity=load('identity.json');end=load('end.json');matches=[]
 if identity:matches=[(i,a) for i,a in enumerate(adopted) if str(a.get('pid'))==str(identity.get('child_pid')) and str(a.get('start_ticks'))==str(identity.get('child_start_ticks')) and isinstance(a.get('raw_wait_status'),int) and all(isinstance(a.get(k),(int,float)) and a[k]>=0 for k in ('user_s','system_s'))]
 valid_end=bool(end and end.get('wrapper_error_errno')==0 and isinstance(end.get('raw_wait_status'),int) and identity and end.get('wrapper_pid')==identity.get('wrapper_pid') and end.get('child_pid')==identity.get('child_pid') and all(isinstance(end.get(k),int) and end[k]>=0 for k in ('user_us','system_us')))
 unique=bool(start and identity and isinstance(identity.get('child_pid'),int) and isinstance(identity.get('wrapper_pid'),int) and identity.get('wrapper_pid')==start.get('wrapper_pid') and str(identity.get('child_start_ticks','')).isdigit() and identities[(identity['child_pid'],str(identity['child_start_ticks']))]==1)
 if valid_end and not matches and unique:method='wrapper_wait4';cpu={'user_s':end['user_us']/1e6,'system_s':end['system_us']/1e6}
 elif len(matches)==1 and not valid_end and unique and matches[0][0] not in used:method='adopted_wait4';used.add(matches[0][0]);cpu={'user_s':matches[0][1]['user_s'],'system_s':matches[0][1]['system_s']}
 else:method='incomplete_or_ambiguous';cpu=None
 items.append({'directory':str(d),'kind':start.get('kind') if start else None,'identity':identity,'method':method,'cpu':cpu,'matching_adopted':len(matches)})
print(json.dumps({'processes':items,'adopted_total':adopted,'complete':bool(items) and all(x['cpu'] is not None for x in items) and not session['cleanup_pending'],'unmatched_adopted_indices':[i for i in range(len(adopted)) if i not in used]},indent=2))
