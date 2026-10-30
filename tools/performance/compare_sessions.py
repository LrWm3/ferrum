#!/usr/bin/env python3
"""Compare uninstrumented/instrumented envelopes and validate separate timing records."""
import argparse,json,pathlib,sys
p=argparse.ArgumentParser();p.add_argument('--plain',action='store_true',help='compare an untimed driver and require no PERF records');p.add_argument('baseline',type=pathlib.Path);p.add_argument('instrumented',type=pathlib.Path);a=p.parse_args();b=json.loads(a.baseline.read_text());t=json.loads(a.instrumented.read_text());faults=[]
for k in ('outcome','exit_code','protocol_errors','cleanup_pending','records'):
 if b.get(k)!=t.get(k):faults.append('different '+k)
perfs=[]
for line in t.get('raw_output','').splitlines():
 if line.startswith('@@PERF@@'):
  try:
   x=json.loads(line[len('@@PERF@@'):]);assert x['clock']=='monotonic' and x['unit']=='ns' and int(x['elapsed_ns'])>=0;assert isinstance(x['phase'],str);perfs.append(x)
  except Exception as e:faults.append('invalid PERF: '+str(e))
requests=[x for x in perfs if x.get('phase')=='request_total'];records=[x for x in t.get('records',[]) if isinstance(x.get('case'),str)]
if not a.plain and t.get('outcome')=='completed' and [x.get('request') for x in requests]!=list(range(len(records))):faults.append('request timing count/order differs from completed records')
if not a.plain and t.get('outcome')=='completed' and [x.get('case') for x in requests]!=[x['case'] for x in records]:faults.append('request timing case order differs')
if not a.plain and not perfs:faults.append('no timing records')
if a.plain and perfs:faults.append('unexpected timing records in plain driver')
print(json.dumps({'equal':not faults,'faults':faults,'timing_records':len(perfs),'timings':perfs},indent=2));sys.exit(bool(faults))
