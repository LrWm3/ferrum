#!/usr/bin/env python3
"""In-memory analysis tests; no primary files or verifiers are read."""
import importlib.util,pathlib
p=pathlib.Path(__file__).resolve().with_name('analyze.py');spec=importlib.util.spec_from_file_location('direct_analysis',p);m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
def row(block,request,wall):
 return {'block_id':block,'request':request,'classification':'valid','mode':'service','command_wall_s':wall,'child_user_s':wall/2,'child_system_s':0.1,'service_startup_to_socket_ns':100000000,'phase_ns':{k:[100] for k in m.PHASES}}
raw=[row(8,0,1.0),row(8,1,2.0),row(8,2,4.0),{'block_id':8,'classification':'invalid_service_cleanup'},row(9,0,1.0),row(9,1,2.0),row(9,2,4.0)]
effective,bad=m.apply_block_invalidations(raw)
assert bad=={8}
assert all(r['classification']=='invalid_service_cleanup' and r['original_classification']=='valid' for r in effective if r['block_id']==8)
assert all(r['classification']=='valid' for r in effective if r['block_id']==9)
usable={(r['block_id'],r['request']):r for r in effective if r['classification']=='valid'}
assert m.collapse_requests([usable.get((8,1)),usable.get((8,2))]) is None
later=m.collapse_requests([usable.get((9,1)),usable.get((9,2))])
assert later['wall_s']==3.0 and later['client_user_s']==1.5 and later['service_startup_s']==0.1
assert m.collapse_requests([usable.get((9,1)),None]) is None
print('synthetic block exclusion and later-request collapse passed')
