import importlib.util,pathlib
p=pathlib.Path(__file__).resolve().parent;s=importlib.util.spec_from_file_location('audit',p/'analyze.py');m=importlib.util.module_from_spec(s);s.loader.exec_module(m)
case={'path':'a','expect':{'outcome':'failure','errors':[{'id':'x','position':'p'}]}};session={'outcome':'completed','exit_code':0,'cleanup_pending':[],'protocol_errors':[],'records':[{'case':'a','outcome':'failure','errors':[{'id':'x','position':'p'}]}]};assert m.check_session(session,case);session['records'][0]['errors'][0]['position']='q';assert not m.check_session(session,case)
table={('on',0):{'eligible':True,'metrics':{'x':4}},('off',0):{'eligible':True,'metrics':{'x':2}},('on',1):{'eligible':False,'metrics':{'x':4}},('off',1):{'eligible':True,'metrics':{'x':2}},('on',2):{'eligible':True,'metrics':{'x':None}},('off',2):{'eligible':True,'metrics':{'x':2}}};x=m.ratio_pairs(table,'on','off','x');assert x['values']==[2] and x['excluded_repetitions']==[1,2]
assert not m.option_audit({'commands':[{'name':'check-sat','index':0}]})['issues']==[]
print('synthetic proof/span, option/budget, invalid and missing-stat ratio exclusions passed')
