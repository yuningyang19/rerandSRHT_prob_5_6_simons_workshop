#!/usr/bin/env python3
"""Isolated invalid data, never imported Lean axioms."""
import copy,hashlib,json,pathlib,tempfile
from verify_evidence import validate_records,validate_manifest,parse_log,validate_definitions,validate_mandatory,validate_execution_sources,validate_source_text,validate_crosswalk_rows,require_full_paper_coverage,MANDATORY_COMMANDS,LEAN_DIR
T={'good':{'kind':'theorem','axioms':[],'type_repr':'expected Prop','type_constants':[],'proof_constants':[]}}
N={'good':{'kind':'theorem','type_constants':[],'proof_constants':[]}}
results={}
def rejected(name,fn):
 try: fn()
 except (ValueError,KeyError): results[name]='REJECTED';return
 raise AssertionError('accepted invalid fixture: '+name)
rejected('missing_target',lambda:validate_records({},N,['good']))
bad=copy.deepcopy(T);bad['good']['axioms']=['unapproved']
rejected('forbidden_axiom_record',lambda:validate_records(bad,N,['good']))
rejected('changed_expected_type',lambda:validate_records(T,N,['good'],{'good':'different Prop'}))
with tempfile.TemporaryDirectory() as d:
 p=pathlib.Path(d);(p/'source').write_text('changed');(p/'manifest.json').write_text(json.dumps({'files':[{'path':'source','sha256':'0'*64}]}))
 rejected('corrupted_manifest',lambda:validate_manifest(p,p/'manifest.json'))
rejected('duplicate_inventory',lambda:validate_records(T,N,['good','good']))
bad=copy.deepcopy(T);bad['good']['kind']='definition'
rejected('wrong_kind',lambda:validate_records(bad,N,['good']))
bad=copy.deepcopy(N);bad['good']['proof_constants']=['missing']
rejected('missing_dependency',lambda:validate_records(T,bad,['good']))
bad=copy.deepcopy(N);bad['good']['proof_constants']=['outside.bad'];bad['outside.bad']={'kind':'axiom','type_constants':[],'proof_constants':[]}
rejected('outside_namespace_axiom',lambda:validate_records(T,bad,['good']))
with tempfile.TemporaryDirectory() as d:
 p=pathlib.Path(d);log=p/'log';log.write_text('CERT_END|4\n')
 rejected('incomplete_graph_output',lambda:parse_log(log))
 log.write_text('CERT_END|0\nCERT_END|0\n')
 rejected('duplicated_graph_end',lambda:parse_log(log))
 log.write_text('CERT_DEFINITION|'+json.dumps({'name':'x','value_repr':'modified'})+'\n')
 rejected('changed_primitive_definition',lambda:validate_definitions(log,{'x':{'name':'x','value_repr':'approved'}}))
 checks=p/'checks.json';checks.write_text('{}')
 rejected('skipped_mandatory_checks',lambda:validate_mandatory(p,checks))
 fake=p/'fake.json';fake.write_text(json.dumps({'returncode':0,'command':['true'],'cwd':str(p/LEAN_DIR)}))
 checks.write_text(json.dumps({k:'fake.json' for k in MANDATORY_COMMANDS}))
 rejected('mandatory_command_substitution',lambda:validate_mandatory(p,checks))
 L=p/LEAN_DIR;(L/'Problem56/PaperV6').mkdir(parents=True)
 (L/'Problem56/PaperV6/CombinedAudit.lean').write_text('import Problem56.Required\n')
 (L/'Problem56/Required.lean').write_text('')
 manifest=p/'manifest.json';manifest.write_text(json.dumps({'files':[{'path':LEAN_DIR+'/Problem56/Required.lean','sha256':'0'*64}]}))
 rejected('omitted_manifest_member',lambda:validate_manifest(p,manifest,complete=True))
root=pathlib.Path(__file__).resolve().parents[1].parents[3]
cmd=MANDATORY_COMMANDS['expected_type_checks']
rejected('deleted_execution_source_bindings',lambda:validate_execution_sources(root,{'command':cmd,'cwd':str(root/LEAN_DIR),'local_lean_sources':{}},cmd))
rejected('anonymous_example_hole',lambda:validate_source_text('example : False := by sorry'))
rejected('unchecked_insertion',lambda:validate_source_text('run_elab addDeclCore malicious'))
validate_source_text('/- nested /- sorry -/ admit -/ theorem good : True := by trivial -- unsafe\n')
rejected('deleted_paper_interface',lambda:validate_crosswalk_rows([{'inventory_id':'a'}],['a','b'],{},''))
rejected('duplicated_paper_interface',lambda:validate_crosswalk_rows([{'inventory_id':'a'},{'inventory_id':'a'}],['a','b'],{},''))
row={'inventory_id':'a','inventory_category':'INTERFACE','literal_source_kernel_covered':True,'source_C':{'line_start':1,'line_end':1,'raw_context_sha256':hashlib.sha256(b'x\n').hexdigest()},'actual_lean_types':[]}
rejected('deleted_covered_type_binding',lambda:validate_crosswalk_rows([row],['a'],{},'x\n'))
row['literal_source_kernel_covered']=False
row['actual_definition_records']=[{'declaration':'d','type_repr_sha256':'0'*64,'value_repr_sha256':'0'*64}]
rejected('changed_crosswalk_definition',lambda:validate_crosswalk_rows([row],['a'],{},'x\n',{'d':{'type_repr':'Prop','value_repr':'True'}}))
extraT=copy.deepcopy(T);extraN=copy.deepcopy(N)
extraT['good']['type_constants']=['structure'];extraN['good']['type_constants']=['structure']
extraN['structure']={'kind':'inductive','type_constants':[],'proof_constants':['structure.mk']}
extraN['structure.mk']={'kind':'constructor','type_constants':['propext'],'proof_constants':[]}
extraN['propext']={'kind':'axiom','type_constants':[],'proof_constants':[]}
assert validate_records(extraT,extraN,['good'])['axiom_closures']['good']['structural_excess']==['propext']
absent=copy.deepcopy(T);absent['good']['axioms']=['propext']
rejected('collectAxioms_missing_from_graph',lambda:validate_records(absent,N,['good']))
extraN['structure.mk']['type_constants'].append('forbidden')
extraN['forbidden']={'kind':'axiom','type_constants':[],'proof_constants':[]}
rejected('forbidden_constructor_excess',lambda:validate_records(extraT,extraN,['good']))
rejected('source_repair_blocks_full_paper',lambda:require_full_paper_coverage([{'inventory_id':'I','classification':'SOURCE_OR_CORRESPONDENCE_REPAIR_REQUIRED'}]))
rejected('unproved_literal_interface_blocks_full_paper',lambda:require_full_paper_coverage([{'inventory_id':'I','inventory_category':'INTERFACE','literal_source_kernel_covered':False}]))
print(json.dumps(results,indent=2))
