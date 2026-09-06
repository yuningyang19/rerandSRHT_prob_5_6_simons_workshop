"""Independently inspect the final corrected-package source-cold execution."""
import datetime, hashlib, importlib.util, json, os, pathlib, subprocess, sys, time
assert len(sys.argv) in (2,3), 'usage: observer OUTPUT_SLUG [RUNNER_REPORT_BASENAME]'
slug=sys.argv[1];assert all(c.isalnum() or c in '-_' for c in slug)
W=pathlib.Path('/Users/yuningyang/GitHub/rsvd_essential_v6_certification')
E=W/'research/problem_5_6/formalization/v6_certification';P=E/'reproduction'
C=E/'packages'/('cold-'+slug);CE=C/'research/problem_5_6/formalization/v6_certification';CL=C/'research/problem_5_6/formalization/lean'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();utc=lambda:datetime.datetime.now(datetime.timezone.utc).isoformat()
report_name=sys.argv[2] if len(sys.argv)==3 else 'independent_final_source_cold_'+slug+'.json';assert pathlib.Path(report_name).name==report_name
runner_report=P/report_name;run=json.loads(runner_report.read_text())
assert run['status']=='PASS' and run['returncode']==0 and run['documented_run_suite_completed_without_recovery'] is True
assert run['initial_compiled_objects']==run['prebuild_compiled_objects']==0 and run['compiled_cache_reused'] is False
assert not run['changed_proof_or_build_inputs'] and len(run['source_fetches'])==9
assert sha(pathlib.Path(run['archive']))==run['archive_sha256'] and sha(pathlib.Path(run['raw_log']))==run['raw_log_sha256']
suites=[x for x in run['execution_commands'] if x['command'][-1].endswith('/scripts/run_suite.py')];assert len(suites)==1 and suites[0]['returncode']==0
suite_start=datetime.datetime.fromisoformat(suites[0]['started_utc'])
manifest=json.loads((C/'EXPORT_MANIFEST.json').read_text());assert manifest['verification_commit']==run['verification_commit']
changed=[p for p,h in manifest['files'].items() if not (C/p).is_file() or sha(C/p)!=h]
allowed=lambda p: p.startswith('research/problem_5_6/formalization/v6_certification/logs/') or p in {'research/problem_5_6/formalization/v6_certification/mandatory_checks.json','research/problem_5_6/formalization/v6_certification/dependency_environment.json'}
assert all(allowed(p) for p in changed),changed
sys.dont_write_bytecode=True
spec=importlib.util.spec_from_file_location('cold_final_verifier',CE/'scripts/verify_evidence.py');v=importlib.util.module_from_spec(spec);spec.loader.exec_module(v)
v.validate_manifest(C,CE/'combined_source_manifest.json',complete=True);v.validate_frozen_sources(C);v.validate_local_source_policy(C);v.validate_mandatory(C,CE/'mandatory_checks.json')
checks=json.loads((CE/'mandatory_checks.json').read_text());receipts={}
for name,p in checks.items():
 r=json.loads((C/p).read_text());assert pathlib.Path(r['cwd'])==CL and datetime.datetime.fromisoformat(r['start_utc'])>=suite_start
 receipts[name]={k:r[k] for k in ['command','cwd','returncode','elapsed_seconds','log_sha256','start_utc','end_utc']}
prerequisite=json.loads((CE/'logs/final_audit_tool_build.execution.json').read_text())
assert prerequisite['command']==['lake','--no-cache','build','Problem56.PaperV6.AuditTools'] and prerequisite['returncode']==0
assert pathlib.Path(prerequisite['cwd'])==CL and datetime.datetime.fromisoformat(prerequisite['start_utc'])>=suite_start
assert datetime.datetime.fromisoformat(prerequisite['end_utc'])<=datetime.datetime.fromisoformat(receipts['unified_build']['start_utc'])
assert prerequisite['log_sha256']==sha(CE/'logs/final_audit_tool_build.log');v.validate_execution_sources(C,prerequisite,prerequisite['command'])
log=CE/'logs/final_combined_audit.log';receipt=json.loads((CE/'logs/final_combined_audit.execution.json').read_text())
assert receipt['returncode']==0 and receipt['log_sha256']==sha(log) and pathlib.Path(receipt['cwd'])==CL
assert datetime.datetime.fromisoformat(receipt['start_utc'])>=datetime.datetime.fromisoformat(receipts['kernel_replay']['end_utc'])
v.validate_execution_sources(C,receipt,['lake','env','lean','Problem56/PaperV6/CombinedAudit.lean'])
targets,nodes=v.parse_log(log);definitions=json.loads((CE/'reviewed_definition_lock.json').read_text());v.validate_definitions(log,definitions)
result=v.validate_records(targets,nodes,json.loads((CE/'combined_target_inventory.json').read_text()),json.loads((CE/'reviewed_type_lock.json').read_text()))
rows=v.validate_paper_inventory(C,targets);coverage=v.paper_coverage_result(rows)
assert len(targets)==359 and len(nodes)==63329 and len(definitions)==134
assert coverage=={'full_manuscript_scope':'NOT_ESTABLISHED','unresolved_source_items':['I-V6-11']}
reported=json.loads((CE/'logs/final_verifier.log').read_text())
assert reported['status']=='PASS' and reported['target_count']==359 and reported['graph_nodes']==63329
for k,x in coverage.items():assert reported[k]==x
cmd=['python3',str(CE/'scripts/check_full_paper_scope.py')];env=os.environ.copy();env['PYTHONDONTWRITEBYTECODE']='1';start=utc();tick=time.monotonic()
r=subprocess.run(cmd,cwd=CL,env=env,capture_output=True,text=True)
full_log=P/('independent_final_full_paper_scope_'+slug+'.log');full_log.write_text(r.stdout+r.stderr)
assert r.returncode==1 and 'FAIL: full manuscript coverage not established: I-V6-11' in r.stderr and json.loads(r.stdout)==coverage
full={'command':cmd,'cwd':str(CL),'started_utc':start,'ended_utc':utc(),'elapsed_seconds':time.monotonic()-tick,'returncode':r.returncode,'log':str(full_log.relative_to(E)),'log_sha256':sha(full_log),'script_sha256':sha(CE/'scripts/check_full_paper_scope.py'),'only_unresolved_item':'I-V6-11'}
(P/('independent_final_full_paper_scope_'+slug+'.execution.json')).write_text(json.dumps(full,indent=2)+'\n')
summary={'reviewer_context':'/root/baseline_audit','time_utc':utc(),'status':'CORRECTED_PACKAGE_SOURCE_COLD_SUITE_PASS_FULL_MANUSCRIPT_REPAIR','verification_commit':run['verification_commit'],'proof_source_freeze':'6c12db598e56103309f7e41144f84b75246fa96b','archive_sha256':run['archive_sha256'],'archive_members':run['archive_members'],'cold_directory':str(C),'execution_method':run['execution_method'],'initial_compiled_objects':0,'prebuild_compiled_objects':0,'compiled_cache_reused':False,'source_object_mirror_reused':run.get('source_object_mirror_reused',False),'prior_source_acquisition_failure_report':run.get('prior_source_acquisition_failure_report'),'prior_source_acquisition_failure_sha256':run.get('prior_source_acquisition_failure_sha256'),'documented_run_suite_invocations':1,'documented_run_suite_returncode':0,'additional_recovery_commands_after_suite_start':False,'dependency_sources':run['source_fetches'],'audit_tool_prerequisite':{k:prerequisite[k] for k in ['command','cwd','returncode','elapsed_seconds','log_sha256','start_utc','end_utc']},'mandatory_checks':receipts,'counts':{'targets':len(targets),'primitive_definitions':len(definitions),'graph_nodes':len(nodes),'named_results':12,'source_interfaces':50,'literal_interfaces_covered':49,'frozen_definitions':34},'encoded_declaration_status':result['status'],'paper_coverage':coverage,'separate_full_paper_gate':full,'archive_generated_files_changed':changed,'immutable_archive_members_unchanged':True,'historical_c030_evidence':'Preserved original suite failure and recovered cold checks remain separate; this PASS belongs only to the new corrected package.','evidence_sha256':{p:sha(CE/p) for p in ['logs/final_combined_audit.log','logs/final_combined_audit.execution.json','logs/final_verifier.log','combined_source_manifest.json','mandatory_checks.json','three_way_crosswalk.json','reviewed_correspondence_lock.json']},'runner_report_sha256':sha(runner_report)}
(P/('independent_final_source_cold_completion_'+slug+'.json')).write_text(json.dumps(summary,indent=2)+'\n')
print(json.dumps({k:summary[k] for k in ['status','counts','paper_coverage','immutable_archive_members_unchanged','documented_run_suite_invocations','documented_run_suite_returncode']},indent=2))
