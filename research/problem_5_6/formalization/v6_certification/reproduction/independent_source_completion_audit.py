"""Inspect the completed, separately executed c030 source-cold reproduction."""
import datetime, hashlib, importlib.util, json, os, pathlib, subprocess, sys, time
W=pathlib.Path('/Users/yuningyang/GitHub/rsvd_essential_v6_certification')
E=W/'research/problem_5_6/formalization/v6_certification'
C=E/'packages/cold-c0303801ca01-shallow'
CE=C/'research/problem_5_6/formalization/v6_certification'
CL=C/'research/problem_5_6/formalization/lean'
P=E/'reproduction'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
utc=lambda:datetime.datetime.now(datetime.timezone.utc).isoformat()
run=json.loads((P/'independent_source_cold_recovery_c0303801.json').read_text())
assert run['status']=='FAIL' and run['returncode']==1, 'preserved original cold suite failure changed'
original_failure=json.loads((CE/'logs/final_combined_audit.execution.json').read_text())
assert original_failure['returncode']==1
assert "AuditTools.olean' of module Problem56.PaperV6.AuditTools does not exist" in (CE/'logs/final_combined_audit.log').read_text()
assert run['initial_compiled_objects']==run['prebuild_compiled_objects']==0
assert run['compiled_cache_reused'] is False and not run['changed_proof_or_build_inputs']
assert len(run['source_fetches'])==9
assert sha(pathlib.Path(run['archive']))==run['archive_sha256']
assert sha(pathlib.Path(run['raw_log']))==run['raw_log_sha256']
manifest=json.loads((C/'EXPORT_MANIFEST.json').read_text())
changed=[p for p,h in manifest['files'].items() if not (C/p).is_file() or sha(C/p)!=h]
allowed=lambda p: p.startswith('research/problem_5_6/formalization/v6_certification/logs/') or p in {'research/problem_5_6/formalization/v6_certification/mandatory_checks.json','research/problem_5_6/formalization/v6_certification/dependency_environment.json'}
assert all(allowed(p) for p in changed), changed
sys.dont_write_bytecode=True
spec=importlib.util.spec_from_file_location('cold_verify_evidence',CE/'scripts/verify_evidence.py');v=importlib.util.module_from_spec(spec);spec.loader.exec_module(v)
v.validate_manifest(C,CE/'combined_source_manifest.json',complete=True)
v.validate_frozen_sources(C);v.validate_local_source_policy(C)
checks={name:str((CE/'logs'/('final_'+name+'.execution.json')).relative_to(C)) for name in v.MANDATORY_COMMANDS}
mandatory_path=P/'independent_recovered_mandatory_checks_c0303801.json'
mandatory_path.write_text(json.dumps(checks,indent=2)+'\n')
v.validate_mandatory(C,mandatory_path)
receipts={}
suite_start=next(x['started_utc'] for x in run['execution_commands'] if x['command'][-1].endswith('/scripts/run_suite.py'))
for name,p in checks.items():
 r=json.loads((C/p).read_text());assert pathlib.Path(r['cwd'])==CL
 assert datetime.datetime.fromisoformat(r['start_utc']) >= datetime.datetime.fromisoformat(suite_start)
 receipts[name]={k:r[k] for k in ['command','cwd','returncode','elapsed_seconds','log_sha256','start_utc','end_utc']}
build=json.loads((CE/'logs/recovery_audit_tools_build.execution.json').read_text())
assert build['returncode']==0 and build['command']==['lake','--no-cache','build','Problem56.PaperV6.AuditTools']
assert build['log_sha256']==sha(CE/'logs/recovery_audit_tools_build.log')
v.validate_execution_sources(C,build,build['command'])
log=CE/'logs/recovery_combined_audit.log'; receipt=json.loads((CE/'logs/recovery_combined_audit.execution.json').read_text())
assert receipt['returncode']==0 and receipt['log_sha256']==sha(log)
assert pathlib.Path(receipt['cwd'])==CL
assert datetime.datetime.fromisoformat(receipt['start_utc']) >= datetime.datetime.fromisoformat(suite_start)
v.validate_execution_sources(C,receipt,['lake','env','lean','Problem56/PaperV6/CombinedAudit.lean'])
targets,nodes=v.parse_log(log);definitions=json.loads((CE/'reviewed_definition_lock.json').read_text())
v.validate_definitions(log,definitions)
result=v.validate_records(targets,nodes,json.loads((CE/'combined_target_inventory.json').read_text()),json.loads((CE/'reviewed_type_lock.json').read_text()))
rows=v.validate_paper_inventory(C,targets);coverage=v.paper_coverage_result(rows)
assert len(targets)==359 and len(nodes)==63329 and len(definitions)==134
assert coverage=={'full_manuscript_scope':'NOT_ESTABLISHED','unresolved_source_items':['I-V6-11']}
verify_cmd=['python3',str(CE/'scripts/verify_evidence.py'),'--root',str(C),'--log',str(log),'--receipt',str(CE/'logs/recovery_combined_audit.execution.json'),'--inventory',str(CE/'combined_target_inventory.json'),'--manifest',str(CE/'combined_source_manifest.json'),'--expected-types',str(CE/'reviewed_type_lock.json'),'--definition-lock',str(CE/'reviewed_definition_lock.json'),'--mandatory-checks',str(mandatory_path)]
verify_env=os.environ.copy();verify_env['PYTHONDONTWRITEBYTECODE']='1'
verify_started=utc();verify_tick=time.monotonic();verified=subprocess.run(verify_cmd,cwd=CL,env=verify_env,capture_output=True,text=True)
verify_log=P/'independent_recovered_verifier_c0303801.log';verify_log.write_text(verified.stdout+verified.stderr)
assert verified.returncode==0, verified.stdout+verified.stderr
verify_receipt={'command':verify_cmd,'cwd':str(CL),'started_utc':verify_started,'ended_utc':utc(),'elapsed_seconds':time.monotonic()-verify_tick,'returncode':verified.returncode,'log_sha256':sha(verify_log)}
(P/'independent_recovered_verifier_c0303801.execution.json').write_text(json.dumps(verify_receipt,indent=2)+'\n')
reported=json.loads(verified.stdout)
assert reported['status']=='PASS' and reported['target_count']==359 and reported['graph_nodes']==63329
for k,x in coverage.items():assert reported[k]==x
cmd=['python3',str(CE/'scripts/check_full_paper_scope.py')]
env=os.environ.copy();env['PYTHONDONTWRITEBYTECODE']='1';started=utc();tick=time.monotonic()
r=subprocess.run(cmd,cwd=CL,env=env,capture_output=True,text=True)
full_log=P/'independent_cold_full_paper_scope_c0303801.log';full_log.write_text(r.stdout+r.stderr)
assert r.returncode==1 and 'FAIL: full manuscript coverage not established: I-V6-11' in r.stderr
assert json.loads(r.stdout)==coverage
full={'command':cmd,'cwd':str(CL),'started_utc':started,'ended_utc':utc(),'elapsed_seconds':time.monotonic()-tick,'returncode':r.returncode,'log':str(full_log.relative_to(E)),'log_sha256':sha(full_log),'script_sha256':sha(CE/'scripts/check_full_paper_scope.py'),'only_unresolved_item':'I-V6-11'}
(P/'independent_cold_full_paper_scope_c0303801.execution.json').write_text(json.dumps(full,indent=2)+'\n')
summary={'reviewer_context':'/root/baseline_audit','time_utc':utc(),'status':'RECOVERED_SOURCE_COLD_CHECKS_PASS_ORIGINAL_SUITE_FAIL_FULL_MANUSCRIPT_REPAIR','verification_commit':run['verification_commit'],'proof_source_freeze':'6c12db598e56103309f7e41144f84b75246fa96b','archive_sha256':run['archive_sha256'],'cold_directory':str(C),'recovery_scope':run['invocation_change']+' Original suite then failed because Certification does not build CombinedAudit-only AuditTools. Compiled the unchanged AuditTools source explicitly, re-ran only CombinedAudit, and verified the existing seven fresh mandatory receipts. This is not a PASS of the original unchanged run_suite command.','initial_compiled_objects':0,'prebuild_compiled_objects':0,'compiled_cache_reused':False,'dependency_sources':run['source_fetches'],'mandatory_checks':receipts,'original_run_suite_status':'FAIL','original_failed_audit_receipt_sha256':sha(CE/'logs/final_combined_audit.execution.json'),'additional_audit_tools_build':{k:build[k] for k in ['command','cwd','returncode','elapsed_seconds','log_sha256','start_utc','end_utc']},'recovered_verifier':verify_receipt,'counts':{'targets':len(targets),'primitive_definitions':len(definitions),'graph_nodes':len(nodes),'named_results':12,'source_interfaces':50,'literal_interfaces_covered':49,'frozen_definitions':34},'encoded_declaration_status':result['status'],'paper_coverage':coverage,'separate_full_paper_gate':full,'archive_generated_files_changed':changed,'immutable_archive_members_unchanged':True,'post_archive_metadata_distinction':{'cold_crosswalk_sha256':sha(CE/'three_way_crosswalk.json'),'current_root_crosswalk_sha256':sha(E/'three_way_crosswalk.json'),'clarification_record':'reviews/i11_implication_metadata_clarification.json','cold_archive_metadata_was_not_edited':True},'evidence_sha256':{p:sha(CE/p) for p in ['logs/recovery_combined_audit.log','logs/recovery_combined_audit.execution.json','logs/final_combined_audit.log','logs/final_combined_audit.execution.json','combined_source_manifest.json']},'runner_report_sha256':sha(P/'independent_source_cold_recovery_c0303801.json')}
(P/'independent_source_cold_completion_c0303801.json').write_text(json.dumps(summary,indent=2)+'\n')
print(json.dumps({k:summary[k] for k in ['status','counts','paper_coverage','immutable_archive_members_unchanged']},indent=2))
