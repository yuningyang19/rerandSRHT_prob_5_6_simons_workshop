#!/usr/bin/env python3
"""Execute the checked target, independent expected types, witnesses and replay.

Run from any directory. This never downloads compiled caches. Lake may fetch
the exact source dependencies from the protected package manifest.
"""
import json,os,pathlib,subprocess,sys
from verify_evidence import MANDATORY_COMMANDS
E=pathlib.Path(__file__).resolve().parents[1];L=E.parent/'lean';R=E.parents[3]
E.joinpath('logs').mkdir(exist_ok=True)
# This pinned Mathlib hook otherwise downloads compiled cache on lake update.
os.environ['MATHLIB_NO_CACHE_ON_UPDATE']='1'
def run(name,cmd):
 subprocess.run([sys.executable,str(E/'scripts/run_logged.py'),name]+cmd,cwd=L,check=True)
# CombinedAudit imports this logger outside the mathematical Certification root.
# A fresh package has no pre-existing AuditTools.olean.
run('final_audit_tool_build',['lake','--no-cache','build','Problem56.PaperV6.AuditTools'])
checks={}
for name in ['unified_build','dependency_environment','expected_type_checks','semantic_witnesses','structural_guards','negative_tests','kernel_replay']:
 run('final_'+name,MANDATORY_COMMANDS[name])
 checks[name]=str((E/'logs'/('final_'+name+'.execution.json')).relative_to(R))
run('final_combined_audit',['lake','env','lean','Problem56/PaperV6/CombinedAudit.lean'])
(E/'mandatory_checks.json').write_text(json.dumps(checks,indent=2)+'\n')
cmd=[sys.executable,str(E/'scripts/verify_evidence.py'),'--root',str(R),
 '--log',str(E/'logs/final_combined_audit.log'),'--receipt',str(E/'logs/final_combined_audit.execution.json'),
 '--inventory',str(E/'combined_target_inventory.json'),'--manifest',str(E/'combined_source_manifest.json'),
 '--expected-types',str(E/'reviewed_type_lock.json'),'--definition-lock',str(E/'reviewed_definition_lock.json'),
 '--mandatory-checks',str(E/'mandatory_checks.json')]
result=subprocess.run(cmd,cwd=L,capture_output=True,text=True)
(E/'logs/final_verifier.log').write_text(result.stdout+result.stderr)
print(result.stdout+result.stderr,end='');sys.exit(result.returncode)
