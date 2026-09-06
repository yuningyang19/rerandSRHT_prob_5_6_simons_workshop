#!/usr/bin/env python3
"""Require exact dependency revisions and unmodified tracked source files."""
import json,pathlib,subprocess,sys
E=pathlib.Path(__file__).resolve().parents[1];L=E.parent/'lean'
def out(cmd,cwd=L):return subprocess.check_output(cmd,cwd=cwd,text=True).strip()
manifest=json.loads((L/'lake-manifest.json').read_text());deps=[]
for p in manifest['packages']:
 d=L/manifest['packagesDir']/p['name'];actual=out(['git','rev-parse','HEAD'],d)
 if actual!=p['rev']:raise SystemExit('dependency revision mismatch: '+p['name'])
 dirty=out(['git','status','--porcelain','--untracked-files=no'],d)
 if dirty:raise SystemExit('modified dependency tracked source: '+p['name']+'\n'+dirty)
 deps.append({'name':p['name'],'revision':actual,'source_url':p['url'],'tracked_source_clean':True})
toolchain=(L/'lean-toolchain').read_text().strip()
if toolchain!='leanprover/lean4:v4.33.0':raise SystemExit('wrong Lean toolchain')
lean=out(['lean','--version']);lake=out(['lake','--version'])
if '4.33.0' not in lean:raise SystemExit('running Lean differs from pinned version')
result={'lean_toolchain':toolchain,'lean_version':lean,'lake_version':lake,'python_version':sys.version,'dependencies':deps,'toolchain_trust_boundary':'Standard installed Lean distribution; not rebuilt from source by this task.'}
(E/'dependency_environment.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
