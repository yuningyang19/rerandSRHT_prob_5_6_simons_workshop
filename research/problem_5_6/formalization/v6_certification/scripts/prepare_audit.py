#!/usr/bin/env python3
"""Build the additive audit root and a complete local source manifest.

The declaration discovery here determines the mechanical audit roots, never the
paper denominators. Those remain the independently reviewed source inventories.
"""
import hashlib,json,pathlib,re
from verify_evidence import local_source_closure
E=pathlib.Path(__file__).resolve().parents[1]
L=E.parent/'lean'; R=E.parents[3]; P=L/'Problem56/PaperV6'
excluded={'AuditTools','BaselineAudit','CombinedAudit','Certification'}
modules=sorted(p for p in P.glob('*.lean') if p.stem not in excluded)
regressions=[L/'Problem56'/f'{n}.lean' for n in
 ['ExtractionRegression','GraphOperatorRegression','GraphOperatorUnequalRegression']]
targets=json.loads((E/'baseline_target_inventory.json').read_text())
targets+=json.loads((E/'additional_baseline_interface_targets.json').read_text())
definitions=[]
for p in modules+regressions:
    src=p.read_text(); namespaces=[]
    # These sources use explicit namespace/end lines; ignore private helpers.
    for line in src.splitlines():
        line=line.lstrip()
        line=re.sub(r'^(?:@\[[^\]]*\]\s*)+','',line)
        if m:=re.match(r'^namespace (\S+)',line): namespaces.append(m[1])
        elif re.match(r'^end(?: |$)',line) and namespaces: namespaces.pop()
        elif m:=re.match(r"^(?:theorem|lemma) ([\w'.]+)",line):
            targets.append('.'.join(namespaces+[m[1]]))
        elif m:=re.match(r"^(?:noncomputable )?def ([\w'.]+)",line):
            if 'Expected' in p.stem: definitions.append('.'.join(namespaces+[m[1]]))
assert len(targets)==len(set(targets))
definitions=sorted(set(definitions+json.loads((E/'additional_baseline_definition_targets.json').read_text())))
imports=['Problem56.Statements']+[str(p.relative_to(L)).removesuffix('.lean').replace('/','.') for p in modules+regressions]
(P/'Certification.lean').write_text('\n'.join('import '+m for m in imports)+'\n')
(P/'CombinedAudit.lean').write_text('import Problem56.PaperV6.Certification\nimport Problem56.PaperV6.AuditTools\n\n'+
 '\n'.join('#cert_target_name '+json.dumps(n,ensure_ascii=False) for n in targets)+'\n'+
 '\n'.join('#cert_definition_name '+json.dumps(n,ensure_ascii=False) for n in definitions)+'\n'+
 '#cert_closure_names '+' '.join(json.dumps(n,ensure_ascii=False) for n in targets+definitions)+'\n')
(E/'combined_target_inventory.json').write_text(json.dumps(targets,indent=2)+'\n')
(E/'primitive_definition_inventory.json').write_text(json.dumps(definitions,indent=2)+'\n')
files=[]; imports_map={}
for p in sorted(R/rel for rel in local_source_closure(R)):
    if p.suffix!='.lean' or p==L/'lakefile.lean':continue
    rel=str(p.relative_to(R))
    files.append({'path':rel,'sha256':hashlib.sha256(p.read_bytes()).hexdigest()})
    imports_map[rel]=re.findall(r'^import\s+(\S+)',p.read_text(),re.M)
for name in ['lakefile.lean','lakefile.toml','lake-manifest.json','lean-toolchain']:
    p=L/name
    if p.is_file():files.append({'path':str(p.relative_to(R)),'sha256':hashlib.sha256(p.read_bytes()).hexdigest()})
(E/'combined_source_manifest.json').write_text(json.dumps({'files':files,'module_imports':imports_map},indent=2)+'\n')
print(json.dumps({'targets':len(targets),'primitive_definitions':len(definitions),'source_files':len(files)}))
