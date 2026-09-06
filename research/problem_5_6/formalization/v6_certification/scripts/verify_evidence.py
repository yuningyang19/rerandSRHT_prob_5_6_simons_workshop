#!/usr/bin/env python3
"""Fail-closed kernel evidence verifier. Does not certify manuscript correspondence."""
import argparse,gzip,hashlib,json,pathlib,re,sys
ALLOWED={'propext','Classical.choice','Quot.sound'}
LEAN_DIR='research/problem_5_6/formalization/lean'
FROZEN_INVENTORIES={
 'inventory_named_results.json':('fe3324f58e323d6fd878f52e692dbe02abf38f1cf622f300f58a0c222f8285ef',12),
 'inventory_interfaces.json':('6ac8641a027876cc13de6d5ab50850c8add7370abd774671bcf847ebc2a6c0e0',50),
 'inventory_definitions.json':('4a4c69da398d7077d3e5b134501086fb48353265a32444b5c55d797308fda10e',34)}
FROZEN_SOURCE_MANIFESTS={
 'source_A_manifest.json':'d97b0348f21ca3955b7f2ffcd9603e0bf577a24da9814437c61fd63deed2489f',
 'baseline_B_manifest.json':'063c94e3b04781d0e154457358927a512202573ed01ac8c30b3a446283420f2e',
 'frozen_C_manifest.json':'2d0adbc6ac5e5a47e3cb2fe3e20ccc649e0d05371d99da46cddf16530bab0dfd'}
MANDATORY_COMMANDS={
 'expected_type_checks':['lake','env','lean','Problem56/PaperV6/ExpectedChecks.lean'],
 'semantic_witnesses':['lake','--no-cache','build','Problem56.ExtractionRegression','Problem56.GraphOperatorRegression','Problem56.GraphOperatorUnequalRegression','Problem56.PaperV6.SemanticWitnesses'],
 'structural_guards':['python3','../v6_certification/scripts/run_structural_guards.py','../semantic_regressions.py'],
 'negative_tests':['python3','../v6_certification/scripts/test_verifier.py'],
 'dependency_environment':['python3','../v6_certification/scripts/record_environment.py'],
 'unified_build':['lake','--no-cache','build','Problem56.PaperV6.Certification'],
 'kernel_replay':['lake','env','leanchecker','--fresh','-v','Problem56.PaperV6.Certification']}
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def read_text(p):
 return gzip.open(p,'rt').read() if p.suffix=='.gz' else p.read_text()
def log_sha(p):
 return hashlib.sha256(gzip.open(p,'rb').read()).hexdigest() if p.suffix=='.gz' else sha(p)
def locate_log(p):return p if p.is_file() else p.with_suffix(p.suffix+'.gz')
def require(ok,msg):
 if not ok: raise ValueError(msg)
def parse_log(path):
 targets={};nodes={};end=[]
 for line in read_text(path).splitlines():
  if line.startswith('CERT_TARGET|'):
   r=json.loads(line.split('|',1)[1]); require(r['name'] not in targets,'duplicated target'); targets[r['name']]=r
  elif line.startswith('CERT_NODE|'):
   r=json.loads(line.split('|',1)[1]); require(r['name'] not in nodes,'duplicated node'); nodes[r['name']]=r
  elif line.startswith('CERT_END|'): end.append(int(line.split('|')[1]))
 require(len(end)==1 and end[0]==len(nodes),'incomplete graph output')
 return targets,nodes

def validate_records(targets,nodes,expected,types=None):
 require(len(expected)==len(set(expected)),'duplicated inventory')
 require(set(targets)==set(expected),'missing or unexpected target')
 axiom_closures={}
 for name,r in targets.items():
  require(r['kind']=='theorem','wrong target declaration kind: '+name)
  require(set(r['axioms'])<=ALLOWED,'forbidden axiom record: '+name)
  if types is not None: require(r['type_repr']==types[name],'changed expected type: '+name)
  todo=[name];seen=set();axs=set()
  while todo:
   n=todo.pop()
   if n in seen:continue
   seen.add(n);require(n in nodes,'missing dependency '+n)
   node=nodes[n]
   if node['kind']=='axiom':axs.add(n)
   todo.extend(node['type_constants']+node['proof_constants'])
  require(axs<=ALLOWED,'forbidden transitive axiom: '+name+' '+str(axs-ALLOWED))
  # The structural visitor includes all constructors of reached inductives
  # and every recursor rule. This intentionally exceeds collectAxioms, which
  # follows only the target's used proof/type constants. Never drop an edge.
  require(set(r['axioms'])<=axs,'collectAxioms dependency missing from structural graph: '+name)
  axiom_closures[name]={'collectAxioms':sorted(r['axioms']),
   'conservative_structural_axioms':sorted(axs),'structural_excess':sorted(axs-set(r['axioms']))}
  require(nodes[name]['kind']==r['kind'] and nodes[name]['type_constants']==r['type_constants'] and nodes[name]['proof_constants']==r['proof_constants'],'target graph discrepancy')
 return {'target_count':len(targets),'graph_nodes':len(nodes),'status':'PASS','scope':'encoded declarations only',
  'axiom_closures':axiom_closures}

def local_source_closure(root):
 L=root/LEAN_DIR;seen=set();todo=[L/'Problem56/PaperV6/CombinedAudit.lean']
 while todo:
  p=todo.pop()
  if p in seen:continue
  require(p.is_file(),'missing local source '+str(p));seen.add(p)
  for mod in re.findall(r'^import\s+(\S+)',p.read_text(),re.M):
   q=L/(mod.replace('.','/')+'.lean')
   if q.is_file():todo.append(q)
   elif mod.startswith('Problem56'):require(False,'missing required local import '+mod)
 for name in ['lakefile.lean','lake-manifest.json','lean-toolchain']:seen.add(L/name)
 return {str(p.relative_to(root)) for p in seen}

def command_source_paths(root,cmd):
 L=root/LEAN_DIR;todo=[];scripts=[]
 for arg in cmd:
  if arg.endswith('.lean') or arg.endswith('.py'):
   p=pathlib.Path(arg);p=p.resolve() if p.is_absolute() else (L/p).resolve()
   (scripts if arg.endswith('.py') else todo).append(p)
  elif arg.startswith('Problem56.'):
   todo.append(L/(arg.replace('.','/')+'.lean'))
 seen=set()
 while todo:
  p=todo.pop()
  if p in seen:continue
  require(p.is_file(),'missing command source '+str(p));seen.add(p)
  for mod in re.findall(r'^import\s+(\S+)',p.read_text(),re.M):
   q=L/(mod.replace('.','/')+'.lean')
   if q.is_file():todo.append(q)
   elif mod.startswith('Problem56'):require(False,'missing command import '+mod)
 if scripts:seen.update(root/p for p in local_source_closure(root))
 scripts.append(root/'research/problem_5_6/formalization/v6_certification/scripts/run_logged.py')
 while scripts:
  p=scripts.pop()
  if p in seen:continue
  require(p.is_file(),'missing checker script '+str(p));seen.add(p)
  for mod in re.findall(r'^(?:from|import)\s+([A-Za-z_]\w*)',p.read_text(),re.M):
   q=p.parent/(mod+'.py')
   if q.is_file():scripts.append(q)
 for name in ['lakefile.lean','lake-manifest.json','lean-toolchain']:seen.add(L/name)
 return {str(p.relative_to(root)) for p in seen}

def validate_execution_sources(root,r,cmd):
 require(r['command']==cmd,'wrong compiler command')
 require(pathlib.Path(r['cwd']).resolve()==(root/LEAN_DIR).resolve(),'wrong compiler workspace')
 require(set(r['local_lean_sources'])==command_source_paths(root,cmd),'incomplete execution source binding')
 for src,h in r['local_lean_sources'].items():require(sha(root/src)==h,'stale execution source: '+src)

def strip_lean_noncode(s):
 out=[];i=0;depth=0;quoted=False
 while i<len(s):
  if depth:
   if s.startswith('/-',i):depth+=1;i+=2
   elif s.startswith('-/',i):depth-=1;i+=2
   else:i+=1
  elif quoted:
   if s[i]=='\\':i+=2
   elif s[i]=='"':quoted=False;i+=1
   else:i+=1
  elif s.startswith('/-',i):depth=1;i+=2;out.append(' ')
  elif s.startswith('--',i):
   k=s.find('\n',i);i=len(s) if k<0 else k;out.append(' ')
  elif s[i]=='"':quoted=True;i+=1;out.append(' ')
  else:out.append(s[i]);i+=1
 return ''.join(out)

def validate_source_text(s):
 code=strip_lean_noncode(s)
 require(not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide)\b|debug\.skipKernelTC|Lean\.trustCompiler|\b(addDecl|addAndCompile|addUnchecked|addDeclCore)\b',code),'forbidden local proof escape or hole')

def validate_local_source_policy(root):
 for p in local_source_closure(root):
  if p.endswith('.lean'):validate_source_text((root/p).read_text())

def validate_manifest(root,path,complete=False):
 d=json.loads(path.read_text())
 require(bool(d['files']),'empty manifest')
 require(len(d['files'])==len({r['path'] for r in d['files']}),'duplicate manifest paths')
 if complete:require({r['path'] for r in d['files']}==local_source_closure(root),'incomplete or excess source manifest')
 for r in d['files']:
  p=root/r['path'];require(p.is_file() and sha(p)==r['sha256'],'corrupted or stale manifest: '+r['path'])

def validate_definitions(log,expected):
 actual={}
 for line in read_text(log).splitlines():
  if line.startswith('CERT_DEFINITION|'):
   r=json.loads(line.split('|',1)[1]);require(r['name'] not in actual,'duplicate definition');actual[r['name']]=r
 require(actual==expected,'primitive definition/type mismatch')

def validate_frozen_sources(root):
 E=root/'research/problem_5_6/formalization/v6_certification'
 for name,h in FROZEN_SOURCE_MANIFESTS.items():require(sha(E/name)==h,'immutable source manifest changed: '+name)
 validate_manifest(root,E/'baseline_B_manifest.json')
 a=json.loads((E/'source_A_manifest.json').read_text())
 require(a['commit']=='35cc5f146fcddc88d8375cc974ff93585099e220','wrong original source commit')
 require(sha(E/'snapshots/solution.tex')==a['sha256']=='53efe688a3845cc6823d31504c04b471e83cee0371e327168e16742f87465c2c','original source hash mismatch')
 c=json.loads((E/'frozen_C_manifest.json').read_text())
 require(c['commit']=='4551d08f3732a3ca06c2f576794e1d75790e1972','wrong frozen manuscript commit')
 require({r['path'] for r in c['files']}=={'research/problem_5_6/paper/v6/main.tex','research/problem_5_6/paper/v6/figures/p7_contraction.tex'},'frozen manuscript closure mismatch')
 for r in c['files']:require(sha(E/'snapshots'/r['path'])==r['sha256'],'frozen manuscript byte mismatch')

def validate_crosswalk_rows(rows,ids,targets,source,definitions=None):
 require(len(rows)==len(ids) and {r['inventory_id'] for r in rows}==set(ids),'missing or duplicated paper crosswalk row')
 lines=source.splitlines(keepends=True)
 for r in rows:
  c=r['source_C'];a,b=c['line_start'],c['line_end']
  require(1<=a<=b<=len(lines),'invalid source range')
  raw=''.join(lines[a-1:b]).encode()
  require(hashlib.sha256(raw).hexdigest()==c['raw_context_sha256'],'changed crosswalk source context')
  covered=r.get('literal_source_kernel_covered',False) or r.get('required_consequence_kernel_covered',False) or r.get('formal_coverage_status')=='NAMED_STATEMENT_CORRESPONDENCE_CHECKED'
  if covered and r.get('inventory_category') in {'NAMED_RESULT','INTERFACE'}:
   require(bool(r.get('actual_lean_types')),'covered paper item lacks actual theorem binding: '+r['inventory_id'])
  for t in r.get('actual_lean_types',[]):
   name=t['declaration'];require(name in targets,'crosswalk theorem absent from actual audit: '+name)
   require(hashlib.sha256(targets[name]['type_repr'].encode()).hexdigest()==t['type_repr_sha256'],'crosswalk actual type changed: '+name)
  for d in r.get('actual_definition_records',[]):
   name=d['declaration'];require(definitions is not None and name in definitions,'crosswalk definition absent from actual audit: '+name)
   for field in ['type_repr','value_repr']:
    require(hashlib.sha256(definitions[name][field].encode()).hexdigest()==d[field+'_sha256'],'crosswalk actual definition changed: '+name)

def validate_paper_inventory(root,targets):
 E=root/'research/problem_5_6/formalization/v6_certification';ids=[]
 require(json.loads((E/'combined_actual_types.json').read_text())==targets,'actual type manifest differs from compiler log')
 require(json.loads((E/'combined_actual_definitions.json').read_text())==json.loads((E/'reviewed_definition_lock.json').read_text()),'actual definitions differ from reviewed compiler definitions')
 for name,(h,count) in FROZEN_INVENTORIES.items():
  p=E/name;require(sha(p)==h,'frozen paper inventory changed: '+name)
  entries=json.loads(p.read_text())['entries'];require(len(entries)==count,'paper denominator changed')
  # The crosswalk retains the exact IDs from the source-first inventories.
  ids.extend(e.get('id',e.get('label')) for e in entries)
 crosswalk=json.loads((E/'three_way_crosswalk.json').read_text())
 require(crosswalk['actual_type_manifest_sha256']==sha(E/'combined_actual_types.json'),'crosswalk actual-manifest binding stale')
 require(crosswalk['combined_source_manifest_sha256']==sha(E/'combined_source_manifest.json'),'crosswalk source-manifest binding stale')
 require(crosswalk['actual_definition_manifest_sha256']==sha(E/'combined_actual_definitions.json'),'crosswalk definition-manifest binding stale')
 lock=json.loads((E/'reviewed_correspondence_lock.json').read_text())
 required={'three_way_crosswalk.json','combined_actual_definitions.json','reviewed_type_lock.json','reviewed_definition_lock.json'}
 require(set(lock['files'])==required,'incomplete independent correspondence lock')
 for name,h in lock['files'].items():require(sha(E/name)==h,'changed independently reviewed correspondence: '+name)
 validate_crosswalk_rows(crosswalk['entries'],ids,targets,(E/'snapshots/research/problem_5_6/paper/v6/main.tex').read_text(),json.loads((E/'combined_actual_definitions.json').read_text()))
 return crosswalk['entries']

def paper_coverage_result(rows):
 unresolved=[]
 for r in rows:
  if r.get('classification')=='SOURCE_OR_CORRESPONDENCE_REPAIR_REQUIRED':unresolved.append(r['inventory_id'])
  elif r.get('inventory_category')=='INTERFACE' and r.get('literal_source_kernel_covered') is not True:unresolved.append(r['inventory_id'])
  elif r.get('inventory_category')=='NAMED_RESULT' and r.get('formal_coverage_status')!='NAMED_STATEMENT_CORRESPONDENCE_CHECKED':unresolved.append(r['inventory_id'])
 return {'full_manuscript_scope':'COVERED' if not unresolved else 'NOT_ESTABLISHED',
  'unresolved_source_items':sorted(set(unresolved))}

def require_full_paper_coverage(rows):
 result=paper_coverage_result(rows)
 require(not result['unresolved_source_items'],'full manuscript coverage not established: '+', '.join(result['unresolved_source_items']))

def validate_mandatory(root,path):
 checks=json.loads(path.read_text())
 require(set(checks)==set(MANDATORY_COMMANDS),'skipped mandatory checks')
 for name,p in checks.items():
  r=json.loads((root/p).read_text());require(r['returncode']==0,'failed mandatory check: '+name)
  validate_execution_sources(root,r,MANDATORY_COMMANDS[name])
  log=locate_log((root/p).parent.parent/r['stdout_stderr'])
  require(log.is_file() and log_sha(log)==r['log_sha256'],'stale mandatory log: '+name)

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--log',type=pathlib.Path,required=True);ap.add_argument('--inventory',type=pathlib.Path,required=True);ap.add_argument('--expected-types',type=pathlib.Path,required=True);ap.add_argument('--definition-lock',type=pathlib.Path,required=True);ap.add_argument('--mandatory-checks',type=pathlib.Path,required=True);ap.add_argument('--receipt',type=pathlib.Path,required=True);ap.add_argument('--root',type=pathlib.Path,required=True);ap.add_argument('--manifest',type=pathlib.Path,required=True);args=ap.parse_args()
 receipt=json.loads(args.receipt.read_text());require(receipt['returncode']==0,'compiler failed');require(receipt['log_sha256']==log_sha(args.log),'stale compiler log')
 validate_execution_sources(args.root,receipt,['lake','env','lean','Problem56/PaperV6/CombinedAudit.lean'])
 validate_manifest(args.root,args.manifest,complete=True)
 validate_frozen_sources(args.root)
 validate_local_source_policy(args.root)
 validate_definitions(args.log,json.loads(args.definition_lock.read_text()))
 validate_mandatory(args.root,args.mandatory_checks)
 t,n=parse_log(args.log);e=json.loads(args.inventory.read_text());types=json.loads(args.expected_types.read_text()) if args.expected_types else None
 result=validate_records(t,n,e,types)
 rows=validate_paper_inventory(args.root,t)
 result.update(paper_coverage_result(rows))
 print(json.dumps(result,indent=2))
if __name__=='__main__':
 try: main()
 except (ValueError,KeyError,OSError,json.JSONDecodeError) as e: print('FAIL: '+str(e),file=sys.stderr);sys.exit(1)
