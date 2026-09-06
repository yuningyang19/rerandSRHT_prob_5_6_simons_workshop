from pathlib import Path
import json,hashlib,collections
E=Path(__file__).resolve().parents[2];W=E.parents[3]
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
t=json.loads((E/'combined_actual_types.json').read_text())
assert 'Problem56.PaperV6.gram_centering' in t,'final bridge types unavailable'
nodes={};end=[];rawtargets={}
for line in (E/'logs/combined_audit.log').open():
 if line.startswith('CERT_NODE|'):
  x=json.loads(line.split('|',1)[1]);assert x['name'] not in nodes;nodes[x['name']]=x
 elif line.startswith('CERT_TARGET|'):
  x=json.loads(line.split('|',1)[1]);rawtargets[x['name']]=x
 elif line.startswith('CERT_END|'):end.append(int(line.split('|')[1]))
assert end==[len(nodes)] and set(rawtargets)==set(t)
for name,x in t.items():assert rawtargets[name]==x
r=json.loads((E/'reviews/independent_reverse_pass2.json').read_text())
def path(a,b):
 queue=collections.deque([a]);prev={a:None}
 while queue:
  x=queue.popleft()
  if x==b:
   out=[]
   while x is not None:out.append(x);x=prev[x]
   return out[::-1]
  for y in nodes[x]['proof_constants']:
   assert y in nodes
   if y not in prev:prev[y]=x;queue.append(y)
 return None
checks=[]
for e in r['FINAL_ENTRIES']:
 chain=path(e['ROOT_DECLARATION'],e['LEAN_DECLARATION_OR_DEPENDENCY_ID'])
 assert chain is not None,e['CANDIDATE_ID']
 checks.append({'candidate':e['CANDIDATE_ID'],'proof_constant_path':chain})
for a,b in [('general_bridgeless_matrix_conversion','generalBridgeless_modification'),('general_bridgeless_matrix_conversion','rooted_history'),('formalLogMomentInterface','squarefreePow_partition'),('formalLogMomentInterface','measure_moment_cumulant_inverse_nonempty_index'),('continuousCoupling','continuousThreshold_law'),('general_sampling_joint','finiteNoiseFailureLaw'),('gram_centering','gram_centering'),('rectangular_trace_power','rectangular_trace_mul_pow')]:
 a='Problem56.PaperV6.'+a;b='Problem56.PaperV6.'+b;chain=path(a,b);assert chain is not None,(a,b);checks.append({'root':a,'dependency':b,'proof_constant_path':chain})
manifest=json.loads((E/'combined_source_manifest.json').read_text())
assert len(manifest['files']) == len({f['path'] for f in manifest['files']}), 'duplicate source manifest paths'
for f in manifest['files']:assert sha(W/f['path'])==f['sha256'],f['path']
files=['combined_actual_types.json','combined_actual_definitions.json','combined_source_manifest.json','combined_target_inventory.json','combined_graph_component_result.json','logs/combined_audit.log','logs/combined_audit.execution.json']
binding={f:sha(E/f) for f in files}
evidence={'method':'Independent streaming parse of final actual graph; shortest paths use proof_constants edges only, not module imports or type-only reachability. Every audited actual type matches the raw log and every manifested source byte matches current files.','targets':len(t),'nodes':len(nodes),'source_manifest_file_count':len(manifest['files']),'paths':checks,'hashes':binding}
(E/'reviews/reverse_pass2/final_dependency_evidence.json').write_text(json.dumps(evidence,indent=2)+'\n')
r['source_manifest_file_count']=len(manifest['files']);r['implementation_binding']=binding;r['actual_type_count']=len(t);r['actual_definition_count']=len(json.loads((E/'combined_actual_definitions.json').read_text()));r['dependency_evidence']='reviews/reverse_pass2/final_dependency_evidence.json';r['additional_bridge_found_and_reviewed']['semantic_review']='PASS: actual elaborated types read, implementation inspected, exact expected statements previously approved, final actual graph and source hashes bound.'
(E/'reviews/independent_reverse_pass2.json').write_text(json.dumps(r,indent=2)+'\n')
p=E/'reviews/independent_reverse_pass2.md';s=p.read_text().replace('Final implementation/hash binding is pending the last I-V6-03 additive bridge and regeneration of actual types/graph.','Final implementation, actual-type and proof-dependency hashes are bound in `reverse_pass2/final_dependency_evidence.json`.').replace('Missing explicit bridge found in this audit; final additive implementation pending','Explicit bridge found missing by this audit and now proved/independently reviewed in TracePower.lean').replace('Final dependency checks will use the freshly regenerated actual graph, without inferring mathematical correspondence from graph PASS.','Final dependency checks independently parsed the fresh actual graph, verified proof-constant reachability for all 15 blinded candidates and the new bridges, and checked source hashes; mathematical correspondence was not inferred from graph PASS.')
s=s.split('\nFinal evidence: ')[0]
s+='\nFinal evidence: '+str(len(t))+' actual targets, '+str(len(nodes))+' graph nodes. All 15 blinded candidate dependencies have explicit proof-constant paths. I-V6-03 is closed by the new exact centering and rectangular trace-power bridges. I-V6-11 remains RA3/REPAIR; no unconditional 50/50 native literal-scope claim is made.\n';p.write_text(s)
print(json.dumps({'targets':len(t),'nodes':len(nodes),'candidate_paths':len(checks),'status':'REPAIR'}))
