#!/usr/bin/env python3
import hashlib,json,pathlib,subprocess
ROOT=pathlib.Path(__file__).resolve().parents[5]
OUT=ROOT/'research/problem_5_6/formalization/v6_certification'
def git(*args): return subprocess.check_output(['git',*args],cwd=ROOT)
def sha(b): return hashlib.sha256(b).hexdigest()
def dump(n,x): (OUT/n).write_text(json.dumps(x,indent=2)+'\n')
A='35cc5f146fcddc88d8375cc974ff93585099e220'; B='40f96935796e484ab4c03865bc93b47827f99980'; C='4551d08f3732a3ca06c2f576794e1d75790e1972'
ap='research/problem_5_6/LaTeX/solution.tex'; cp='research/problem_5_6/paper/v6/main.tex'; lp='research/problem_5_6/formalization/lean/'
a=git('show',A+':'+ap); assert sha(a)=='53efe688a3845cc6823d31504c04b471e83cee0371e327168e16742f87465c2c'
(OUT/'snapshots/solution.tex').write_bytes(a)
assert git('rev-parse',C+':'+cp).decode().strip()=='29cedead0714e560d6b1ca8f789a2183c2c1e241'
bfiles=git('ls-tree','-r','--name-only',B,lp).decode().splitlines()
brows=[]
for p in bfiles:
 b=git('show',B+':'+p); assert (ROOT/p).read_bytes()==b,p
 brows.append({'path':p,'sha256':sha(b),'git_blob':git('rev-parse',B+':'+p).decode().strip()})
cpaths=git('ls-tree','-r','--name-only',C,'research/problem_5_6/paper/v6').decode().splitlines()
crows=[]
for p in cpaths:
 b=git('show',C+':'+p); assert (OUT/'snapshots'/p).read_bytes()==b
 crows.append({'path':p,'sha256':sha(b),'git_blob':git('rev-parse',C+':'+p).decode().strip()})
dump('source_A_manifest.json',{'commit':A,'path':ap,'sha256':sha(a)})
dump('baseline_B_manifest.json',{'commit':B,'closure_record_commit':'394f2468311996c10b4d1f1ad33429ef1eb975e6','files':brows})
dump('frozen_C_manifest.json',{'commit':C,'files':crows,'input_closure_review':'main.tex inputs figures/p7_contraction.tex; inline TikZ and bibliography reside in main.tex'})
sk=[]
for p in [pathlib.Path('/Users/yuningyang/.codex/skills/my-academic-research-flow-6-0/SKILL.md'),pathlib.Path('/Users/yuningyang/.codex/skills/my-academic-lean-formalizer/SKILL.md'),pathlib.Path('/Users/yuningyang/.codex/skills/.system/openai-docs/SKILL.md')]: sk.append({'path':str(p),'sha256':sha(p.read_bytes())})
dump('certification_packet.json',{'LEAN_OPERATION':'CERTIFICATION','status':'PREPARATION_PENDING_INDEPENDENT_POST_TEX','actual_input_head':git('rev-parse','HEAD').decode().strip(),'branch':git('branch','--show-current').decode().strip(),'A':'source_A_manifest.json','B':'baseline_B_manifest.json','C':'frozen_C_manifest.json','source_manifests':{n:sha((OUT/n).read_bytes()) for n in ['source_A_manifest.json','baseline_B_manifest.json','frozen_C_manifest.json']},'skills':sk,'allowed_axioms':['propext','Classical.choice','Quot.sound'],'baseline_targets':53,'v6_denominators':'pending independent source extraction; cannot shrink once frozen','author_comprehension_or_publication_approval':'NOT_ASSERTED','historical_operation_B':'PROBE','astra_official_review':{'url':'https://developers.openai.com/api/docs/guides/latest-model?model=gpt-6-astra','adjustment':'No mathematical scope change. Reuse authorization, persist, delegate independent review, proportional development checks plus all mandatory final checks.'},'protected_bytes_verified':True})
print('Pinned A/B/C verified;',len(brows),'B files;',len(crows),'C files')
