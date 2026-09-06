#!/usr/bin/env python3
"""Deterministic export from a committed certification checkout.

Only tracked, explicit baseline/addon/evidence files enter the archive. No
compiled object, cache, private user PDF, or unrelated repository path enters.
"""
import argparse,gzip,hashlib,io,json,pathlib,subprocess,tarfile
E=pathlib.Path(__file__).resolve().parents[1];R=E.parents[3]
ap=argparse.ArgumentParser();ap.add_argument('--output',type=pathlib.Path,required=True);args=ap.parse_args()
head=subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip()
tracked=subprocess.check_output(['git','ls-tree','-r','--name-only',head],cwd=R,text=True).splitlines()
base=json.loads((E/'baseline_B_manifest.json').read_text())
selected={r['path'] for r in base['files']}
for p in tracked:
 if p.startswith('research/problem_5_6/formalization/lean/Problem56/PaperV6/') or p.startswith('research/problem_5_6/formalization/v6_certification/'):
  if '/packages/' not in p:selected.add(p)
selected.add('research/problem_5_6/formalization/semantic_regressions.py')
if not selected<=set(tracked):raise SystemExit('required export files are uncommitted')
payload={}
for p in sorted(selected):
 if any(x in pathlib.PurePosixPath(p).parts for x in ['.lake','__pycache__']) or pathlib.PurePosixPath(p).suffix in {'.olean','.ilean','.pyc','.o','.a','.so','.dylib','.dll','.exe'}:
  raise SystemExit('compiled/cache artifact forbidden in export: '+p)
 b=subprocess.check_output(['git','show',head+':'+p],cwd=R)
 if (R/p).read_bytes()!=b:raise SystemExit('uncommitted export input: '+p)
 payload[p]=b
for row in base['files']:
 if hashlib.sha256(payload[row['path']]).hexdigest()!=row['sha256']:raise SystemExit('protected baseline byte mismatch')
manifest={'verification_commit':head,'files':{p:hashlib.sha256(b).hexdigest() for p,b in payload.items()},'compiled_objects_included':False}
payload['EXPORT_MANIFEST.json']=(json.dumps(manifest,indent=2)+'\n').encode()
payload['README.md']=payload['research/problem_5_6/formalization/v6_certification/README.md']
args.output.parent.mkdir(parents=True,exist_ok=True)
with args.output.open('wb') as f:
 with gzip.GzipFile(filename='',mode='wb',fileobj=f,mtime=0) as gz:
  with tarfile.open(fileobj=gz,mode='w') as tar:
   for p,b in sorted(payload.items()):
    info=tarfile.TarInfo(p);info.size=len(b);info.mode=0o644;info.mtime=0
    tar.addfile(info,io.BytesIO(b))
print(json.dumps({'path':str(args.output.resolve()),'verification_commit':head,'sha256':hashlib.sha256(args.output.read_bytes()).hexdigest(),'files':len(payload)},indent=2))
