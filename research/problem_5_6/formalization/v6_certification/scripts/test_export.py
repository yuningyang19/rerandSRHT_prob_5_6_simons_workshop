#!/usr/bin/env python3
"""Verify a committed source archive, then really run its documented suite.

The destination must not exist. No files are copied from another build tree.
This can serve as the independent all-dependencies cold reproduction when
invoked and reviewed by a context independent of the proof authors.
"""
import argparse,datetime,hashlib,json,os,pathlib,subprocess,sys,tarfile,time

def sha(path):
 return hashlib.sha256(path.read_bytes()).hexdigest()

def main():
 ap=argparse.ArgumentParser()
 ap.add_argument('--archive',required=True,type=pathlib.Path)
 ap.add_argument('--destination',required=True,type=pathlib.Path)
 ap.add_argument('--report',required=True,type=pathlib.Path)
 args=ap.parse_args()
 archive=args.archive.resolve();dest=args.destination.resolve();report=args.report.resolve()
 if dest.exists():raise ValueError('fresh unpack destination already exists')
 with tarfile.open(archive,'r:gz') as tar:
  members=tar.getmembers();names=[m.name for m in members]
  if len(names)!=len(set(names)):raise ValueError('duplicate archive member')
  for m in members:
   p=pathlib.PurePosixPath(m.name)
   if not m.isfile() or p.is_absolute() or '..' in p.parts or '.lake' in p.parts or '__pycache__' in p.parts:
    raise ValueError('unsafe or cached archive member: '+m.name)
   if p.suffix in {'.olean','.ilean','.pyc','.o','.a','.so','.dylib','.dll','.exe'}:
    raise ValueError('compiled archive member: '+m.name)
  dest.mkdir(parents=True)
  for m in members:
   p=dest/m.name;p.parent.mkdir(parents=True,exist_ok=True)
   p.write_bytes(tar.extractfile(m).read())
 manifest=json.loads((dest/'EXPORT_MANIFEST.json').read_text())
 if set(names)!=set(manifest['files'])|{'README.md','EXPORT_MANIFEST.json'}:
  raise ValueError('archive membership differs from source manifest')
 for name,h in manifest['files'].items():
  if sha(dest/name)!=h:raise ValueError('source archive hash mismatch: '+name)
 if manifest['compiled_objects_included'] is not False:raise ValueError('archive cache declaration invalid')
 entry='research/problem_5_6/formalization/v6_certification'
 if (dest/'README.md').read_bytes()!=(dest/entry/'README.md').read_bytes():
  raise ValueError('top-level README differs from documented entrypoint')
 cmd=['python3',entry+'/scripts/run_suite.py']
 record={'verification_commit':manifest['verification_commit'],'archive':str(archive),
  'archive_sha256':sha(archive),'destination':str(dest),'initial_compiled_objects':0,
  'source_members_checked':len(manifest['files']),'command':cmd,'cwd':str(dest),
  'start_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
  'scope':'fresh unpack; all project and dependency sources; installed standard Lean toolchain trusted',
  'cache_policy':'No .lake in archive; no copied objects; MATHLIB_NO_CACHE_ON_UPDATE=1 and lake --no-cache build',
  'status':'RUNNING'}
 report.parent.mkdir(parents=True,exist_ok=True);report.write_text(json.dumps(record,indent=2)+'\n')
 env=os.environ.copy();env['MATHLIB_NO_CACHE_ON_UPDATE']='1'
 start=time.monotonic();log=report.with_suffix('.log')
 try:
  with log.open('wb') as out:result=subprocess.run(cmd,cwd=dest,env=env,stdout=out,stderr=subprocess.STDOUT)
 except OSError as exc:
  record.update(status='FAIL',returncode=1,error=str(exc),elapsed_seconds=time.monotonic()-start)
  report.write_text(json.dumps(record,indent=2)+'\n');raise
 record.update(returncode=result.returncode,elapsed_seconds=time.monotonic()-start,
  end_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),stdout_stderr=str(log),
  log_sha256=sha(log),status='PASS' if result.returncode==0 else 'FAIL')
 # Reproduction writes evidence, but must preserve every proof/build input.
 changed=[]
 for name,h in manifest['files'].items():
  if name.startswith('research/problem_5_6/formalization/lean/') and (not (dest/name).is_file() or sha(dest/name)!=h):changed.append(name)
 record['changed_proof_or_build_inputs']=changed
 if changed:record['status']='FAIL';record['returncode']=1
 report.write_text(json.dumps(record,indent=2)+'\n');print(json.dumps(record,indent=2))
 return record['returncode']

if __name__=='__main__':
 try:sys.exit(main())
 except (OSError,ValueError,KeyError,tarfile.TarError) as exc:
  print('FAIL: '+str(exc),file=sys.stderr);sys.exit(1)
