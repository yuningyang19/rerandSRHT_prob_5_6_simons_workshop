#!/usr/bin/env python3
"""Run one command without pipelines; retain real return code and bound inputs."""
import datetime,hashlib,json,os,pathlib,subprocess,sys,time
base=pathlib.Path(__file__).resolve().parents[1]
name=sys.argv[1]; cmd=sys.argv[2:]
if not cmd: raise SystemExit('missing command')
log=base/'logs'/f'{name}.log'; receipt=base/'logs'/f'{name}.execution.json'
start=datetime.datetime.now(datetime.timezone.utc).isoformat(); tick=time.monotonic()
root=base.parents[3]
workspace=base.parent/'lean'
# Bind the exact command's local proof and checker-script closure.
from verify_evidence import command_source_paths
files={p:hashlib.sha256((root/p).read_bytes()).hexdigest()
       for p in sorted(command_source_paths(root,cmd))}
with log.open('wb') as out:
 p=subprocess.run(cmd,stdout=out,stderr=subprocess.STDOUT)
r={'command':cmd,'cwd':os.getcwd(),'start_utc':start,'end_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'elapsed_seconds':time.monotonic()-tick,'returncode':p.returncode,'stdout_stderr':str(log.relative_to(base)),'log_sha256':hashlib.sha256(log.read_bytes()).hexdigest(),'local_lean_sources':files,'receipt_kind':'local subprocess execution record; not authenticated external attestation'}
receipt.write_text(json.dumps(r,indent=2)+'\n'); print(json.dumps({k:r[k] for k in ['command','returncode','elapsed_seconds','stdout_stderr']})); sys.exit(p.returncode)
