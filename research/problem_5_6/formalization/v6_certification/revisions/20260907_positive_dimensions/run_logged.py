#!/usr/bin/env python3
"""Log a current command without changing the parent snapshot's receipts."""
import datetime
import hashlib
import json
import pathlib
import subprocess
import sys
import time

R = pathlib.Path(__file__).resolve().parent
E = R.parents[1]
W = E.parents[3]
L = E.parent / 'lean'
sys.path.insert(0, str(E / 'scripts'))
from verify_evidence import command_source_paths

name, *command = sys.argv[1:]
if not command or not name.replace('_', '').isalnum():
    raise SystemExit('usage: run_logged.py NAME COMMAND ...')
(R / 'logs').mkdir(exist_ok=True)
log = R / 'logs' / (name + '.log')
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
sources = {p: sha(W / p) for p in sorted(command_source_paths(W, command))}
start = datetime.datetime.now(datetime.timezone.utc).isoformat()
tick = time.monotonic()
with log.open('wb') as output:
    result = subprocess.run(command, cwd=L, stdout=output, stderr=subprocess.STDOUT)
receipt = {
    'command': command, 'cwd': str(L), 'start_utc': start,
    'end_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
    'elapsed_seconds': time.monotonic() - tick, 'returncode': result.returncode,
    'stdout_stderr': str(log.relative_to(R)), 'log_sha256': sha(log),
    'local_lean_sources': sources,
    'receipt_kind': 'actual local subprocess execution; not an authenticated external attestation',
}
(R / 'logs' / (name + '.execution.json')).write_text(json.dumps(receipt, indent=2) + '\n')
print(json.dumps({k: receipt[k] for k in ['command', 'returncode', 'elapsed_seconds']}))
raise SystemExit(result.returncode)
