#!/usr/bin/env python3
"""Rebuild extracted proofs and check current v6 scope in a disposable copy.

Historical evidence is never overwritten. Optional dependency reuse is explicit;
no compiled Problem56 artifact is copied. Installed Lean is trusted.
"""
import argparse
import datetime
import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import time
from verify_source_identity import ROOT, verify

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--dependency-cache', type=Path,
                    help='explicitly reuse an existing .lake/packages directory')
args = parser.parse_args()
manifest = verify()
out = ROOT / '.verification'
out.mkdir(exist_ok=True)
work = Path(tempfile.mkdtemp(prefix='run-', dir=out))
for name in manifest['files']:
    dest = work / name
    dest.parent.mkdir(parents=True, exist_ok=True)
    shutil.copyfile(ROOT / name, dest)
lean = work / 'research/problem_5_6/formalization/lean'
revision = work / 'research/problem_5_6/formalization/v6_certification/revisions/20260907_positive_dimensions'
if args.dependency_cache:
    cache = args.dependency_cache.resolve(strict=True)
    (lean / '.lake').mkdir(exist_ok=True)
    (lean / '.lake/packages').symlink_to(cache, target_is_directory=True)
env = dict(os.environ, MATHLIB_NO_CACHE_ON_UPDATE='1')
commands = [
    ['lake', '--no-cache', 'build', 'Problem56.PaperV6.AuditTools', 'Problem56.PaperV6.Certification'],
    ['python3', str(revision / 'run_logged.py'), 'current_graph_history_client',
     'lake', 'env', 'lean', 'Problem56/PaperV6/ExpectedGraphHistoryChecks.lean'],
    ['python3', str(revision / 'run_logged.py'), 'current_combined_audit',
     'lake', 'env', 'lean', 'Problem56/PaperV6/CombinedAudit.lean'],
    ['python3', str(revision / 'check_full_paper_scope.py')],
    ['python3', str(revision / 'test_revision_gate.py')],
    ['lake', 'env', 'leanchecker', '--fresh', '-v', 'Problem56.PaperV6.Certification'],
]
report = {'source_commit': manifest['verification_commit'],
          'paper_commit': 'f279b6fac180125dce81a82d824da971bb7ae715',
          'work_directory': str(work),
          'dependency_cache_reused': str(args.dependency_cache) if args.dependency_cache else None,
          'compiled_Problem56_cache_reused': False, 'commands': [], 'status': 'RUNNING'}
report_path = out / 'latest_result.json'
for i, cmd in enumerate(commands, 1):
    print(f'[{i}/{len(commands)}] {" ".join(cmd)}', flush=True)
    log = work / f'check-{i}.log'
    start = time.monotonic()
    with log.open('w') as stream:
        result = subprocess.run(cmd, cwd=lean, env=env, stdout=stream, stderr=subprocess.STDOUT)
    report['commands'].append({'command': cmd, 'returncode': result.returncode,
                              'elapsed_seconds': time.monotonic() - start, 'log': str(log)})
    report_path.write_text(json.dumps(report, indent=2) + '\n')
    if result.returncode:
        report['status'] = 'FAIL'
        report_path.write_text(json.dumps(report, indent=2) + '\n')
        print(log.read_text()[-6000:])
        raise SystemExit(f'FAIL: see {log}')
verify()
report['status'] = 'PASS'
report['completed_utc'] = datetime.datetime.now(datetime.timezone.utc).isoformat()
report_path.write_text(json.dumps(report, indent=2) + '\n')
print(f'PASS: fresh local proof build, current 12/50/34 scope, negative fixtures and kernel replay. Report: {report_path}')
