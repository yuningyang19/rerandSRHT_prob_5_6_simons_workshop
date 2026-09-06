"""Preserve completed 6bb96aa receipts verbatim and compress their actual logs.

This evidence-only helper does not build proofs or alter the tested archive.
It refuses incomplete runs and checks every copied log against its receipt.
"""
import gzip
import hashlib
import json
import pathlib

E = pathlib.Path(__file__).resolve().parents[1]
R = E / 'reproduction'
completion = R / 'independent_final_source_cold_completion_6bb96aa-final.json'
summary = json.loads(completion.read_text())
assert summary['documented_run_suite_returncode'] == 0
assert summary['documented_run_suite_invocations'] == 1
assert summary['additional_recovery_commands_after_suite_start'] is False
assert summary['compiled_cache_reused'] is False
assert summary['immutable_archive_members_unchanged'] is True
C = pathlib.Path(summary['cold_directory'])
CE = C / 'research/problem_5_6/formalization/v6_certification'
D = E / 'cold_evidence_final'
(D / 'logs').mkdir(parents=True, exist_ok=True)
sha = lambda b: hashlib.sha256(b).hexdigest()
manifest = {
    'status': 'CORRECTED_ARCHIVED_COMMAND_PASS',
    'source_directory': str(CE),
    'verification_commit': summary['verification_commit'],
    'archive_sha256': summary['archive_sha256'],
    'source_object_mirror_reused': summary['source_object_mirror_reused'],
    'compiled_cache_reused': False,
    'completion_report_sha256': sha(completion.read_bytes()),
    'checks': {},
    'files': {},
}
names = ['final_' + n for n in summary['mandatory_checks']]
names += ['final_audit_tool_build', 'final_combined_audit']
assert len(names) == len(set(names)) == 9
for name in names:
    receipt_path = pathlib.Path('logs') / (name + '.execution.json')
    receipt_bytes = (CE / receipt_path).read_bytes()
    receipt = json.loads(receipt_bytes)
    assert receipt['returncode'] == 0
    raw = (CE / 'logs' / (name + '.log')).read_bytes()
    assert sha(raw) == receipt['log_sha256']
    compressed = gzip.compress(raw, mtime=0)
    assert gzip.decompress(compressed) == raw
    log_path = pathlib.Path('logs') / (name + '.log.gz')
    (D / receipt_path).write_bytes(receipt_bytes)
    (D / log_path).write_bytes(compressed)
    manifest['checks'][name] = {
        'receipt': str(receipt_path), 'receipt_sha256': sha(receipt_bytes),
        'log_gzip': str(log_path), 'log_sha256': sha(raw),
        'gzip_sha256': sha(compressed), 'returncode': 0,
        'elapsed_seconds': receipt['elapsed_seconds'],
    }
for name in ['mandatory_checks.json', 'dependency_environment.json',
             'logs/final_verifier.log']:
    raw = (CE / name).read_bytes()
    (D / name).write_bytes(raw)
    manifest['files'][name] = sha(raw)
assert json.loads((D / 'logs/final_verifier.log').read_text())['status'] == 'PASS'
(D / 'capture_manifest.json').write_text(json.dumps(manifest, indent=2) + '\n')
print(json.dumps({'status': manifest['status'], 'receipts': len(names),
                  'destination': str(D)}, indent=2))
