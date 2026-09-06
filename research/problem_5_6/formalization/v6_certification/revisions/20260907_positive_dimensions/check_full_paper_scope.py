#!/usr/bin/env python3
"""Fail-closed scope recheck for the single positive-dimension paper revision.

Parent source records and their old I11 REPAIR remain immutable. This command
rechecks current proof evidence, then applies the independently reviewed new
source binding. It inherits the explicitly identified prior cold build/replay;
it does not claim a new cold build or a new kernel replay.
"""
import collections
import hashlib
import json
import pathlib
import sys

R = pathlib.Path(__file__).resolve().parent
E = R.parents[1]
W = E.parents[3]
sys.path.insert(0, str(E / 'scripts'))
import verify_evidence as v

PAPER_COMMIT = 'f279b6fac180125dce81a82d824da971bb7ae715'
MAIN_SHA256 = '778731145bc9f537e561579303eb644388733d485b483c90f82e62243971e8cc'
MAIN = 'research/problem_5_6/paper/v6/main.tex'
BEFORE = ('allowing parallel edges and loops. Each vertex $u$ has a coordinate\n'
          'range $\\{1,\\ldots,N_u\\}$ from which its label $i_u$ is chosen,\n')
AFTER = ('allowing parallel edges and loops. Each vertex $u$ has a positive integer\n'
         'coordinate dimension $N_u$ and a range $\\{1,\\ldots,N_u\\}$ from which\n'
         'its label $i_u$ is chosen,\n')
INVENTORIES = {'inventory_named_results.json': 12,
               'inventory_interfaces.json': 50,
               'inventory_definitions.json': 34}
load = lambda path: json.loads(path.read_text())


def validate_revision_metadata(revision):
    lock = load(revision / 'reviewed_revision_lock.json')
    required = {'reviewed_crosswalk.json', 'frozen_C_manifest.json',
                'verification_packet.json', 'candidate_obligation.md',
                'independent_report.json', 'independent_report.md',
                *INVENTORIES,
                '../../combined_source_manifest.json',
                '../../combined_actual_types.json',
                '../../combined_actual_definitions.json',
                '../../reviewed_type_lock.json', '../../reviewed_definition_lock.json',
                '../../reviewed_correspondence_lock.json', '../../three_way_crosswalk.json',
                '../../scripts/verify_evidence.py',
                '../../reproduction/independent_final_source_cold_completion_6bb96aa-final.json',
                '../../cold_evidence_final/capture_manifest.json',
                'snapshots/' + MAIN,
                'snapshots/research/problem_5_6/paper/v6/figures/p7_contraction.tex'}
    v.require(required <= set(lock['files']), 'incomplete independent revision lock')
    for name, digest in lock['files'].items():
        v.require(v.sha(revision / name) == digest, 'changed reviewed revision input: ' + name)
    report = load(revision / 'independent_report.json')
    v.require(report['kernel_operation'] == 'SOURCE_INTERFACE_CHECK'
              and report['operation_status'] == 'PASS'
              and report['verifier_verdict'] is None
              and report['source_interface_status'] == 'VERIFIED',
              'independent source-interface review did not pass')
    v.require(report['generator_is_verifier'] is False
              and report['verifier_context'] != report['generator_context'],
              'missing independent review context')
    v.require(not report['open_obligations'] and not report['critical_errors'],
              'unresolved independent review obligations')
    v.require(report['exact_version'] == PAPER_COMMIT, 'review targets wrong manuscript')
    source = load(revision / 'frozen_C_manifest.json')
    parent = load(E / 'frozen_C_manifest.json')
    v.require(source['commit'] == PAPER_COMMIT
              and source['parent_commit'] == parent['commit'], 'wrong source lineage')
    v.require({f['path'] for f in source['files']} == {f['path'] for f in parent['files']},
              'changed manuscript input closure')
    for f in source['files']:
        v.require(v.sha(revision / 'snapshots' / f['path']) == f['sha256'],
                  'changed revised manuscript input')
        if f['path'] != MAIN:
            v.require((revision / 'snapshots' / f['path']).read_bytes()
                      == (E / 'snapshots' / f['path']).read_bytes(), 'figure changed')
    v.require(v.sha(revision / 'snapshots' / MAIN) == MAIN_SHA256, 'wrong new main bytes')
    old = (E / 'snapshots' / MAIN).read_text()
    new = (revision / 'snapshots' / MAIN).read_text()
    v.require(old.count(BEFORE) == 1 and old.replace(BEFORE, AFTER) == new,
              'paper delta exceeds the one authorized clarification')
    ids = []
    lines = new.splitlines(keepends=True)
    for name, count in INVENTORIES.items():
        data = load(revision / name)
        prior = load(E / name)
        entries = data['entries']
        v.require(data['frozen_v6_commit'] == PAPER_COMMIT
                  and data['main_sha256'] == MAIN_SHA256, 'wrong inventory source')
        v.require(len(entries) == count
                  and [x['id'] for x in entries] == [x['id'] for x in prior['entries']],
                  'missing, duplicated or changed paper inventory IDs')
        for item, previous in zip(entries, prior['entries']):
            raw = ''.join(lines[item['line_start'] - 1:item['line_end']])
            v.require(raw == item['exact_context_tex']
                      and hashlib.sha256(raw.encode()).hexdigest() == item['raw_context_sha256'],
                      'bad revised inventory source anchor')
            v.require(previous['exact_context_tex'].replace(BEFORE, AFTER) == raw,
                      'inventory reanchoring lost source content')
        ids.extend(x['id'] for x in entries)
    crosswalk = load(revision / 'reviewed_crosswalk.json')
    v.require(crosswalk['frozen_C_commit'] == PAPER_COMMIT, 'crosswalk source is stale')
    return crosswalk['entries'], ids, new


def validate_current_receipt(name, command):
    receipt = load(R / 'logs' / (name + '.execution.json'))
    log = v.locate_log(R / 'logs' / (name + '.log'))
    v.require(receipt['returncode'] == 0 and receipt['log_sha256'] == v.log_sha(log),
              'failed or stale current execution: ' + name)
    v.validate_execution_sources(W, receipt, command)
    return log, receipt


def validate_inherited_cold_receipts():
    """Bind historical working directories honestly, then compare exact sources.

    The original receipt is neither rewritten nor presented as an execution in
    W. The old machine's unpack directory need not still exist to inspect the
    preserved receipts and byte-identical current source tree.
    """
    directory = E / 'cold_evidence_final'
    completion_path = E / 'reproduction/independent_final_source_cold_completion_6bb96aa-final.json'
    cold = load(completion_path)
    capture = load(directory / 'capture_manifest.json')
    v.require(capture['completion_report_sha256'] == v.sha(completion_path),
              'cold receipt capture is bound to a different completion report')
    checks = load(R / 'inherited_mandatory_checks.json')
    v.require(set(checks) == set(v.MANDATORY_COMMANDS), 'skipped inherited mandatory check')
    expected_cwd = str(pathlib.Path(cold['cold_directory']) / v.LEAN_DIR)
    for name, command in v.MANDATORY_COMMANDS.items():
        record = capture['checks']['final_' + name]
        path = directory / record['receipt']
        v.require((W / checks[name]).resolve() == path.resolve(),
                  'wrong inherited receipt selection: ' + name)
        v.require(v.sha(path) == record['receipt_sha256'], 'changed captured cold receipt')
        receipt = load(path)
        v.require(receipt['command'] == command and receipt['returncode'] == 0,
                  'failed or wrong inherited command: ' + name)
        v.require(receipt['cwd'] == expected_cwd, 'wrong historical compiler workspace')
        reviewed = cold['mandatory_checks'][name]
        for field in ['command', 'cwd', 'returncode', 'elapsed_seconds',
                      'log_sha256', 'start_utc', 'end_utc']:
            v.require(receipt[field] == reviewed[field], 'cold completion/receipt mismatch')
        log = directory / record['log_gzip']
        v.require(v.sha(log) == record['gzip_sha256']
                  and v.log_sha(log) == receipt['log_sha256'] == record['log_sha256'],
                  'changed captured cold log')
        v.require(set(receipt['local_lean_sources']) == v.command_source_paths(W, command),
                  'incomplete inherited source closure: ' + name)
        for source, digest in receipt['local_lean_sources'].items():
            v.require(v.sha(W / source) == digest, 'inherited proof/checker bytes changed: ' + source)
    v.require(cold['documented_run_suite_returncode'] == 0
              and cold['documented_run_suite_invocations'] == 1
              and cold['immutable_archive_members_unchanged'] is True,
              'inherited exact-proof cold suite did not pass')
    v.require(cold['evidence_sha256']['combined_source_manifest.json']
              == v.sha(E / 'combined_source_manifest.json'), 'cold proof source binding changed')
    return cold


def main():
    rows, ids, source = validate_revision_metadata(R)
    v.validate_frozen_sources(W)
    v.validate_manifest(W, E / 'combined_source_manifest.json', complete=True)
    v.validate_local_source_policy(W)
    log, receipt = validate_current_receipt(
        'current_combined_audit', ['lake', 'env', 'lean', 'Problem56/PaperV6/CombinedAudit.lean'])
    validate_current_receipt('current_graph_history_client',
                            ['lake', 'env', 'lean', 'Problem56/PaperV6/ExpectedGraphHistoryChecks.lean'])
    targets, nodes = v.parse_log(log)
    v.validate_definitions(log, load(E / 'reviewed_definition_lock.json'))
    result = v.validate_records(targets, nodes, load(E / 'combined_target_inventory.json'),
                                load(E / 'reviewed_type_lock.json'))
    prior = v.validate_paper_inventory(W, targets)
    v.require(v.paper_coverage_result(prior)['unresolved_source_items'] == ['I-V6-11'],
              'parent repair history changed')
    v.validate_crosswalk_rows(rows, ids, targets, source, load(E / 'combined_actual_definitions.json'))
    old_rows = {x['inventory_id']: x for x in prior}
    for row in rows:
        previous = old_rows[row['inventory_id']]
        for field in ['actual_lean_types', 'actual_definition_records']:
            v.require(row.get(field) == previous.get(field),
                      'revision changed proof/definition bindings: ' + row['inventory_id'])
    cold = validate_inherited_cold_receipts()
    v.require_full_paper_coverage(rows)
    return {
        'status': 'PASS', 'frozen_paper_commit': PAPER_COMMIT,
        'main_sha256': MAIN_SHA256, **v.paper_coverage_result(rows),
        'named_results': '12/12', 'literal_interfaces': '50/50', 'definitions': '34/34',
        'classification_counts': dict(collections.Counter(x['classification'] for x in rows)),
        'proof_targets': result['target_count'], 'dependency_nodes': result['graph_nodes'],
        'primitive_definitions': len(load(E / 'reviewed_definition_lock.json')),
        'Lean_proof_sources_changed': False,
        'current_graph_history_client': 'PASS', 'current_combined_audit': 'PASS',
        'current_audit_elapsed_seconds': receipt['elapsed_seconds'],
        'cold_build_and_replay': 'Inherited after exact source/hash/receipt revalidation; not rerun',
        'inherited_tested_Lean_source_commit': cold['verification_commit'],
        'source_Git_objects_reused_in_inherited_run': cold['source_object_mirror_reused'],
        'compiled_cache_reused_in_inherited_run': cold['compiled_cache_reused'],
        'author_comprehension_or_publication_approval': 'NOT_ASSERTED',
        'workflow_metadata': 'Original lifecycle/authenticated-receipt limitations remain separate',
    }


if __name__ == '__main__':
    try:
        print(json.dumps(main(), indent=2))
    except (OSError, KeyError, ValueError, TypeError) as exc:
        print('FAIL: ' + str(exc), file=sys.stderr)
        raise SystemExit(1)
