#!/usr/bin/env python3
"""Reject isolated bad revision evidence; never edit a proof or actual record."""
import copy
import json
import pathlib
import shutil
import tempfile

import check_full_paper_scope as gate

R, E, v = gate.R, gate.E, gate.v
load = gate.load
targets = load(E / 'combined_actual_types.json')
definitions = load(E / 'combined_actual_definitions.json')


def verify(path):
    rows, ids, source = gate.validate_revision_metadata(path)
    v.validate_crosswalk_rows(rows, ids, targets, source, definitions)
    v.require_full_paper_coverage(rows)


def change_json(path, name, mutation):
    value = load(path / name)
    mutation(value)
    (path / name).write_text(json.dumps(value, indent=2) + '\n')
    # Refresh the local fixture's hash so semantic guards are also exercised.
    lock = load(path / 'reviewed_revision_lock.json')
    lock['files'][name] = v.sha(path / name)
    (path / 'reviewed_revision_lock.json').write_text(json.dumps(lock, indent=2) + '\n')


def missing_interface(path):
    change_json(path, 'reviewed_crosswalk.json',
                lambda d: d.update(entries=[x for x in d['entries'] if x['inventory_id'] != 'I-V6-11']))


def changed_type(path):
    def mutate(data):
        row = next(x for x in data['entries'] if x['inventory_id'] == 'I-V6-11')
        row['actual_lean_types'][0]['type_repr_sha256'] = '0' * 64
    change_json(path, 'reviewed_crosswalk.json', mutate)


def unresolved_interface(path):
    def mutate(data):
        row = next(x for x in data['entries'] if x['inventory_id'] == 'I-V6-11')
        row['literal_source_kernel_covered'] = False
    change_json(path, 'reviewed_crosswalk.json', mutate)


def failed_review(path):
    change_json(path, 'independent_report.json', lambda d: d.update(operation_status='REPAIR'))


def changed_source(path):
    source = path / 'snapshots' / gate.MAIN
    source.write_text(source.read_text().replace('positive integer', 'nonnegative integer', 1))


verify(R)
results = []
for name, mutation, diagnostic in [
    ('missing_interface', missing_interface, 'missing or duplicated paper crosswalk row'),
    ('changed_expected_type', changed_type, 'crosswalk actual type changed'),
    ('unresolved_literal_interface', unresolved_interface, 'full manuscript coverage not established'),
    ('failed_independent_review', failed_review, 'independent source-interface review did not pass'),
    ('changed_positive_dimension_source', changed_source, 'changed reviewed revision input'),
]:
    with tempfile.TemporaryDirectory(prefix='.revision-negative-', dir=R.parent) as directory:
        fixture = pathlib.Path(directory)
        lock = load(R / 'reviewed_revision_lock.json')
        for name_in_lock in lock['files']:
            if name_in_lock.startswith('../'):
                continue
            target = fixture / name_in_lock
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(R / name_in_lock, target)
        shutil.copyfile(R / 'reviewed_revision_lock.json', fixture / 'reviewed_revision_lock.json')
        mutation(fixture)
        try:
            verify(fixture)
        except ValueError as error:
            if diagnostic not in str(error):
                raise AssertionError('unexpected rejection for ' + name + ': ' + str(error))
            results.append({'fixture': name, 'status': 'REJECTED_AS_REQUIRED', 'diagnostic': str(error)})
        else:
            raise AssertionError('invalid fixture accepted: ' + name)
print(json.dumps({'status': 'PASS', 'valid_control': 'PASS', 'invalid_fixtures_rejected': len(results),
                  'results': results, 'actual_sources_or_records_changed': False}, indent=2))
