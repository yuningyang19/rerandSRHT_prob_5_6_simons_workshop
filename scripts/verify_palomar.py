#!/usr/bin/env python3
"""Static extraction checks and optional local declaration/axiom preflight."""
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess
import tomllib
from verify_source_identity import ROOT, verify

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--static-only', action='store_true')
args = parser.parse_args()
verify()
L = ROOT / 'research/problem_5_6/formalization/lean'
manifest = json.loads((ROOT / 'palomar/extraction_manifest.json').read_text())
challenge = (ROOT / 'Challenge.lean').read_text()
config = json.loads((ROOT / 'comparator.json').read_text())
expected = ['Problem56.main_universal_ose', 'Problem56.PaperV6.fixed_frame_squared_norm_success']
assert config['theorem_names'] == expected
assert config['challenge_module'] == 'Challenge' and config['solution_module'] == 'Solution'
assert config['definition_names'] == []
assert set(config['permitted_axioms']) == {'propext', 'Quot.sound', 'Classical.choice'}
assert re.findall(r'^import (.+)$', challenge, re.M) == ['Mathlib']
assert len(re.findall(r'\bsorry\b', challenge)) == 2
assert len(challenge.encode()) <= 100 * 1024 and len(challenge.splitlines()) <= 1000
assert not re.search(r'\b(?:axiom|unsafe|native_decide|run_tac|implemented_by)\b', challenge)
assert hashlib.sha256(challenge.encode()).hexdigest() == manifest['challenge_sha256']
assert re.findall(r'^import (.+)$', (ROOT / 'Solution.lean').read_text(), re.M) == ['Problem56.PaperV6.FixedFrame']
assert (ROOT / 'LICENSE').read_bytes() == (ROOT / 'palomar/drafts/Apache-2.0.txt').read_bytes()
for name in ['lean-toolchain', 'lake-manifest.json']:
    assert (ROOT / name).read_bytes() == (L / name).read_bytes()
lake = tomllib.loads((ROOT / 'lakefile.toml').read_text())
assert lake['lean_lib'][0] == {'name': 'Problem56', 'srcDir': 'research/problem_5_6/formalization/lean'}

def definition(text, name):
    return re.search(rf'^(?:noncomputable )?(?:def|abbrev) {re.escape(name)}\b[\s\S]*?(?=\n(?:\n|(?:noncomputable )?(?:def|abbrev) )|\Z)', text, re.M).group().rstrip()
original = (L / 'Problem56/Definitions.lean').read_text()
for name, digest in manifest['definitions'].items():
    a, b = definition(original, name), definition(challenge, name)
    assert a == b and hashlib.sha256(a.encode()).hexdigest() == digest, name
for full, path in zip(expected, [L / 'Problem56/Statements.lean', L / 'Problem56/PaperV6/FixedFrame.lean']):
    name = full.split('.')[-1]
    source = path.read_text()
    key = 'theorem ' + name + ' :'
    a = source[source.index(key):source.index(' := by', source.index(key))]
    b = challenge[challenge.index(key):challenge.index(' := by', challenge.index(key))]
    assert a == b and hashlib.sha256(a.encode()).hexdigest() == manifest['theorem_signatures'][full]
assert hashlib.sha256(definition(challenge, 'SquaredNormEdges').encode()).hexdigest() == manifest['SquaredNormEdges_sha256']
assert hashlib.sha256(definition(challenge, 'FixedFrameOSE').encode()).hexdigest() == manifest['FixedFrameOSE_sha256']
assert re.findall(r'^run_cmd .+$', challenge, re.M) == ['run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}']
print('STATIC_PREFLIGHT_PASS: frozen inputs, two exact statements, transparent definitions, imports, pins and licence', flush=True)
if not args.static_only:
    for cmd in [
        ['lake', 'env', 'lean', '-o', '.lake/build/lib/lean/Challenge.olean', 'Challenge.lean'],
        ['lake', 'env', 'lean', '-o', '.lake/build/lib/lean/Solution.olean', 'Solution.lean'],
        ['lake', 'env', 'lean', '--run', 'palomar/CheckClosure.lean'],
        ['lake', 'env', 'lean', 'palomar/AxiomAudit.lean'],
    ]:
        subprocess.run(cmd, cwd=ROOT, check=True)
    print('LOCAL_ELABORATION_AND_CLOSURE_PASS; use the Linux workflow for pinned Comparator/NanoDa verification')
