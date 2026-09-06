#!/usr/bin/env python3
"""Check every immutable exported file and the complete local Lean inventory."""
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]

def verify():
    raw = (ROOT / 'EXPORT_MANIFEST.json').read_bytes()
    if hashlib.sha256(raw).hexdigest() != '80181167590998c82a02e7b233793b5abb3176c2f268d5d03f03e03c9ec51a49':
        raise SystemExit('FAIL: export manifest differs from the frozen export')
    manifest = json.loads(raw)
    for name, digest in manifest['files'].items():
        path = ROOT / name
        if not path.is_file() or hashlib.sha256(path.read_bytes()).hexdigest() != digest:
            raise SystemExit('FAIL: missing or changed certified input: ' + name)
    lean = ROOT / 'research/problem_5_6/formalization/lean'
    actual = {str(p.relative_to(ROOT)) for p in lean.rglob('*.lean')
              if '.lake' not in p.relative_to(lean).parts}
    expected = {p for p in manifest['files']
                if p.startswith('research/problem_5_6/formalization/lean/') and p.endswith('.lean')}
    if actual != expected:
        raise SystemExit('FAIL: local Lean file inventory differs from certified export')
    print(f'PASS: {len(manifest["files"])} immutable inputs; {len(actual)} Lean files (including lakefile.lean)', flush=True)
    return manifest

if __name__ == '__main__':
    verify()
