#!/usr/bin/env python3
"""Additional scope gate; proof audit must independently pass as well.

A successful encoded-proof build does not override a source repair or an
unresolved literal interface. This command fails on either condition.
"""
import json,pathlib,sys
from verify_evidence import require_full_paper_coverage,paper_coverage_result,validate_paper_inventory
E=pathlib.Path(__file__).resolve().parents[1]
try:
 rows=validate_paper_inventory(E.parents[3],json.loads((E/'combined_actual_types.json').read_text()))
 print(json.dumps(paper_coverage_result(rows),indent=2))
 require_full_paper_coverage(rows)
except (OSError,KeyError,ValueError) as exc:
 print('FAIL: '+str(exc),file=sys.stderr);sys.exit(1)
