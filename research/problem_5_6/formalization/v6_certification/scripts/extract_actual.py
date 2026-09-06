#!/usr/bin/env python3
"""Extract actual checked declarations, without approving their paper scope.

Reviewer-owned expectations and locks are deliberately never modified here.
"""
import json,pathlib
from verify_evidence import parse_log,read_text,validate_records,require
E=pathlib.Path(__file__).resolve().parents[1]
log=E/'logs/combined_audit.log'
targets,nodes=parse_log(log)
result=validate_records(targets,nodes,json.loads((E/'combined_target_inventory.json').read_text()))
definitions={}
for line in read_text(log).splitlines():
 if line.startswith('CERT_DEFINITION|'):
  row=json.loads(line.split('|',1)[1]);require(row['name'] not in definitions,'duplicate definition')
  definitions[row['name']]=row
require(set(definitions)==set(json.loads((E/'primitive_definition_inventory.json').read_text())),'definition inventory mismatch')
for name,data in [('combined_actual_types.json',targets),('combined_actual_definitions.json',definitions),('combined_graph_component_result.json',result)]:
 (E/name).write_text(json.dumps(data,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if k!='axiom_closures'}))
