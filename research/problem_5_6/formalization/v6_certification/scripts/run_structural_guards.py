#!/usr/bin/env python3
"""Run every unchanged historical source-marker guard with its required ID.

These are structural checks, not proofs of semantic correspondence.
"""
import ast,pathlib,subprocess,sys

EXPECTED=[
 'R-MAIN-QUANTIFIERS','R-EXACT-RANDOM-LAW','R-MATRIX-ORDER',
 'R-BOTH-SPECTRAL-EDGES','R-SIGNED-TRACE','R-I35-CONDITIONAL-COUPLING',
 'R-I16-I19-MOMENT-SCOPE','R-I08-NONEMPTY','R-L2-NORM-SCOPE',
 'R-GRAPH-ORIENTATION','R-I04-ADJACENT-RANK-CUT','R-I35-THREE-CATEGORY-ORDER',
 'R-I07-RANK-EDGE-SPLIT','R-I05-BRIDGELESS-DAG','R-JOINT-ENTRY-REINDEX',
 'R-SIGNED-TRACE-SUMMATION','R-TRACE-CYCLIC-EXPANSION',
 'R-SIGNED-TRACE-EXPANSION','R-I20-CONTRACTED-CORE-CLOSURE']
if len(sys.argv)!=2:raise SystemExit('usage: run_structural_guards.py /path/to/semantic_regressions.py')
script=pathlib.Path(sys.argv[1]).resolve()
tree=ast.parse(script.read_text());inventories=[]
for node in tree.body:
 if isinstance(node,ast.Assign) and any(isinstance(t,ast.Name) and t.id=='tests' for t in node.targets):
  if not isinstance(node.value,ast.Dict):raise SystemExit('unexpected historical test inventory')
  inventories.append([ast.literal_eval(k) for k in node.value.keys])
if inventories!=[EXPECTED]:raise SystemExit('historical structural inventory changed or incomplete')
for test_id in EXPECTED:subprocess.run([sys.executable,str(script),test_id],check=True)
print('Historical structural guards: 19/19 PASS (source markers only)')
