# Frozen revision correspondence candidate

Review the exact paper delta and its mapping to unchanged Lean declarations.
The paper changes only def:graph-contraction to require positive integer coordinate dimensions.
Read I-V6-11 and the graph definitions and dependent uses in the new snapshot.
Compare paper_identity_norm, graph_fiber_boundary, graph_reversal_boundary, graph_fiber_norm_product, rooted_elementary, rooted_history and rooted_graph_norm_product against their actual elaborated types and definitions in the unchanged certification evidence.
Check positivity persists along the permitted finite histories and that matrix orientation, boundary entries, full sums and norm-product equality have the written scope.
Check that stronger Lean theorems covering arbitrary dimensions can be restricted to the new positive-dimensional definitions for every affected row.
The old 12/50/34 inventory and exact proof/type/definition hashes must be preserved; only source reanchoring and reviewed scope changes are authorized.
No zero-dimensional product-equality assertion, new theorem, publication approval or authenticated workflow receipt may be inferred.

Inputs: revision_contract.json, paper_delta.patch, frozen_C_manifest.json, candidate_crosswalk.json, the three revised inventories, snapshots/, and the parent evidence directory.
Output: independent_report.json/md; reviewed_crosswalk.json; reviewed_revision_lock.json. The report must preserve any open defect.
