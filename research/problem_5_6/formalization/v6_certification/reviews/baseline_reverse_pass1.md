# Reverse audit pass 1: actual B semantics and dependency routes

Reviewer `/root/baseline_audit`, separate from B and current addon proof authors. Scope is the main OSE, graph contraction, and trace aggregation routes assigned by the controller. This is one independent pass of the requested reverse audit; it is not two passes, whole-v6 coverage, or final combined reproduction.

Source-first expectations were frozen in `baseline_expected_semantics.md` before the graph inspection. The raw actual types for the three endpoints were then read at `pp.all` level, including every input binder and arithmetic coercion. They have exactly the finite real/Walsh fields, dimensions, constants, rank hypotheses, operator ordering, and quantifier order described by the semantic report. A copy of inspected actual types and raw-expression hashes is in `baseline_reverse_reviewed_types.json`.

The current emitted graph was independently parsed from `logs/baseline_full_graph.log`: 53 unique target records, 61,701 unique node records, exactly one matching `CERT_END=61701`, no dangling dependency name, and no forbidden axiom node. The independent traversal used both type and body edges without namespace filtering. Primitive definitions, imported dependencies, constructors and recursors remain in the traversal. This checks the emitted data; the controller still owns final fresh compilation and replay trust.

The three endpoint closure sizes are main_universal_ose 61,531; graph_rank_contraction 29,789; signed_trace_proposition 38,380. Each contains only propext, Classical.choice, Quot.sound as axiom nodes. Full paths and log/type hashes appear in `baseline_reverse_graph_checks.json`. In particular these are **body-edge paths**, not merely co-occurring names or imports:

- main_universal_ose → bernoulli_coordinate_sampling_corollary → signed_trace_proposition.
- main_universal_ose → fixed_size_sampling_transfer and → small_rank_second_moment.
- graph_rank_contraction → I07_rank_edge_factorization_bound → mingo_speicher_graph_operator_specialization → endpointAwareRankCutStepFactorization_all.
- graph_rank_contraction → I07_rank_edge_factorization_bound → I05_mingo_speicher_bridgeless_conversion → mingo_speicher_bridgeless_conversion.
- signed_trace_proposition → signedTrace_bound → signedTrace_master_geometric_bound → private selectorEqualityData_contribution_sum_le → private selectorEntryContribution_abs_sum_le_aggregateBound → aggregate_partition_cumulant_bound.
- signed_trace_proposition → signedTrace_bound → signedTrace_master_geometric_bound → private signedTrace_abs_le_boundedSelectorData → signBernoulliExpectation_trace_eq_partition_cumulant_sum.

This confirms the source-described mechanisms actually support the theorem proof bodies. The graph norm bound does not terminate at an uninstantiated factorization certificate; the trace bound does not terminate at a bound supplied as a theorem hypothesis. `spectralFailureSup` and `frameFailureProbability` also occur in the actual main proof closure. Those concrete definitions were read separately in the semantic audit.

**Pass-1 local outcome:** no additional semantic defect found for these B endpoints and their identified proof routes. Exact C correspondence still needs the graph transpose/boundary bridges and separately callable fixed-(d,h) contribution statement described in `baseline_semantic_audit.md`, plus the independent general-domain work. The source/expected definitions remain authoritative if later generated type manifests differ. The controller noted this preliminary execution receipt included hashes of unimported addons; therefore this report binds the actual graph log hash and reviewed source bytes, and does not claim that receipt is the final precise closure manifest. Final combined graph output must be rechecked after integration.
