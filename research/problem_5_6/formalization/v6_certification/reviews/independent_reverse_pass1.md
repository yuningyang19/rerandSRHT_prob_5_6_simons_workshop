# Independent reverse audit, pass 1

Reviewer `/root/baseline_audit`; audit-only, separate from the additive proof authors. This report proposes reverse-audit candidates and does not assign pass-2 RA classifications. GeneralSamplingExpected was a definitions-only reviewer contribution, independently source-approved before another context wrote its proof. No manuscript bytes or proof bodies were changed by this review.

The frozen graph has 189 targets, 62407 nodes, 39 definition records, one complete graph terminator, no missing dependency, and only propext, Classical.choice and Quot.sound as axiom nodes. Log SHA256: `d71c4db87cad0fce2be6b4d8c85ebcc4acf6b310b44934635f4dca5ca037b3e7`. Exact types, definition bodies, inventory hashes and mechanically checked proof-body paths are retained in the JSON and graph snapshot. This is a development snapshot, not final clean-build or replay attestation.

All 12 named statements, 30 conjuncts, 50 source interfaces and 34 source definitions remain in scope. Source-first baseline reports cover B; this pass read the additive expected statements and implementations, including arbitrary-measure cumulants, the general sampling and finite-noise transport, squared-norm interpretation, graph orientation and boundary preservation, binary support and fixed-class absolute contribution. General graph ear/path helpers in this snapshot are only partial preparation. The refreshed 189-target graph also includes incoming/outgoing DAG splitting, concrete fresh-path insertion and injective finite rank ordering. These three modules were read in full: they derive the local acyclicity and reachability conclusions, but do not compose the general bridgeless conversion. The ongoing unimported state-construction module is excluded.

Conservative literal interface accounting is **47/50**: exclude I-V6-10 (general conversion), I-V6-14 (formal-series coefficient objects), and I-V6-42 (continuous order-statistic objects). Downstream conclusions including valid alternative proofs cover **49/50**: partition cancellation establishes the cumulant conclusion, and finite common-order coupling establishes the sampling conclusion. Neither count is final machine certification. I-V6-11 counts its frozen per-operation boundary/sum/norm preservation; a finite history datatype is not an additional frozen claim in that interface and belongs to the outstanding general-conversion construction.

The written-source definitions D-V6-13 and D-V6-31 retain the general bridgeless and continuous-uniform meanings. D-V6-27 disjoint-pair support U is contained in the implementation weight-four support; these supports are not claimed definitionally equal. The 34-item definition denominator does not mean 34 identical Lean constants.

## Four-test candidates

### R1: thm:main

Universal width is chosen before a deterministic frame; success means both squared-norm edges for every vector in this fixed frame.

Actual body path: `Problem56.PaperV6.fixed_frame_squared_norm_success → Problem56.PaperV6.squared_edges_iff_spectral_bound`.

- Deletion: Removing normalization or supremum domination severs the fixed-frame probability conclusion.
- Object identity: Read exact sampled Gram, uniformProbability, spectralFailureSup and Euclidean L2 objects; no simultaneous all-subspaces event.
- Route substitution: Quadratic-form equivalence is a valid explicit elaboration, while casts and normalized-vector case splits need no manuscript text.
- Endpoint: Check k=n, z=0, nonempty k-subsets and both inclusive success edges; failure is strict > epsilon.

### R2: lem:transfer

The two-projection route includes endpoint blocks, defective 2x2 blocks and compensation for nonreal roots.

Actual body path: `Problem56.two_projection_spectral_transfer → Problem56.two_projection_spectral_transfer_proof → Problem56.exists_twoProjection_bad_block_trace_gt → Problem56.twoProjectionPairTransferMatrix_trace_even_power_gt_of_large_real_root → Problem56.real_matrix_fin_two_trace_pow_eq_root_power_sum_re`.

- Deletion: Deleting endpoint or negative-block compensation would invalidate the spectral-to-signed-trace implication.
- Object identity: The paper and Lean use the same centered projections and signed even trace, not an expected absolute moment.
- Route substitution: Matrix trace equals root power sum even without diagonalizability; a spectral-only argument assuming simple roots cannot replace it.
- Endpoint: Retain lambda=0,1 and delta endpoints and the zero spectral-deviation branches.

### R3: prop:trace

Actual signed trace aggregation reaches the concrete partition-weight estimate, through the centered Gram and cyclic trace identities.

Actual body path: `Problem56.signed_trace_proposition → Problem56.signedTrace_bound → Problem56.signedTrace_master_geometric_bound → _private.Problem56.SignedTraceExpansion.0.Problem56.selectorEqualityData_contribution_sum_le → _private.Problem56.SignedTraceExpansion.0.Problem56.selectorEntryContribution_abs_sum_le_aggregateBound → Problem56.aggregate_partition_cumulant_bound`.

- Deletion: Deleting selector/entry factorization or exact-class regrouping destroys the finite trace majorization.
- Object identity: Equality partition pi differs from entry occurrence partition rho; absolute expected trace remains distinct from expected absolute trace.
- Route substitution: Finite reindexing implementation is bookkeeping; the dimension factors and geometric parameter ranges are mathematical obligations.
- Endpoint: Retain zero/positive parameter branches, empty classes and logarithmic-rank hypotheses.

### R4: cor:bernoulli

Bernoulli probability derives from compensated signed trace and the stated logarithmic choice of p.

Actual body path: `Problem56.bernoulli_coordinate_sampling_corollary → Problem56.signed_trace_proposition`.

- Deletion: Without compensation, a negative signed contribution cannot support Markov-type probability inference.
- Object identity: Same two independent sign layers, centered Bernoulli law and effective width kappa.
- Route substitution: Elementary final arithmetic may differ in algebraic order but cannot replace the signed trace by a norm moment.
- Endpoint: Check all density/rank inequalities used by the corollary rather than only asymptotic large rank.

### R5: lem:graph

The paper orientation and rectangular boundary convention are transported to the existing rank proof.

Actual body path: `Problem56.PaperV6.graph_rank → Problem56.graph_rank_contraction`.

- Deletion: Removing transpose/boundary transport would prove a differently oriented matrix statement.
- Object identity: Target-row/source-column paper matrices match the explicit transposition of B; loops and distinct boundary copies are retained.
- Route substitution: The graph proof reaches a constructed factorization, not an assumed norm field; mere equality of scalar sums would be insufficient.
- Endpoint: Projection edge can be a loop; factorization creates two distinct r-dimensional copies and preserves the rank multiplier.

### R6: lem:graph

Each allowed fiber split preserves every entry with designated boundary labels fixed.

Actual body path: `Problem56.PaperV6.graph_fiber_boundary → Problem56.fiberSplitConsistentEquiv`.

- Deletion: A full scalar-sum identity alone cannot replace boundary-entry preservation in the operator argument.
- Object identity: The fiber label equality is enforced by actual identity edges, with fixed input/output copy labels.
- Route substitution: Restriction to consistent labels and its finite bijection is an equivalent elaboration; the implementation does not encode a general finite modification-history datatype.
- Endpoint: Positive coordinate dimensions are necessary for identity norm exactly 1; dimension zero would give only the weaker bound.

### R7: lem:graph

The broad connected-bridgeless conversion stated in v6 is not established merely by the narrower even-degree B conversion.

Actual body path: `Problem56.PaperV6.graph_rank → Problem56.graph_rank_contraction → Problem56.I07_rank_edge_factorization_bound → Problem56.I05_mingo_speicher_bridgeless_conversion → Problem56.mingo_speicher_bridgeless_conversion`.

- Deletion: Deleting even-degree hypotheses from B is invalid; the general construction remains a separate obligation.
- Object identity: GeneralBridgelessExpected uses connectedness and edge deletion, with prescribed distinct endpoints and no assumed norm certificate.
- Route substitution: An imported published statement can validate the written source, but does not make the general conversion a local kernel theorem.
- Endpoint: Current ear/path helpers do not themselves close arbitrary connected bridgeless graphs or allowed modification histories.

### R8: lem:cumulant-identities

General moment and product identities are algebraic partition identities in actual integral moment data.

Actual body path: `Problem56.PaperV6.generalCumulantIdentities → Problem56.PaperV6.generalMomentIdentity`.

- Deletion: Finite-uniform-only expectation would leave the stated arbitrary probability-space conclusion uncovered.
- Object identity: measureJointCumulant uses real finite products and integrals; no target identity is a field of the moment structure.
- Route substitution: Partition cancellation validly replaces the written formal-log route for the conclusion; formal logarithm and exponential coefficient objects themselves are not kernel encoded.
- Endpoint: Nonempty occurrence families and empty moment normalization are distinct; no analytic exponential-integrability assumption is introduced.

### R9: lem:cumulant-identities

Mixed independence, multilinearity, shifts and odd symmetry retain the manuscript general domain.

Actual body path: `Problem56.PaperV6.generalCumulantIdentities → Problem56.PaperV6.generalMixedIndependence`.

- Deletion: Without expectation factorization under independent families, mixed vanishing would be assumed rather than proved.
- Object identity: Finite requisite products are integrable under arbitrary probability measure; IndepFun and IdentDistrib supply the actual law facts.
- Route substitution: Cardinality induction and finite partition cancellation are alternative valid proof organization, while measurable representatives alone do not require prose expansion.
- Endpoint: Shift invariance requires q>=2; symmetry uses odd order and exact distributional symmetry, not pointwise oddness.

### R10: lem:cumulants

The cumulant bounds and XOR vanishing use both normalized Walsh layers and the fixed-frame law.

Actual body path: `Problem56.joint_entry_cumulant_lemma → Problem56.joint_entry_cumulant_assembly → Problem56.joint_entry_cumulant_assembly_of_occurrence_expansion → Problem56.joint_entry_cumulant_vanish → _private.Problem56.JointEntryCumulant.0.Problem56.joint_entry_cumulant_covariance → _private.Problem56.JointEntryCumulant.0.Problem56.randomProjection_walsh_transform_entry → Problem56.randomProjection_walsh_symmetry → Problem56.transformedFrame_walsh_symmetry → Problem56.signDiagonal_translate`.

- Deletion: Deleting the fixed-frame sign-law invariance invalidates character-induced XOR vanishing.
- Object identity: Occurrence partitions allow repeated labels across blocks; graph contractions are unrestricted signed sums.
- Route substitution: The partition route is exact reuse; XOR is a necessary support condition and never a sufficient nonvanishing certificate.
- Endpoint: Centering leaves cumulants unchanged only in orders >=2; first cumulants are handled separately.

### R11: lem:count

Exact equality counts preserve half-edge ports, returning paths and the separate unmarked case.

Actual body path: `Problem56.selector_equality_graph_count → Problem56.I20_contracted_core_encoding_bound`.

- Deletion: Deleting port identity or a=0 handling destroys the claimed decoding/count injection.
- Object identity: Counted objects are numbered equality patterns with no extra vertex-permutation factor; returning and parallel links are distinct.
- Route substitution: Lean finite encoding is a valid elaboration only because deterministic expansion recovers the actual original graph.
- Endpoint: Zero chain lengths and B-empty exceptional graphs are retained, rather than dismissed by positive-parameter bounds.

### R12: lem:binary-constraints

Unrestricted XOR kernel count is exact; injective label count is bounded by inclusion.

Actual body path: `Problem56.PaperV6.binary_count → Problem56.entryXorConstraintSolutionCount`.

- Deletion: Removing forbidden injective pairs before using unrestricted labels is mathematically necessary.
- Object identity: Paper block XOR and actual binary constraint rank are proved equal; B weight-four support is a safe superset of source disjoint-pair support U, not identical.
- Route substitution: Coordinatewise kernel cardinality is a valid proof route; necessity cannot be promoted to sufficiency.
- Endpoint: Retain rank-zero, repeated-loop cases and t<=12d+4h without assuming every supported labeling contributes nonzero.

### R13: prop:entry-contribution

Fixed-(d,h) bounds contain the actual weighted partition sum and internal absolute label/selector contributions.

Actual body path: `Problem56.PaperV6.entry_absolute_contribution → Problem56.PaperV6.paperEntry_fixed_class_sum_bound`.

- Deletion: Deleting the explicit finite-sum bridge leaves a code-count theorem with the wrong object.
- Object identity: The weight is product_C (2|C|)^(12|C|), and all r/n powers match the paper; pi and rho are distinct.
- Route substitution: Termwise absolute sums imply the required signed absolute contribution; reverse implication is not used.
- Endpoint: All natural d,h are covered via a proved empty-class alternative; nonempty class implies d<=p-1 and s+h<=p, preventing unsafe Nat subtraction.

### R14: lem:sampling

Arbitrary independent random frame sampling is certified through averaged pointwise bounds and exact finite-noise law transfer.

Actual body path: `Problem56.PaperV6.general_sampling_joint → Problem56.PaperV6.bernoulli_noise_failure_law → Problem56.PaperV6.finiteNoiseFailureLaw`.

- Deletion: Replacing averaged marginal failures by a maximum gamma would weaken the target and is not done.
- Object identity: Measurable coordinate maps represent the same random real matrix; uniform k-subset and Bernoulli marginals are exact.
- Route substitution: Finite common-order coupling is a valid alternative to continuous uniforms; the latter order-statistic object and null-tie proof are written-source only.
- Endpoint: No independence between lower and upper Bernoulli samples is assumed; only independence from X and the required marginal laws are used.

### R15: lem:small

Finite-population second moment and row fourth moment preserve fixed-size without-replacement sampling.

Actual body path: `Problem56.small_rank_second_moment → Problem56.small_rank_second_moment_of_gram_reduction → Problem56.small_rank_frobenius_expectation_bound`.

- Deletion: Substituting independent row selection would change the finite-population factor.
- Object identity: The row Rademacher law and Frobenius domination refer to the same normalized Gram.
- Route substitution: Operator domination and probability arithmetic are valid consequences of the exact expectation identity.
- Endpoint: Full sampling, n=1 where allowed, and the chosen small-rank width branch retain their explicit cases.

## Findings and handoff

No new mathematical defect was identified in the reviewed additive proofs or audited B endpoints. The general connected-bridgeless conversion has status FORMALIZATION_OPEN in this snapshot. The published source result was independently checked; this is not a claim that the mathematical theorem is an open problem. No numerical result, supplied expected proposition, published reference, helper path theorem or emitted graph record is treated as a proof of that missing conclusion. The written formal-log and continuous-uniform routes need their own source audit and are not falsely described as literal kernel objects.

Three additive declarations were present transitively but omitted as explicit targets by a generator that required column-zero `theorem`: aggregate_parameters, pair_eq_iff and generalMomentIdentity. This was a coverage-inventory defect, not an admitted proof. The generator was changed to strip leading whitespace and the refreshed 189-target inventory contains all three. A further same-line attribute edge case omitted adjoinedEarPoint_zero, adjoinedEarPoint_last and adjoinedEarPoint_internal as explicit targets. All occur in the checked transitive closure; the subsequent attribute-stripping fix was read, and final inventory refresh should expose them too.

The installed lifecycle asks for distinct hash-bound generator passes and controller-runtime invocation receipts. This custom report is a real independent context output, but it does not fabricate an authenticated receipt or claim schema compliance. certification_packet.json is a custom preparation packet; baseline_packet_validation.json records submitting it to the different verification-kernel packet schema. That rejection is a schema mismatch, not a mathematical rejection. Proper current workflow artifacts/validation remain separate prerequisites.

Pass 2 must read exact C source first and independently classify these candidates; the controller must refresh graph/types/source bindings after integration, run the mandatory clean reproduction and stored-proof replay, and retain exact unresolved coverage if general conversion or literal intermediate coverage remains open. No full manuscript PASS is supported by this snapshot.
