# Graph, binary-constraint, and fixed-class contribution implementation

Implementation author: `/root/graph_entry_proofs`. This is an implementation
record, not an independent correspondence acceptance. The reviewer-owned
`GraphAndEntryExpected.lean` supplies the unchanged nine expected propositions.

All changes are additive, under `Problem56.PaperV6`; baseline B proof bodies
and build files are untouched. The implementation imports `Problem56.Statements`.
The controlling protocol is `.danus/policy/research_paper_engineering_protocol.md`
(version 0.2-draft), with the frozen certification prompt's authorized evidence
location taking precedence over the protocol's generic run-artifact location.

## Intended target mapping

| Expected proposition | Implementation theorem | Adaptation |
|---|---|---|
| GraphOrientationExpected | graph_orientation | target-row/source-column transpose; explicit path/source/sink equivalence |
| GraphBoundaryExpected | graph_boundary | exact boundary sum with distinct prescribed vertices |
| GraphOperatorExpected | graph_operator | I04 plus transpose norm equality |
| GraphRankExpected | graph_rank | graph_rank_contraction plus HEq dimension and projection-transpose transport |
| BinaryForbiddenPairExpected | binary_forbidden_pair | injective characteristic-two classification plus block XOR vanishing |
| BinaryCountExpected | binary_count | exact unrestricted count and injective subtype cardinal upper bound |
| BinaryOddIncidenceExpected | binary_odd_incidence | forbidden/surviving equivalence, derive d≤p−1 from nonempty partition, I24 |
| EntryWeightedCountExpected | entry_weighted_count | I28 at d≤p−1; empty-class proof otherwise; I24 for nonempty class |
| EntryAbsoluteContributionExpected | entry_absolute_contribution | exact fixed-class label sum, selector product, exact I29 dimension factors |

`paper_sum_injective_labels_bound` retains absolute values inside the labeling
sum, and `paperEntry_fixed_class_sum_bound` sums over exactly
`AggregateEntryPartition Q d h`. No all-(d,h) bound is substituted for this
fixed class. The weight is the baseline definition
`entryPartitionCumulantConstant = ∏ B∈P.parts, (2*B.card)^(12*B.card)`.
No XOR sufficiency is asserted: XOR is only a necessary support condition.

For d≥p the partition type is empty because a partition of Fin(2*p), p≥2,
has a positive number of blocks. When the class is nonempty, rank≤column count
and Q.parts.card=p−s give s+h≤p; these hypotheses are derived inside the proof,
not added to the expected statement. The final RHS retains the exact negative
integer powers in s,d,h.

## Reuse provenance

The transpose, I04, graph-rank, I24, I28, I29, and characteristic-two proofs are
called directly. The few private B helpers inaccessible by normal imported
Lean identifiers were reconstructed under distinct PaperV6 names, with the
same finite-sum arguments, without modifying or shadowing old declarations:

- SignedTraceExpansion.lean 745–761: finite equivalence Fin B.card ≃ B, now
  `paperBlock_xor_sum`.
- SignedTraceExpansion.lean 556–576: injection-to-full-finite-sum estimate,
  now `paper_sum_le_of_injective`.
- SignedTraceExpansion.lean 774–870: support and label-sum argument, now
  `paper_product_xor_of_ne_zero` and `paper_sum_injective_labels_bound`, using
  the public old cumulant-product bound/vanishing theorem and exact XOR count.
- SignedTraceExpansion.lean 1265–1286: inverse-power notation rearrangement,
  now `paper_dimension_factor`, calling public I29 for its substantive equality.

## Additional frozen interface scope

I-V6-10 (C 930–936) is broader than B I05: it assumes connected and bridgeless,
whereas `mingo_speicher_bridgeless_conversion` in B additionally assumes positive
even degrees. Connected bridgeless K4 has degree three, so no implication from
the written assumptions to B's hypotheses exists. The nine targets above do
not prove the general bridgeless conversion. No new axiom, conditional field,
or merely renamed I05 is offered as coverage. A faithful additional theorem
would need the actual graph-modification relation and a general conversion
construction (e.g. the external source's ear/path construction), or a clearly
recorded externally supported interface with kernel coverage left open.

The initially identified I-V6-11 gap (C 938–970) concerns fixed-boundary-entry preservation under allowed
identity splits and edge reversal. B has scalar contraction equalities
`graphContraction_fiberSplit`, `graphContraction_rootedFiberSplit`, and
`graphContraction_selectivelyReverse`; these and I05's scalar-sum equality do
not on their own establish the stronger fixed-boundary assertion. The reversal
part is immediate entrywise; the supplemental module below now supplies the
reviewed boundary-copy constraints and finite-sum transport.
B's generic norm-product statements are ≤ rather than equality because its
zero-dimensional cases are wider; the manuscript's positive dimensions permit
identity norm exactly one. These distinctions remain in the inventory.

## Supplemental boundary-preservation targets

The controller independently froze and reviewed `GraphModificationsExpected.lean`
(SHA256: `dd14ef25a551cb4bef21f6b2671160c78dc4d939bce2b1310f808344db67d6d6`).
The source was elaborated before implementation (`logs/graph_expected.log`).

`GraphModifications.lean` implements `graph_fiber_boundary` and
`graph_reversal_boundary` against those definition-only Props. The former uses
B's actual finite-copy graph with arbitrary incidence routing and selected
boundary copies; each consistent copied labeling corresponds to precisely one
old labeling. The identity product kills inconsistent copied labels before
reindexing. The latter uses the actual `selectiveReversalEquiv`, preserving the
same boundary test. `paper_identity_norm` and `graph_fiber_norm_product` retain
the manuscript's positive dimension assumption for exact norm equality.
These targets have passed compilation against the reviewed expected Props.
They supply the additional I-V6-11 boundary-strength proof evidence; they do
not prove I-V6-10 conversion. Independent final correspondence acceptance is
not asserted by the implementation author.

The controller located the user's published JFA PDF and supplied a read-only
extraction at `reviews/mingo_published_extraction.txt`. I read its Lemma 16 and
proof (extraction 786–829), confirming the broad connected bridgeless statement
and the finite ear/path insertion proof. This resolves the source-numbering
question, not the missing general Lean conversion construction.

GraphBridges passed in `logs/additive_batch4.log`; BinaryBridges passed in
`logs/additive_batch6.log`; EntryBridges passed in
`logs/entry_modification_iteration4.log` (18 seconds). GraphModifications,
ExpectedChecks, and SemanticWitnesses passed in
`logs/expected_and_graph_iteration5.log`. All nine original expected
propositions and both supplemental expected propositions have completed
targeted compilation, together with the supplemental positive-dimensional
identity and norm-product equalities. No implementation proof goal remains.

This report does not self-approve independent correspondence or a final axiom
audit. The controller performs the combined proof-closure audit and independent
review; those results must be read from their actual reports. I-V6-10's general
ear/path conversion remains outside the scope of these four implementation
modules; any further proof is accounted separately by the controller.

## Final worker source hashes

SHA256, computed after the successful targeted build and before this handoff:

- `GraphAndEntryExpected.lean`: `1e0a265df84ba4d117cfc8212db8f7b75ecf5ae31e5efa07586ed7b6c25edfb9`
- `GraphModificationsExpected.lean`: `dd14ef25a551cb4bef21f6b2671160c78dc4d939bce2b1310f808344db67d6d6`
- `GraphBridges.lean`: `016321e3426ac396d32fc352d6e69638aeaf5c36644c683ea0bb6f19d5e4f9f5`
- `BinaryBridges.lean`: `0e786c35a6c9807e9970ab753818f987b8d31f75f5d9ca3958ac4ffb6ff6b6f4`
- `EntryBridges.lean`: `979f779200ae074b43639141a6326ad199b42426d2c902c241275feed599ffea`
- `GraphModifications.lean`: `9b7a9e511a814860e5c414c25b13457aa7139975f2a0ed7e4fc6fbb1b2e3d3d1`
