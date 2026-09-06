# Root-pruned modification history: expected statements

Executor: `/root/graph_entry_proofs`. This record preserves the independent expected-statement approval given
before proof generation and the subsequent implementation/build evidence.
It is not self-approval of correspondence.

The source scope is the frozen C I-V6-10 conversion and I-V6-11 boundary-entry
preservation. `FiniteBoundaryGraph` carries only finite graph/matrix data.
`ElementaryBoundaryModification` has exactly the reversal and root-pruned
identity-star split constructors; `BoundaryModification` is their finite
reflexive-transitive closure. No analytic bound is an input field.

`RootedHistoryExpected.lean` introduces primitive boundary operator/norm-product
notations and `BoundaryEntriesPreserved`, whose endpoint dimension equalities
and `Fin.cast` equality are output conclusions. `RootedElementaryExpected`
and `RootedHistoryExpected` require boundary preservation and norm-product ≤
for all dimensions, and exact norm equality plus preserved positivity when
all input dimensions are positive. This preserves the paper's positive-space
scope while also recording B's harmless zero-dimensional extension.

`GeneralBridgelessConsequenceBridgeExpected` accepts only the separately proved
literal topology construction. It derives the existing general conversion
operator target by consuming that construction's finite history. It does not
constitute a proof of the pure topology proposition; final closure requires an
actual proof argument supplied to the bridge.

Planned reuse: immutable B `rootedFiberSplitIdentityProduct`,
`fiberSplitConsistentEquiv`, `rootedFiberSplitMatrix_norm_product_le`, and the
already accepted additive reversal/identity-norm lemmas. Root-pruned stars omit
the trivial root identity loops from the previous all-copy representation.
Boundary preservation is obtained before any unrestricted boundary summation.

The controller independently approved the unchanged expected module before
proof generation and recorded `reviews/rooted_history_expected_review.json`.
Proof modules are now `RootedHistoryBoundary.lean`, `RootedHistory.lean`, and
`RootedHistoryConversion.lean`. The final public theorem
`general_bridgeless_matrix_conversion` applies the bridge to the actual
`generalBridgeless_modification` theorem; it does not leave a conversion
proposition as an input for public callers. Targeted compilation completed successfully: `RootedHistoryExpected` and
`RootedHistoryBoundary` passed in `logs/addon_iteration13.log`;
`RootedHistory` and `RootedHistoryConversion` passed in
`logs/addon_iteration14.log` (25.64 seconds for the serialized build,
8817 jobs in the combined import graph). The actual log ends with
`Build completed successfully (8817 jobs).`

Frozen expected-module SHA256:
`e3645969f8fe9f6bfeaa5ac6e89f1355b7ee600396552288e284ac73beb864ee`.


## Proved entry points and dependency separation

- `rooted_graph_boundary`: exact matrix equality for the root-pruned identity
  split, with the selected copies carrying the two boundary labels. It uses
  immutable B `rootedFiberSplitIdentityProduct` and
  `fiberSplitConsistentEquiv`, plus accepted additive finite-sum helpers.
- `rooted_graph_norm_product`: exact norm-product equality for positive
  dimensions; it reuses `paper_identity_norm` for each added proper-copy edge.
- `rooted_elementary : RootedElementaryExpected`: handles each actual reversal
  or split constructor. The all-dimension weak bound uses B's
  `rootedFiberSplitMatrix_norm_product_le`; it is not an assumed graph field.
- `rooted_history : RootedHistoryExpected`: induction over the literal finite
  history; dimension equalities compose, and `Fin.cast_cast` transports each
  boundary entry. Positivity and norm equality propagate step by step.
- `rooted_history_consequence : GeneralBridgelessConsequenceBridgeExpected`:
  the internal compositional theorem consumes the separate topology result.
- `general_bridgeless_matrix_conversion : GeneralBridgelessConversionExpected`:
  the final public entry point applies that bridge to the actual
  `generalBridgeless_modification` proof from `GeneralBridgelessConversion`.
  The public theorem has no conversion, boundary-equality, or norm-certificate
  hypothesis. Its exact explicit matrix/dimension type is the already frozen
  `GeneralBridgelessConversionExpected` proposition.

These statements retain B's input-row/output-column representation; the
already proved graph orientation bridge interprets the boundary operator in
C's target-row/source-column convention.

The four new RootedHistory module bytes are frozen after this successful build.
No accepted GraphModifications module or protected B proof/build file was
edited. The final full dependency/axiom audit and independent correspondence
acceptance belong to the controller's combined reports, not this implementation
record. No remaining proof goal exists in these four modules.

## Final source hashes

SHA256, computed after the successful build:

- `RootedHistoryExpected.lean`: `e3645969f8fe9f6bfeaa5ac6e89f1355b7ee600396552288e284ac73beb864ee`
- `RootedHistoryBoundary.lean`: `3a9cc850c72eff829441032b4efe8e68d3011428cb43de06094583abe449ecb6`
- `RootedHistory.lean`: `631273263d23c64cc980a23a2506145ecf4ebb91f4e9b5f7bfaa332f19f2b0ed`
- `RootedHistoryConversion.lean`: `8e611a22f7f3ec5fd8079304040e57d7e981852e979171b51eb2e4d9b1a1bcd5`
