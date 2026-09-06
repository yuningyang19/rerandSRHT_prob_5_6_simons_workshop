# Independent graph-state invariant review

Reviewer `/root/v6_inventory`, before transition-proof generation.
Reviewed definitions-only file SHA-256: `bec214f664fa45b227be54002d74e75120c0fe7825a336659f8619511470e143`.

APPROVED_AS_PARTIAL_CONSTRUCTION_INVARIANT. The state stores the actual full graph and an already-completed finite permitted history. Original edge injection and endpoint projection retain indexed original edges and their reversal choices. The active graph includes used original edges and inserted auxiliary edges; its acyclicity and input/output reachability are local invariant fields. They are not the full final DAG conclusion, because every unused original edge remains in the full graph and is excluded from that active relation. The decreasing measure counts only unused original edges. There are no assumed boundary equality or norm fields.

Existence of the initial state, a permitted update whenever original edges remain, strict decrease and final active coverage must be proved. In particular the final public theorem must not accept the existence of this state as an extra caller hypothesis. When used is universal, connectedness and distinct prescribed boundaries imply each original vertex has an incident original edge, making the active set universal; the partial reachability then becomes full reachability. A returned ear must be lifted through the projection with inactive singleton fibers. If an incoming/outgoing split is applied on the full graph, inactive fibers must remain singleton rather than using Bool everywhere.

The independently read DAGSplit, EarInsertion and TotalRank bodies prove valid local operations: strict topological rank excludes directed cycles; lifted old walks and concrete new-path segments give both boundary reaches; finite rank tie-breaking orders distinct endpoints. They do not yet constitute the source's complete modification construction or a proof that every required state transition exists.
