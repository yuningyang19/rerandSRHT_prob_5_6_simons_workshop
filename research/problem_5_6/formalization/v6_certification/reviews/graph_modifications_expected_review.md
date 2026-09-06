# Additional expected graph modifications, I-V6-11

Reviewer: /root (controller; not the graph implementation author).
Source: frozen C main.tex 938–970, plus definitions 882–908.

GraphModificationsExpected.lean was written and source-reviewed before graph
proof generation. FiberBoundaryExpected fixes arbitrary selected copies of
the two distinct original boundary vertices. The identity-edge constraints
must give equality entry by entry with the original boundary matrix.
ReversalBoundaryExpected reverses selected edges and transposes their
matrices, preserving the same boundary labels. Both retain rectangular
endpoint dimensions and finite loops/parallel edges. They are deliberately
stronger than scalar contraction equality, as the written paragraph requires.
They are expressed in B orientation; GraphOrientationExpected supplies the
explicit transpose to C orientation. Neither proposition assumes a norm
bound or its own conclusion. Expected-type elaboration PASS is recorded in
logs/graph_expected.execution.json. Scope APPROVED for additive implementation.
Positive-dimensional identity operators have norm one, supporting C's exact
norm product preservation; B's weaker zero-dimensional ≤ convention remains
valid outside C's positive-dimensional context. No manuscript edit authorized.
