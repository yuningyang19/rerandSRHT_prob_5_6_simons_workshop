# General bridgeless conversion: additive preparation

This work addresses frozen C main.tex 930–936 and the modification explanation
through line 970. The primary published source is Mingo–Speicher, Lemma 16,
pp. 2286–2287; the locally supplied PDF is extracted in
`reviews/mingo_published_extraction.txt`, lines 786–834. Existing B's
`GraphBridgelessConversion.lean` is unchanged.

## Frozen targets and independent review

`PaperV6/GeneralBridgelessExpected.lean` defines
`EveryEdgeDeletionConnected` by undirected connectivity on the indexed-edge
subtype excluding one specified edge. This keeps loops and parallel edges and
does not assume even degree. `GeneralBridgelessConversionExpected` states the
rectangular DAG operator consequence, with individually preserved boundary
entries and a concluding norm-product bound. It is a proposition, not an axiom
or a proved theorem. The independent inventory reviewer accepted it as
**APPROVED_AS_CONSEQUENCE_ONLY**: it cannot replace the literal finite-modification
claim in I-V6-10.

`PaperV6/GeneralBridgelessModifications.lean` separately defines finite graph
data and concrete selective reversal/transposition and rooted identity-edge
splitting operations. `ElementaryBoundaryModification` has only those
constructors; `BoundaryModification` is their reflexive transitive closure.
No constructor accepts a boundary equality, norm bound, or DAG certificate.
The expected existence proposition uses primitive connectedness, every-edge
deletion connectedness, and prescribed distinct boundaries. The independent
inventory reviewer accepted this as
**APPROVED_AS_LITERAL_CONSTRUCTION_EXPECTATION**. A rooted star split is an
explicit finite macro of the permitted binary splits. Neither expected
proposition has been supplied with a general conversion proof.

## Concrete general-scope proof preparation

The new modules contain the following proof candidates; their authoritative
compiler and axiom results are recorded by the controller's serialized build,
not inferred from this report.

- `GeneralBridgelessPaths.exists_first_hit_walk`: stop a relational walk at
  its first old vertex, so every retained step starts outside the old set.
- `GeneralBridgelessPaths.exists_unused_return_walk`: deleting the entering
  edge leaves a route to the old graph; stopping it at first contact excludes
  all already used edges, because both endpoints of each used edge are old.
- `GeneralBridgelessSimplePaths.exists_simple_chain_of_walk`: delete cycles
  by truncating to a suffix when a newly prepended vertex already occurs.
  This works for arbitrary relations, without symmetry or finite ambient type.
- `GeneralBridgelessSimplePaths.exists_simple_unused_return_path`: a simple
  return path avoiding both the entering edge and every already used edge.
- `GeneralBridgelessEars.exists_unused_edge_at_old_vertex`: connectivity and
  the existence of an unused edge imply that a fresh edge touches the nonempty
  old graph.
- `GeneralBridgelessEars.exists_fresh_ear_path`: combine the last two results
  into the published construction's actual ear-selection step. Its primitive
  hypotheses contain no parity, routing, norm, or desired conversion statement.

The zero-length return when the far endpoint is already old is retained. This
includes an original loop, whose eventual insertion needs the coincident-endpoint
split. The simple path is represented by a vertex list with an existential
indexed-edge witness at each step; selecting these witnesses into a distinct
oriented-edge list remains a representation bridge for an insertion engine.

## Exact remaining construction

The outstanding target is `GeneralBridgelessModificationExpected`, not the
name of a missing library theorem. A faithful shortest route is:

1. Start with a simple path from the prescribed input to output, using the
   generic simple-chain theorem and original connectedness.
2. Maintain a partial input-output DAG using a subset of the original indexed
   edges, plus identity edges from prior splits; retain an explicit mapping of
   each copy to its original vertex and a finite modification history for the
   full graph. Vertices outside the active original vertex set remain unsplit.
3. Use `exists_fresh_ear_path` on the original graph and the used original edge
   set. Lift its first and last incidences to their current vertex copies; its
   internal original vertices are fresh and require no ambiguous copy choice.
4. For distinct lifted endpoints, orient the ear in an order compatible with
   reachability in the old DAG. Prove no directed cycle is introduced and every
   new vertex remains between the same input/output boundaries.
5. For coincident lifted endpoints, split that current vertex into two copies:
   old incoming edges attach to the first, old outgoing edges to the second,
   an identity edge and the new ear run from first to second. Update a marked
   input to the first copy and a marked output to the second copy when relevant.
   Prove acyclicity and both boundary reachability conditions. Track untouched
   edge incidences explicitly rather than silently moving them between copies.
6. Induct on the number of unused original edges, which strictly decreases;
   added identity edges must not be counted as new unfinished original edges.
   The final finite history yields the literal conversion theorem.

The proof of steps 2, 4–6 and the indexed-edge-list bridge has not been supplied.
The old Euler two-path construction cannot fill these obligations: connected
bridgeless graphs can have odd-degree vertices, while an Euler circuit requires
even degree. Adding identity loops changes degrees by two and does not repair
that mismatch. Replacing primitive bridgelessness with an assumed DAG routing
would merely restate the missing construction and is not done here.

For a subsequent full operator consequence, compose reversal and **root-pruned**
split boundary-preservation lemmas over the finite history. The existing new
fiber-boundary theorem uses the unpruned fiber operation, so an explicit bridge
is still required. Norm products satisfy the requested weak inequality even
with zero dimensions; the published exact equality is recovered under positive
vertex dimensions, when inserted identities have norm one. These preservation
results do not by themselves prove the general history-existence target.

No part of this preparation labels I-V6-10 kernel closed, calls the general
published citation formally verified, changes the frozen manuscript, or
weakens the original inventory denominator.
