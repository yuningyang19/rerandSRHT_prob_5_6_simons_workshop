# Required source clarification for the unchanged frozen snapshot

**I-V6-11: generic coordinate dimensions.** Frozen C is commit
`4551d08f3732a3ca06c2f576794e1d75790e1972`, main SHA256
`3f140ac21cf98d07371ba81c307db1b272251fabe80fd58f7f290683e8d95286`.
No TeX changes were applied.

The triangle explicitly uses positive dimensions (line 818), but the generic
graph definition (lines 849–865) does not explicitly retain that convention.
The generic vertex-splitting prose (lines 958–969) asserts identity norm one
and equality of edge-norm products. Under a reading permitting zero-dimensional
coordinate spaces, the first assertion fails: the operator norm of the identity
on the zero space is zero. The generic product assertion can also fail if an
isolated zero-dimensional vertex is split.

A concrete product example has vertices s,t,z with dimensions 1,1,0, an identity
edge s→t, and isolated z. The original norm product is 1. Splitting z and adding
an identity edge of dimension zero changes the product to 0. The boundary
matrix remains zero. This is an ambiguity in the stated generic scope; it is
not a counterexample to the connected graph bound or the paper's main theorem.
For a connected graph with distinct boundary vertices, a zero-dimensional
vertex already forces an incident zero-norm edge and hence a zero product.

## Minimal proposed TeX clarification — not applied

In `def:graph-contraction`, replace lines 855–856 by:

```tex
allowing parallel edges and loops. Each vertex $u$ has a positive integer
coordinate dimension $N_u$ and a range $\{1,\ldots,N_u\}$ from which
its label $i_u$ is chosen,
```

This makes the intended convention explicit and agrees with the earlier
triangle and the positive dimensions n and r used in the application. A future
edit must receive a new snapshot binding and affected-scope recheck. The current
task does not apply the proposed edit or certify that future snapshot.

## Executed evidence and current Lean scope

`probes/ZeroDimensionIdentity.lean` was compiled by the pinned Lean compiler;
`logs/zero_dimension_identity_witness.execution.json` records the successful
command. It instantiates the already audited
`Problem56.GraphOperatorRegression.zero_dimensional_domain_has_zero_norm`
at the zero-dimensional identity and proves its norm is not one.

`rooted_elementary` and `rooted_history` prove every boundary entry is preserved
and the norm product does not increase for arbitrary natural dimensions.
They separately prove preservation of positivity and exact product equality
for positive dimensions. No unsupported positivity premise was silently added
to an allegedly unconditional manuscript claim.

Independent source-first pass 2 classifies this issue as RA3 / REPAIR. The frozen
50-interface denominator is retained; I-V6-11 is not counted as unconditionally
covered. No other necessary manuscript correction has been identified in the
completed reviews. The general graph construction, formal logarithm, continuous
coupling, and introductory trace/centering bridges were repaired in additive
Lean modules without editing the manuscript.
