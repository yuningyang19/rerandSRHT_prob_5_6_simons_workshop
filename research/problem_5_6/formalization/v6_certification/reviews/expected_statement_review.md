# Independent expected-statement and source-scope review

Reviewer context: `/root/v6_inventory`, separate from additive proof authors.
Operation: controller-requested source-first inventory and expected-type review.
This is not a final proof verdict, authenticated specialist receipt, release approval, or claim that statements-only modules are proved.

## Frozen inputs and read coverage

C is commit `4551d08f3732a3ca06c2f576794e1d75790e1972`. Main raw SHA256 is `3f140ac21cf98d07371ba81c307db1b272251fabe80fd58f7f290683e8d95286`; included `figures/p7_contraction.tex` is `9df62c726d52766be5996124d3257b751bcbc5116ff770f80f452d6089bddabe`. I read all 3277 main lines, the complete included figure source, inline TikZ, macros, ordinary paragraphs, examples, tables, and embedded bibliography. The only active input is the named figure; the source parser strips comments while retaining source line numbers. Named environments were parsed and individually reviewed; manual interface/definition extraction followed a full sequential reading. A source parser or count alone is not semantic evidence.

A was read directly at `35cc5f146fcddc88d8375cc974ff93585099e220:research/problem_5_6/LaTeX/solution.tex`; its SHA256 was reproduced as `53efe688a3845cc6823d31504c04b471e83cee0371e327168e16742f87465c2c`. The source spans for each named C result are in the named inventory. General cumulant prose and arbitrary-random-frame wording were already present in A; their limited B representation is not evidence that C may be narrowed. The newly named C cumulant, binary and entry-contribution results correspond to A prose/proof interfaces.

B source inspection covered primitive probability/norm/frame/graph/cumulant/partition definitions, all nine named result types, the relevant I01-I42 interface types, the correction report and Gate 3 ledger, and the actual trace-entry/weighted aggregate definitions and selected implementation bodies. This review does not claim a complete B proof reread, axiom closure, compiler verification, or complete independent reverse audit; those belong to the other assigned operations.

## Inventory approval

`EXPECTED_SOURCE_SCOPE: APPROVED_AS_WRITTEN`

- 12 named results, with 30 individually recorded conjuncts.
- 50 additional theorem-strength proof/prose interfaces.
- 34 definitions/notation entries, including all 7 named definitions.

These denominators are frozen before additive proof coverage. Interfaces are connected mathematical source units, not generated Lean helper counts. Each has exact raw source context, lines and SHA256 plus a semantic expected statement and assumptions. Literature/complexity background, repeats, concrete examples, diagrams and bibliography are separately registered and must not inflate kernel coverage. The two figures' sources and example arithmetic were read; visual rendering has not been performed by this reviewer. Source-numbered labels are stable; numeric typeset result/equation numbers await the controller's compiled-C reconciliation.

## Exact expected-type approvals

`FixedFrameExpected.lean` SHA256 `7a060c21c36812f6acfc0cb1f10e462605d81626f4ac2fbe6960b428c80deff1`: **APPROVED for proof generation**. `FixedFrameOSE` chooses universal C and deterministic k before V. Requiring C equal the explicit source constant is an allowed stronger witness. `SquaredNormEdges` writes the outside quantity as norm(Vx)^2; the source writes norm(x)^2. These are equivalent under `OrthonormalFrame V`, so the interpretation theorem must carry that assumption and prove/use isometry. Rank positivity and nonempty frame/sample classes, probability normalization and the custom L2 norm must be checked by the client proof; they cannot be inferred from names.

`GeneralCumulantsExpected.lean` SHA256 `e455d314ba827a7be386fb256a5041c54e625435c95bd44fcce49dcd5e1fc1e0`: **APPROVED for proof generation**. The six Props have arbitrary probability measure, real scalar variables, all required occurrence-subset products integrable, real multilinearity, independence of two vectors of variables, shift invariance at order at least two, and odd-order symmetry via equality in distribution. Empty-product integrability follows from the probability-space hypothesis. Distinct occurrences may hold the same random variable. There is no exponential moment or finite/uniform sample-space restriction. These types preserve the paper's general domain. They assert no theorem/axiom.

No sampling expected module was available at this review point. An integral over an arbitrary frame law of the finite sampling failure probabilities, together with a proved independence/joint-law bridge, is the accepted intended direction. Its exact type still needs independent review.

## Scope mismatches and necessary correspondence work

1. **General cumulants: NEW_FORMALIZATION.** B I08/I09/I10 use finite uniform probability and I10 product coordinate factors. They do not prove the six general claims. General scalar field is read as real from this real paper's context; no unexplained switch to complex or moment-generating convergence is permitted. Independent groups means independent vectors, not pairwise independent variables.

2. **General random frame: NEW_FORMALIZATION.** B `fixed_size_sampling_transfer` has `[Fintype Ω] [Nonempty Ω]` with a uniform average. C explicitly allows arbitrary independent random X. Uniform finite X and deterministic X are useful specializations but do not close C. The written continuous-uniform proof and B finite coupling may be valid alternative proofs; their identities should not be conflated.

3. **Graph orientation: WRAPPER_ONLY after checked bridge.** C uses target row/source column, while B `graphContraction`, `graphOperator` and its edge family use source row/target column. Transpose every matrix and boundary matrix, preserving operator norms; rank projection transpose is itself. Loops, parallel occurrences, rectangular endpoint dimensions, vertex weights and distinct boundaries must survive. C's boundary operator is defined by a finite sum before DAG hypotheses; never put its norm bound into a definition field.

4. **General bridgeless conversion: unresolved wider interface.** C main lines 930-936 state connected bridgeless conversion for arbitrary such graphs and prescribed distinct boundaries. B I05 additionally assumes positive even degrees. This is sufficient at the rank-contraction application, but not an exact formalization of the broader prose. Source-interface verification of Mingo--Speicher's actual lemma and/or a faithful general proof is required. This reviewer has not checked that external source and does not call the broader assertion false.

5. **Boundary preservation is stronger than scalar-sum preservation.** C lines 938-970 claim preservation of every boundary entry under the explicitly prescribed modifications with labels fixed. B I05 only concludes preservation of the full sum and boundary dimensions. Check actual split/fiber theorems, or prove the finite-sum bridge; do not infer entrywise preservation from scalar equality.

6. **Exact weighted partition sum matches; all-parameter extension pending.** B `AggregateEntryPartition` and `entryPartitionCumulantConstant` encode the actual admissible class and c(rho)=product(2 card B)^(12 card B), not an unweighted or differently normalized count. But C quantifies all d,h≥0; I28 requires d≤p−1. When d≥p, the class is empty because 2p>0 forces at least one block, and the extension must prove that fact before returning zero. The constraint t≤12d+4h is required only for nonempty classes. The dimension-factor lemma needs d≤p and h≤p−s, derived from nonemptiness; never use truncated natural subtraction as integer subtraction without those guards.

7. **Per-class absolute contribution.** C's second entry-contribution clause fixes d,h and sums absolute cumulant products over the injective row labels. B's private `selectorEntryContribution_abs_sum_le_aggregateBound` sums all d,h and takes absolute values outside its inner partition sum. It is not alone a direct matching target. Earlier per-partition absolute-label estimates support a faithful additive fixed-class bridge. They may be reused without editing B, but must be exposed through an actual checked theorem.

8. **Support definition differs harmlessly but needs inclusion, not equality.** B `disjointPairRows` selects every constraint row of weight four, including a possible large block, whereas C's U is the support union of disjoint pair rows. The latter is contained in the former, and both have the needed ≤4h support bound by a basis argument. A literal identification is wrong; a proved inclusion or direct pair-row definition is faithful.

9. **Binary lemma has all clauses.** Exact unrestricted label count is already expressed generally by `entryXorConstraintSolutionCount`; I22 alone expects an h-row full-rank matrix and would need a basis reduction. Forbidden pairs must vanish under injectivity before relaxing to unrestricted labels. Necessity is not sufficiency. Both pair obstructions, exact count, injective bound and t inequality remain in the denominator.

10. **Transfer and main theorem.** Delta in the deterministic transfer is an independent parameter, not necessarily r/n; scalar endpoints, complementary ker-P space and nonreal roots remain required. The trace statement has absolute value outside expectation. Fixed frame quantifiers, both squared edges, exact independent two-sign Walsh law and without-replacement uniform sample cannot be altered.

## Source and written-proof findings

No false named statement or minimal necessary manuscript repair was established in this bounded review. This is not a final `NO_REPAIRS` verdict: external Mingo source verification, complete written-proof reverse audit and actual additive correspondence remain pending. The complete C elementary two-projection expansion, ordered-partition coefficient reasoning, count code description, weighted constants, XOR argument, finite-population fourth moments and final arithmetic were read. I found no obvious arithmetic inconsistency in those passages. The p=2 examples and p=7 word/code/transitions are consistent with their stated counts; they are examples, not kernel-certified general results.

The source expected inventory is approved independently of implementation authors. Actual implemented-type equality, proof dependency/axiom closure, final independent forward/reverse acceptance and workflow prerequisites must be supplied separately. No historical PASS was copied as current proof evidence.

## Inventory file hashes at review freeze

- `inventory_definitions.json`: `4a4c69da398d7077d3e5b134501086fb48353265a32444b5c55d797308fda10e`
- `inventory_interfaces.json`: `6ac8641a027876cc13de6d5ab50850c8add7370abd774671bcf847ebc2a6c0e0`
- `inventory_named_results.json`: `fe3324f58e323d6fd878f52e692dbe02abf38f1cf622f300f58a0c222f8285ef`

## Additive expected graph/entry freeze

The subsequently controller-requested `GraphAndEntryExpected.lean` is frozen at SHA256 `1e0a265df84ba4d117cfc8212db8f7b75ecf5ae31e5efa07586ed7b6c25edfb9`. Nine definition-only Props preserve target-row/source-column graph orientation, explicit source/sink DAG conditions, boundary sum, graph rank/operator bounds, both forbidden pair types, exact/injective kernel counts, odd-incidence bound, all-d,h weighted class count and fixed-class absolute contribution. It elaborated with exit 0 and is approved for independent proof generation. See `written_proof_source_review.md`; no proof was authored by this reviewer.
