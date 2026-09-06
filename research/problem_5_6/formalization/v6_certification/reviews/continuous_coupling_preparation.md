# Continuous uniform common-order coupling preparation

Frozen C source: `main.tex:2774–2789`, with context starting at 2770. The
manuscript takes independent continuous uniform keys on [0,1], orders them to
choose the k smallest, thresholds the same keys, and invokes a count-conditional
set sandwich. This obligation is distinct from the finite alternative proof.

The definitions-only intended target is
`Problem56.PaperV6.ContinuousCouplingExpected`. Its primitive noise measure is
the finite product of `volume.restrict (Set.Icc (0 : ℝ) 1)`. It requires the
actual independent uniform coordinate laws, almost sure injectivity of keys,
and a measurable choice of the k smallest values. The choice's tie fallback
must still respect the weak key ordering. Uniform k-subset and Bernoulli
product laws are conclusions, never hypotheses. The two thresholds share one
key vector. Inclusions require their two count inequalities. Both threshold
endpoints and k=0,n are included.

The root independently approved this target in a separate agent context.
Definitions-only elaboration passed in
`logs/log_coefficients_continuous_expected.log:373` (12 seconds). Expected
module SHA256:
`ddd5f2c19de0c4d96c67c1df277c09884b70941a192b00cac28b92484f344ace`.

The implementation first minimizes the sum of the selected keys over the
finite family of k-subsets. Exchanging a selected larger key for an unselected
smaller key proves that an ordered subset exists. Measurability is obtained
by enumerating that finite family and taking the first subset satisfying the
measurable finite set of ordering comparisons; this supplies the tie fallback.
Order plus cardinality proves both count-conditional inclusions without any
no-tie assumption.

The diagonal in two uniform coordinates has zero product measure, by the
section formula for product measures and the atomless restricted Lebesgue
law. Actual coordinate independence then gives almost sure injectivity of the
finite key vector. An ordered k-subset is unique on this full-measure event.
Equivalences between two k-subsets and their complements extend to a
permutation of the index type. `measurePreserving_piCongrLeft` proves
permutation invariance of the continuous product law. Thus every ordered
k-subset event has the same probability. Its almost-everywhere equality with
the chosen sampler fiber, and the sum of all fiber probabilities being one,
give the exact uniform fixed-size marginal.

Threshold marginals are products of the Lebesgue masses of `[0,θ]` and
`(θ,1]`, identified with the literal B `bernoulliWeight` including θ=0,1. A
canonical product with any frame law provides independence through pinned
Mathlib `indepFun_prod`. The separate proved
`continuousKey_frame_marginal` uses `Measure.map_fst_prod` and unit key mass
to preserve the original frame-space law; it should be included in the
combined axiom audit even though it is not a proof dependency of the final
conjunction.

`ContinuousCouplingBasics.lean` compiled successfully in
`logs/active_state_log_inverse_continuous_basics.log:751` (12 seconds), source
SHA256 `6152c491073252c927efe3cfe75025d0d852e86efdb5fd97ed9755c68bf02730`.
It proves probability normalization, coordinate uniformity/independence,
threshold measurability and complete Bernoulli joint atom probabilities, plus
frame marginal preservation and frame/noise independence on the canonical
product. The named batches include unrelated failures; only these component
successes are claimed here.

**The complete continuous-coupling target compiled successfully.**
`ContinuousCouplingNoTies` and `ContinuousCouplingSelection` passed in
`logs/ear_activation_continuous_iteration8.log:218–219` (12 seconds each).
The assembled theorem `Problem56.PaperV6.continuousCoupling`, with literal
type `ContinuousCouplingExpected`, passed in
`logs/continuous_original_ear_audittools_iteration9.log:597` (12 seconds).
The latter batch failed in the unrelated graph-ear module, so no whole-batch
PASS is asserted. Commands and source bindings are in the matching
`.execution.json` records.

Final source SHA256 values (all paths under `lean/Problem56/PaperV6/`):

| File | SHA256 |
|---|---|
| `ContinuousCouplingExpected.lean` | `ddd5f2c19de0c4d96c67c1df277c09884b70941a192b00cac28b92484f344ace` |
| `ContinuousCouplingBasics.lean` | `6152c491073252c927efe3cfe75025d0d852e86efdb5fd97ed9755c68bf02730` |
| `ContinuousCouplingNoTies.lean` | `4ef424db7bdae7175fe5180c389c05d6566ca38452b37bc9613a3c3acbb8908d` |
| `ContinuousCouplingSelection.lean` | `de4b25b5686db644a88a1e4161c7b2468fbf2ffbd739500ce771b89a5dcd28a9` |
| `ContinuousCoupling.lean` | `fa573de308d63d2b4f7f8498544b4977f2b6f923e502f5e4977a1be660101f7f` |

The expected statement remains byte-identical to its approved hash in
`reviews/continuous_coupling_expected_review.json`. No B proof, build file,
manuscript, prior expected statement, or other worker's source was changed by
this worker. All source proof terms are complete; failed elaborations and their
compiler diagnostics are preserved in the earlier iteration logs.

Independent implementation correspondence, the fail-closed transitive axiom
audit, combined clean build, and replay remain controller/auditor operations.
No finite-law surrogate is counted as the literal continuous construction, and
this worker does not self-sign any independent acceptance verdict.

EVIDENCE_STATUS_AT_RETURN: UNCHANGED
