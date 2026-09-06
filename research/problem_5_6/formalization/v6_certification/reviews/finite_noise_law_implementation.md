# Finite independent sampling law implementation

Target: `Problem56.PaperV6.finiteNoiseFailureLaw`, with literal type
`Problem56.PaperV6.FiniteNoiseFailureLawExpected`, frozen independently in
`GeneralSamplingExpected.lean`.

Source implementation: `lean/Problem56/PaperV6/FiniteNoiseLaw.lean` (paths here
are relative to `formalization/`). The existing B development and the
reviewer-owned expected definitions are unchanged by this worker.

The proof decomposes the joint event into the disjoint measurable events
`{ω | event (X ω) b} ∩ {ω | S ω = b}` over the finite sampling space. Mathlib's
`IndepFun.measure_inter_preimage_eq_mul` factors each probability; applying
`ENNReal.toReal` and the exact marginal identity replaces the sampling factor
by `q b`. `measureReal_iUnion_fintype` sums the disjoint probabilities.
`integral_finsetSum` and `integral_indicator_const` identify that sum with the
stated real integral. Each indicator is integrable because its support is
measurable and the ambient measure is finite.

This is valid for an arbitrary probability space, finite α, arbitrary frame
size r including zero, and finite sampling type β. It imposes no frame
orthonormality, finite-uniform model for Ω, positivity of a failure threshold,
or probability estimate. The frozen nonnegative/normalized q assumptions are
retained; they are redundant in this identity once all exact marginals are
given. The empty β case is already inconsistent with a random variable into
β on a probability space, and no nonempty β assumption was added.

The two concrete finite laws, Gram-event measurability, and the final sampling
inequality are handled by the controller's separate application modules.

Implementation check status: **target compilation succeeded** in the
controller's serialized `additive_batch6` build. The raw log
`v6_certification/logs/additive_batch6.log:1938` records
`Built Problem56.PaperV6.FiniteNoiseLaw (13s)`; the command and source hashes
are recorded in `v6_certification/logs/additive_batch6.execution.json`.
The batch as a whole failed in other modules, so this is only the stated
module's successful component result.

SHA256 of the compiled implementation:
`15cf98e053c9d0556fd22692448c9a205eed10f827d09628a0c35578c6931399`.
The unchanged reviewer-owned expected module has SHA256
`f7cfcb4cb64fa8e1260b2754b536a76abfa66eb4acc61d4354990c9cb4aba8c6`.

The earlier name-resolution and expression-conversion diagnostics are retained
in `sampling_and_law_iteration1.log` and `sampling_and_entry_iteration2.log`.
They were repaired without changing the target or any hypothesis. No
transitive-axiom, cold-build, or independent correspondence verdict is asserted
in this worker report; those are controller/auditor operations.

EVIDENCE_STATUS_AT_RETURN: UNCHANGED
