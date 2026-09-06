# Independent intended-type review

Reviewer `/root/baseline_audit`; target `Problem56/PaperV6/FixedFrameExpected.lean`; SHA256 `7a060c21c36812f6acfc0cb1f10e462605d81626f4ac2fbe6960b428c80deff1`.

**Intended definitions APPROVED.** This is approval of expected semantic targets before implementation, not proof certification.

- `FixedFrameOSE`: constant and width precede the universal fixed frame; the correct frame orthonormality is an assumption; the failure bound is a conclusion, not an assumption. The explicit constant equality is a stronger witness consistent with the C existence claim.
- `SquaredNormEdges`: one realized draw quantifies over every x in Fin r→ℝ and includes both edges. Its reference quantity is ‖Vx‖². For the intended client with `hV : OrthonormalFrame V`, this equals ‖x‖², so it is equivalent to C's displayed interpretation. The definition does not assume its own conclusion or any probability guarantee.
- Intended client `fixed_frame_ose : FixedFrameOSE`: APPROVED target. It must derive boundedness of the supremum set, not assume it.
- Intended deterministic client `hV → euclideanOperatorNorm (compressedGram V d₁ d₂ J - 1) ≤ ε → SquaredNormEdges ε V d₁ d₂ J`: APPROVED target, for arbitrary instantiated dimensions and fixed subset. The displayed probability conclusion follows for the main valid parameter range.
- C says the complementary event says *precisely* the squared inequalities. A forward implication alone proves the guarantee but does not completely encode this equivalence. A reverse implication can be proved from symmetry of compressedGram−I and the quadratic-form norm characterization; record as open unless supplied.

No implementation proof was read as evidence in making this approval. Final independent implementation review and axiom/build evidence remain required.

## Additional approved targets

The controller's proposed `squared_edges_iff_spectral_bound` under ε≥0 and hV is approved: it establishes both directions of C's event interpretation. The proposed success-probability conclusion ≥99/100 with the same width chosen before every fixed V is approved, provided the positive finite sample normalization is proved from k≤n and the main width range. The reviewer read the initial FixedFrame.lean implementation and found the supremum bound, Gram quadratic-form identity, frame isometry, and forward edge implication faithful to the approved targets; final dependency/axiom auditing remains separate.
