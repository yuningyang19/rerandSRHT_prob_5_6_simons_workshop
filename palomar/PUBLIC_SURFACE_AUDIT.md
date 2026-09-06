# Palomar public statement surface

The Comparator configuration selects two existing certified declarations:

| Public declaration | Source scope |
|---|---|
| `Problem56.main_universal_ose` | Frozen v6 Theorem 1: one universal width bound with the supremum over frames outside probability |
| `Problem56.PaperV6.fixed_frame_squared_norm_success` | The fixed-frame interpretation: one draw preserves both squared-norm inequalities for every vector in that subspace |

The full companion continues to contain 12 named results, 50 additional
mathematical interfaces, and 34 definition mappings. Those larger coverage
counts are not counts of separately submitted Palomar declarations.

## Identity and extraction

- Mathematical/evidence source: `93acaadec26c715917c1cf54d22781820a8a20c6`.
- Frozen paper: `f279b6fac180125dce81a82d824da971bb7ae715`.
- Current public companion base: `d0276b4b5bb85e25a43e6f677356dd625a19c1d6`.
- `EXPORT_MANIFEST.json`: 601 byte-preserved inputs, including every exported Lean source.
- `extraction_manifest.json`: exact copied definition and theorem-signature hashes.

`Challenge.lean` imports only Mathlib. It transparently copies the finite Walsh,
sign, coordinate-subset, Gram, Euclidean-norm and uniform-probability definitions
needed by the two conclusions. No definition is left unspecified. Only the two
selected theorem bodies use deliberate `sorry` placeholders.

`Solution.lean` imports `Problem56.PaperV6.FixedFrame`, which already contains
both certified proofs through its dependency closure. It neither restates nor
reproves a theorem. The root Lakefile only adds this public layout and points
`Problem56` at the original nested source directory. The original nested build
files are preserved, and the root toolchain and dependency manifest are exact
copies of their pinned originals.

The copied statements preserve assumptions, quantifiers, conclusion, rate,
sampling model and scope. In particular, C precedes m, r and epsilon; k precedes
V; r is positive; sampling is without replacement; and the first theorem bounds
the supremum of separate frame-failure probabilities. The squared-norm event
quantifies all vectors of one fixed frame. The explicit constant is large and
is not presented as a practically sharp numerical bound.

## Generated declaration compatibility

The source module generates `Problem56.PaperV6.FixedFrameOSE._proof_1`,
a standard nonzero numeral instance used by the value of `SquaredNormEdges`.
The public Challenge reproduces the original module boundary by clearing only
Lean's non-persisted auxiliary-lemma cache before the exact `FixedFrameOSE`
definition. This regenerates the same auxiliary name and value. It does not
add an axiom, modify a declaration, or change typeclass instances. The reset
command is explicitly allowlisted by the extraction checker. Both the local
closure comparison and the pinned Linux Comparator must accept all ordinary
used declarations, including that generated auxiliary. It is not an extra
public result or a definition hole.

## Verification boundaries

The local closure preflight compares the complete used-constant graph in the
trusted local Challenge and Solution environments and rejects forbidden axioms.
The pinned Palomar-compatible Linux workflow separately runs the official
export, provenance, Comparator, Lean-kernel and NanoDa pipeline. A local
preflight does not stand in for that workflow or for service verification.

The existing independent source-to-Lean correspondence record is retained.
This extraction inherits it only through exact statement/definition binding;
it does not assert a new independent human review, originality, or endorsement.
See `STATUS.md` for current operation results and `policy_snapshot.json` for the
live policy and exact verifier revisions used in this operation.
