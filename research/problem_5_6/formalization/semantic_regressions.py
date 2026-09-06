#!/usr/bin/env python3
"""Gate-1 source-structure regressions for the frozen public semantics.

These tests are guards against obvious signature drift.  They are not a
substitute for the independent correspondence audit.
"""

from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[3]
DEFS = (ROOT / "research/problem_5_6/formalization/lean/Problem56/Definitions.lean").read_text()
STMTS = (ROOT / "research/problem_5_6/formalization/lean/Problem56/Statements.lean").read_text()
GRAPH = (ROOT / "research/problem_5_6/formalization/lean/Problem56/GraphOperatorL2.lean").read_text()
EXTRACTION = (ROOT / "research/problem_5_6/formalization/lean/Problem56/ExtractionRegression.lean").read_text()
RANK_CUT = (ROOT / "research/problem_5_6/formalization/lean/Problem56/RankCutStateFactorGeneral.lean").read_text()
THREE_CATEGORY = (ROOT / "research/problem_5_6/formalization/lean/Problem56/ThreeCategoryOrderCoupling.lean").read_text()
GRAPH_RANK_SPLIT = (ROOT / "research/problem_5_6/formalization/lean/Problem56/GraphRankEdgeSplit.lean").read_text()
GRAPH_BRIDGELESS = (ROOT / "research/problem_5_6/formalization/lean/Problem56/GraphBridgelessConversion.lean").read_text()
JOINT_ENTRY = (ROOT / "research/problem_5_6/formalization/lean/Problem56/JointEntryCumulant.lean").read_text()
SIGNED_TRACE_SUM = (ROOT / "research/problem_5_6/formalization/lean/Problem56/SignedTraceSummation.lean").read_text()
TRACE_CYCLIC = (ROOT / "research/problem_5_6/formalization/lean/Problem56/TraceCyclicExpansion.lean").read_text()
SIGNED_TRACE_EXPECTATION = (ROOT / "research/problem_5_6/formalization/lean/Problem56/SignedTraceExpectationExpansion.lean").read_text()
SIGNED_TRACE_ENTRY = (ROOT / "research/problem_5_6/formalization/lean/Problem56/SignedTraceEntryCumulant.lean").read_text()
SIGNED_TRACE_MOMENT = (ROOT / "research/problem_5_6/formalization/lean/Problem56/SignedTraceMomentExpansion.lean").read_text()
SIGNED_TRACE_EXPANSION = (ROOT / "research/problem_5_6/formalization/lean/Problem56/SignedTraceExpansion.lean").read_text()
CORE_REALIZATION = (ROOT / "research/problem_5_6/formalization/lean/Problem56/ContractedCoreCanonicalRealization.lean").read_text()
CORE_CARD = (ROOT / "research/problem_5_6/formalization/lean/Problem56/ContractedCoreCanonicalCard.lean").read_text()
CORE_ZERO = (ROOT / "research/problem_5_6/formalization/lean/Problem56/ContractedCoreZeroParameter.lean").read_text()
CORE_CLOSURE = (ROOT / "research/problem_5_6/formalization/lean/Problem56/ContractedCoreEncodingClosure.lean").read_text()

CORPUS = (DEFS + STMTS + GRAPH + EXTRACTION + RANK_CUT + THREE_CATEGORY
          + GRAPH_RANK_SPLIT + GRAPH_BRIDGELESS + JOINT_ENTRY
          + SIGNED_TRACE_SUM + TRACE_CYCLIC + SIGNED_TRACE_EXPECTATION
          + SIGNED_TRACE_ENTRY + SIGNED_TRACE_MOMENT + SIGNED_TRACE_EXPANSION
          + CORE_REALIZATION + CORE_CARD + CORE_ZERO + CORE_CLOSURE)


def require(*needles: str) -> None:
    missing = [needle for needle in needles if needle not in CORPUS]
    if missing:
        raise SystemExit("missing frozen semantic marker(s): " + repr(missing))


tests = {
    "R-MAIN-QUANTIFIERS": lambda: require(
        "∃ C : ℕ, C = explicitUniversalConstant ∧ 1 ≤ C ∧",
        "∀ (m r : ℕ) (ε : ℝ)",
        "∃ k : ℕ", "spectralFailureSup m r k ε ≤ 1 / 100"),
    "R-EXACT-RANDOM-LAW": lambda: require(
        "SignLayer (WalshIndex m) ×", "FixedSubset (WalshIndex m) k",
        "uniformProbability"),
    "R-MATRIX-ORDER": lambda: require(
        "signDiagonal d₁ * normalizedWalsh m * signDiagonal d₂",
        "normalizedWalsh m * signDiagonal d₂ * normalizedWalsh m * signDiagonal d₁ * V"),
    "R-BOTH-SPECTRAL-EDGES": lambda: require(
        "euclideanOperatorNorm", "compressedGram V", "> ε"),
    "R-SIGNED-TRACE": lambda: require(
        "|signBernoulliExpectation θ", "Matrix.trace", "^ (2 * p)"),
    "R-I35-CONDITIONAL-COUPLING": lambda: require(
        "sample.2.1 i = true → sample.2.2 i = true",
        "card ≤ k ∧", "k ≤ (Finset.univ.filter",
        "i35_unconditional_support_conflict"),
    "R-I16-I19-MOMENT-SCOPE": lambda: require(
        "theorem I16_selector_quotient_degree_excess", "(hp : 2 ≤ p)",
        "theorem I19_degree_four_classification_and_loop_bound",
        "i16_empty_selector_counterexample", "i19_two_loop_endpoint_counterexample"),
    "R-I08-NONEMPTY": lambda: require(
        "I08_moment_cumulant_inverse", "[Fintype Ω] [Nonempty Ω]",
        "i08_empty_boundary_conflict"),
    "R-L2-NORM-SCOPE": lambda: require(
        "open scoped BigOperators Matrix Matrix.Norms.L2Operator",
        "euclideanOperatorNorm_eq_l2_opNorm", "Matrix.l2_opNorm_def"),
    "R-GRAPH-ORIENTATION": lambda: require(
        "euclideanOperatorNorm_transpose", "Matrix.l2_opNorm_conjTranspose",
        "graphOperator_eq_one_of_eq_endpoints"),
    "R-I04-ADJACENT-RANK-CUT": lambda: require(
        "endpointAwareRankCutState_factor_all",
        "endpointAwareRankCutStepFactorization_all",
        "graphOperator_norm_le_edge_product_of_exists_zero_dim",
        "theorem mingo_speicher_graph_operator_specialization"),
    "R-I35-THREE-CATEGORY-ORDER": lambda: require(
        "inductive Category where",
        "threeCategoryOrderCoupling_fixedSubset_marginal",
        "threeCategoryOrderCoupling_lower_marginal",
        "threeCategoryOrderCoupling_plus_marginal",
        "uniform_key_nested_coupling_via_three_category"),
    "R-I07-RANK-EDGE-SPLIT": lambda: require(
        "theorem graphContraction_rankEdgeSplit",
        "theorem graphConnected_rankEdgeSplit",
        "theorem graphDegree_rankEdgeSplit_old",
        "theorem hasRankProjectionEdge_factorization",
        "theorem rankEdgeSplitMatrix_norm_le_one"),
    "R-I05-BRIDGELESS-DAG": lambda: require(
        "theorem exists_weightLoop_twoPathCover",
        "theorem twoPath_mingoAdmissibleDAG",
        "theorem graphContraction_reindex",
        "theorem graphMatrixNormProduct_reindex",
        "theorem mingo_speicher_bridgeless_conversion"),
    "R-JOINT-ENTRY-REINDEX": lambda: require(
        "theorem hasJointEntryOccurrenceExpansion",
        "fullLabelPartitionSum_eq_occurrenceDataSum",
        "occurrenceDataSum_eq_evenOccurrencePairSum",
        "theorem joint_entry_cumulant_assembly"),
    "R-SIGNED-TRACE-SUMMATION": lambda: require(
        "theorem signedTrace_bound_of_master_geometric_bound",
        "trace_geometric_summation p r hp hr",
        "(K₀ : ℝ) ^ p * base"),
    "R-TRACE-CYCLIC-EXPANSION": lambda: require(
        "theorem matrix_pow_succ_apply_eq_sum_pathWeight",
        "theorem rootedCyclicMatrixMonomial_eq_prod",
        "theorem trace_pow_succ_eq_sum_rootedCyclicMatrixMonomial",
        "theorem trace_centeredSelector_product_pow_expansion"),
    "R-SIGNED-TRACE-EXPANSION": lambda: require(
        "theorem signBernoulliExpectation_trace_centered_product_pow_expansion",
        "theorem signPairExpectation_cyclic_centeredProjection_product_expansion",
        "theorem signBernoulliExpectation_trace_eq_selector_entryPartition_sum",
        "theorem signBernoulliExpectation_trace_eq_partition_cumulant_sum",
        "private theorem signedTrace_abs_le_boundedSelectorData",
        "theorem signedTrace_master_geometric_bound",
        "theorem signedTrace_bound",
        "apply signedTrace_bound"),
    "R-I20-CONTRACTED-CORE-CLOSURE": lambda: require(
        "theorem equalityCanonicalExpandedPortSourceHalfEdge_injective",
        "theorem equalityCanonicalExpandedPort_card",
        "noncomputable def equalityCanonicalSourceRealizationData",
        "theorem zeroParameterCanonicalizationExists",
        "noncomputable def zeroParameterInjection",
        "theorem contracted_core_encoding_bound_closed"),
}


if len(sys.argv) != 2 or sys.argv[1] not in tests:
    raise SystemExit("usage: semantic_regressions.py " + "|".join(tests))
tests[sys.argv[1]]()
print(f"{sys.argv[1]}: PASS")
