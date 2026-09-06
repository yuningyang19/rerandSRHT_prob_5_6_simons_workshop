import Problem56.Statements
import Mathlib.Util.PrintSorries

/-!
Machine-readable Gate 3 dependency and axiom audit commands.

Each output row is derived from the elaborated declaration value in the Lean
environment.  `DIRECT` lists constants in the `Problem56` namespace that occur
in the declaration's own proof term; `AXIOMS` is Lean's transitive
`collectAxioms` result.  This is intentionally separate from the planned
mathematical DAG in `dependency_manifest.json`.
-/

open Lean Elab Command

private def declarationValueConstants (ci : ConstantInfo) : Array Name :=
  match ci with
  | .defnInfo v => v.value.getUsedConstants
  | .thmInfo v => v.value.getUsedConstants
  | .opaqueInfo v => v.value.getUsedConstants
  | _ => #[]

private def problem56Constants (ci : ConstantInfo) : Array Name :=
  declarationValueConstants ci |>.filter fun n =>
    n.toString.startsWith "Problem56."

private def problem56Theorems (env : Environment) (ci : ConstantInfo) : Array Name :=
  problem56Constants ci |>.filter fun n =>
    !n.toString.contains "._proof_" &&
      match env.find? n with
      | some (.thmInfo _) => true
      | _ => false

private def renderNames (names : Array Name) : String :=
  String.intercalate "," <| (names.qsort Name.lt).toList.map Name.toString

elab "#audit_problem56 " n:ident : command => do
  let name ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo n
  let env ← getEnv
  let some ci := env.find? name
    | throwError "unknown declaration {name}"
  let constants := problem56Constants ci
  let direct := problem56Theorems env ci
  let axioms ← Lean.collectAxioms name
  logInfo m!"AUDIT|{name}|DIRECT_THEOREMS|{renderNames direct}|PROBLEM56_CONSTANTS|{renderNames constants}|AXIOMS|{renderNames axioms}"

namespace Problem56

#audit_problem56 I01_walsh_card
#audit_problem56 I01_walsh_symmetry
#audit_problem56 I01_walsh_involution
#audit_problem56 I02_exact_gram_reduction
#audit_problem56 I03_full_sample_exact
#audit_problem56 I04_mingo_speicher_graph_operator_specialization
#audit_problem56 I05_mingo_speicher_bridgeless_conversion
#audit_problem56 I06_connected_even_multigraph_has_no_bridge
#audit_problem56 I07_rank_edge_factorization_bound
#audit_problem56 I08_moment_cumulant_inverse
#audit_problem56 I09_product_cumulant_connected_partition_identity
#audit_problem56 I10_independent_families_mixed_cumulant_vanish
#audit_problem56 I11_projection_entry_expansion
#audit_problem56 I12_occurrence_partitions_form_connected_even_graph
#audit_problem56 I13_rademacher_cumulant_bound
#audit_problem56 I14_walsh_translation_modulation
#audit_problem56 I15_projection_mean_and_centering
#audit_problem56 I16_selector_quotient_degree_excess
#audit_problem56 I17_centered_bernoulli_moment_bound
#audit_problem56 I18_exceptional_vertex_degree_budget
#audit_problem56 I19_degree_four_classification_and_loop_bound
#audit_problem56 I20_contracted_core_encoding_bound
#audit_problem56 I21_euler_transition_count
#audit_problem56 I22_xor_kernel_solution_count
#audit_problem56 I23_pointwise_vanishing_pair_classification
#audit_problem56 I24_large_block_and_support_rank_bound
#audit_problem56 I25_large_block_partition_constant_bound
#audit_problem56 I26_disjoint_pair_support_bound
#audit_problem56 I27_loop_parallel_pairing_bound
#audit_problem56 I28_aggregate_partition_cumulant_bound
#audit_problem56 I29_exact_dimension_factor
#audit_problem56 I30_trace_geometric_summation
#audit_problem56 I31_two_projection_block_decomposition
#audit_problem56 I32_quadratic_root_even_power_bound
#audit_problem56 I33_bad_spectral_edge_large_root
#audit_problem56 I34_bernoulli_failure_arithmetic
#audit_problem56 I35_uniform_key_nested_coupling
#audit_problem56 I36_sampling_sandwich_spectral_conversion
#audit_problem56 I37_binomial_tail_bounds
#audit_problem56 I38_finite_population_second_moment_identity
#audit_problem56 I39_rademacher_vector_fourth_moment
#audit_problem56 I40_operator_norm_le_frobenius
#audit_problem56 I41_large_rank_cutoff_arithmetic
#audit_problem56 I42_final_width_constant_assembly

#audit_problem56 graph_rank_contraction
#audit_problem56 joint_entry_cumulant_lemma
#audit_problem56 selector_equality_graph_count
#audit_problem56 signed_trace_proposition
#audit_problem56 two_projection_spectral_transfer
#audit_problem56 bernoulli_coordinate_sampling_corollary
#audit_problem56 fixed_size_sampling_transfer
#audit_problem56 small_rank_second_moment
#audit_problem56 main_universal_ose

end Problem56
