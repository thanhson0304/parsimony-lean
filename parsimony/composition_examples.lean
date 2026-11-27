import parsimony.reduction_examples

namespace parsimony

namespace counterexamples

def conjunction_part_csp : binary_csp 2 :=
  csp_of_edges 2 [2, 2] [(0, 1, [(0, 0), (1, 0), (1, 1)])] (by decide) (by decide)

theorem conjunction_part_order_is_valid : is_tree_order conjunction_part_csp [0, 1] := by
  decide +kernel

theorem conjunction_part_extension_counts :
    extension_count conjunction_part_csp first_vertex_is_original
        (tuple_of_values conjunction_part_csp first_vertex_is_original ![0, 0]) = 1 ∧
      extension_count conjunction_part_csp first_vertex_is_original
        (tuple_of_values conjunction_part_csp first_vertex_is_original ![1, 0]) = 2 := by
  decide +kernel

theorem conjunction_part_exactly_one_counts (value : ℕ) :
    models_over_tuple conjunction_part_csp first_vertex_is_original all_vertices
        (support_encoding conjunction_part_csp)
        (tuple_of_values conjunction_part_csp first_vertex_is_original ![value, 0]) =
          extension_count conjunction_part_csp first_vertex_is_original
            (tuple_of_values conjunction_part_csp first_vertex_is_original ![value, 0]) ∧
      models_over_tuple conjunction_part_csp first_vertex_is_original all_vertices
        (direct_encoding conjunction_part_csp)
        (tuple_of_values conjunction_part_csp first_vertex_is_original ![value, 0]) =
          extension_count conjunction_part_csp first_vertex_is_original
            (tuple_of_values conjunction_part_csp first_vertex_is_original ![value, 0]) ∧
      models_over_tuple conjunction_part_csp first_vertex_is_original all_vertices
        (min_eo_encoding conjunction_part_csp [0, 1])
        (tuple_of_values conjunction_part_csp first_vertex_is_original ![value, 0]) =
          extension_count conjunction_part_csp first_vertex_is_original
            (tuple_of_values conjunction_part_csp first_vertex_is_original ![value, 0]) ∧
      log_models_over_tuple conjunction_part_csp first_vertex_is_original
        (tuple_of_values conjunction_part_csp first_vertex_is_original ![value, 0]) =
          extension_count conjunction_part_csp first_vertex_is_original
            (tuple_of_values conjunction_part_csp first_vertex_is_original ![value, 0]) :=
  ⟨support_models_over_tuple _ _ _, direct_models_over_tuple _ _ _,
    min_eo_models_over_tuple _ _ _ conjunction_part_order_is_valid _,
    log_models_over_tuple_eq_extension_count _ _ _⟩

theorem conjunction_part_partial_support_counts :
    models_over_tuple conjunction_part_csp first_vertex_is_original first_vertex_is_original
        (partial_support_encoding conjunction_part_csp first_vertex_is_original)
        (tuple_of_values conjunction_part_csp first_vertex_is_original ![0, 0]) = 1 ∧
      models_over_tuple conjunction_part_csp first_vertex_is_original first_vertex_is_original
        (partial_support_encoding conjunction_part_csp first_vertex_is_original)
        (tuple_of_values conjunction_part_csp first_vertex_is_original ![1, 0]) = 3 := by
  decide +kernel

def conjunction_whole_csp : binary_csp 3 :=
  csp_of_edges 3 [2, 2, 1] [(0, 1, [(0, 0), (1, 0), (1, 1)]), (0, 2, [(0, 0)])] (by decide)
    (by decide)

theorem conjunction_whole_counts :
    is_tree_order conjunction_whole_csp [0, 1, 2] ∧
      relation_count conjunction_whole_csp middle_vertex_is_hidden = 1 ∧
      model_count (support_encoding conjunction_whole_csp) = 1 ∧
      model_count (direct_encoding conjunction_whole_csp) = 1 ∧
      model_count (min_eo_encoding conjunction_whole_csp [0, 1, 2]) = 1 ∧
      model_count (partial_support_encoding conjunction_whole_csp middle_vertex_is_hidden) = 1 := by
  decide +kernel

theorem conjunction_whole_log_count : model_count (log_encoding conjunction_whole_csp) = 1 := by
  rw [log_model_count]
  decide +kernel

def ms_part_csp : binary_csp 3 :=
  csp_of_edges 3 [1, 2, 2] [(0, 1, [(0, 0)]), (1, 2, [(0, 0), (0, 1), (1, 1)])] (by decide)
    (by decide)

theorem ms_part_counts :
    is_tree_order ms_part_csp [0, 1, 2] ∧
      relation_count ms_part_csp middle_vertex_is_hidden = 2 ∧
      has_unique_extension ms_part_csp middle_vertex_is_hidden ∧
      model_count (minimal_support_encoding ms_part_csp middle_vertex_is_hidden [0, 1, 2]) = 3 ∧
      models_over_tuple ms_part_csp middle_vertex_is_hidden middle_vertex_is_hidden
        (minimal_support_encoding ms_part_csp middle_vertex_is_hidden [0, 1, 2])
        (tuple_of_values ms_part_csp middle_vertex_is_hidden ![0, 0, 0]) = 1 ∧
      models_over_tuple ms_part_csp middle_vertex_is_hidden middle_vertex_is_hidden
        (minimal_support_encoding ms_part_csp middle_vertex_is_hidden [0, 1, 2])
        (tuple_of_values ms_part_csp middle_vertex_is_hidden ![0, 0, 1]) = 2 := by
  decide +kernel

theorem ms_part_is_not_parsimonious :
    ¬ is_parsimonious ms_part_csp middle_vertex_is_hidden
      (minimal_support_encoding ms_part_csp middle_vertex_is_hidden [0, 1, 2]) := by
  unfold is_parsimonious
  decide +kernel

def ms_restriction_clause : cnf_clause (boolean_variable ms_part_csp middle_vertex_is_hidden) :=
  [value_literal ms_part_csp middle_vertex_is_hidden 0 ⟨0, by decide⟩ false,
    value_literal ms_part_csp middle_vertex_is_hidden 2 ⟨1, by decide⟩ false]

theorem ms_conjunction_one_model :
    model_count (minimal_support_encoding ms_part_csp middle_vertex_is_hidden [0, 1, 2] ++
      [ms_restriction_clause]) = 1 := by
  decide +kernel

end counterexamples

end parsimony
